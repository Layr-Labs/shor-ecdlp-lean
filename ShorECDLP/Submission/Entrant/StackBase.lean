import Mathlib.FieldTheory.Finite.Basic
import ShorECDLP.Submission.«2607_13816».Challenge.Lookup
import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
import ShorECDLP.Submission.«2607_13816».Challenge.BatchState
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.AccumulatorEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.Interval
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
import ShorECDLP.Submission.«2607_13816».Challenge.RegisterEquality
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Framework.Quantum.RelabelCongr
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedIdentity
import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».Window.Uniform
import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import ShorECDLP.Framework.Quantum.AdaptiveHadamard
import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.Reindex
import ShorECDLP.Challenge.Decoder
import ShorECDLP.Challenge.Resources
import ShorECDLP.Submission.«2607_13816».OrderFinding.WrappedCandidates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import ShorECDLP.Submission.Naive.OrderFinding.Proofs.SuccessProbability
import ShorECDLP.Submission.«2607_13816».Window.CharacterMixture
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part4
import ShorECDLP.Challenge.Template
import ShorECDLP.Math.EllipticCurve.GeneratorOrder
import ShorECDLP.Submission.Naive.Challenge.NumericCosts
import ShorECDLP.Submission.Naive.Challenge.RepeatedEntry
import ShorECDLP.Submission.Naive.EllipticCurve.ECDLPOracle
import ShorECDLP.Framework.Quantum.MeasurementUncompute
import ShorECDLP.Submission.Naive.EllipticCurve.PointEncoding
import ShorECDLP.Math.BitcoinPrimes
import ShorECDLP.Submission.Naive.Challenge.Certificate
import ShorECDLP.Submission.Naive.Challenge.RecordPositions
import ShorECDLP.Submission.Naive.Challenge.NumericLengths
import ShorECDLP.Submission.Naive.Challenge.StaticResources
import ShorECDLP.Submission.«2607_13816».Challenge.PointTable
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint

-- Assembly bundle: generic Streaming skeleton
section
/-! Body-parametric 29-addition Streaming producer and retained public compiler interfaces.
Bundled for bounded kernel-replay memory. Original Apache-2.0 provenance is retained. -/

-- ==== bundle: Streaming/Resources ====

section

/-! Adaptive zero guards, based on VerifiedQC/ShorECDLP, streaming-dev, PR #551,
Apache-2.0; see LICENSE and NOTICE. -/
set_option maxRecDepth 4096

namespace ShorECDLP.Entrant.ZeroAdaptive
open ShorECDLP Classical Quantum Paper2607_13816 Paper2607_13816.ChallengeMigration

def reg : List Wire := 263 :: List.range' 264 255
def scratch : List Wire := List.range' 7 254
def cx : Circuit := [.CX 837 263]

def prepare : AdaptiveCircuit := (computeEqConstAdaptive reg 0 837 scratch).seq (.unitary cx .done)
def restore : AdaptiveCircuit := (AdaptiveCircuit.unitary cx .done).seq (computeEqConstAdaptive reg 0 837 scratch)

def division : AdaptiveCircuit := (prepare.seq secp256k1InPlaceDivision).seq restore
def multiplication : AdaptiveCircuit := (prepare.seq secp256k1InPlaceMultiplication).seq restore

noncomputable section
/-- Five sequential field-word queries, each loaded and cleared around its modular addition. -/
def coordinateSource (x y : Nat → Nat) : AdaptiveCircuit :=
  ((((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    division).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    multiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))

open ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] divisionProgram multiplicationProgram equalityProgram
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication

def zDivisionProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let a := equalityProgram n start reg 0 837 scratch
  let b := divisionProgram n (start+a.1)
  appendCompiled a (prependCompiled cx (appendCompiled b
    (prependCompiled cx (equalityProgram n (start+a.1+b.1) reg 0 837 scratch))))

def zMultiplicationProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let a := equalityProgram n start reg 0 837 scratch
  let b := multiplicationProgram n (start+a.1)
  appendCompiled a (prependCompiled cx (appendCompiled b
    (prependCompiled cx (equalityProgram n (start+a.1+b.1) reg 0 837 scratch))))

def adaptiveCoordinateSegments : List (FixedSegment 32768) :=
  [fieldLookupAddProgram .negX (List.range' 263 256), signedFieldProgram .negY,
   zDivisionProgram 32768, pointSquareProgram 32768,
   fieldLookupAddProgram .tripleX (List.range' 263 256), zMultiplicationProgram 32768,
   xNegateProgram 32768, fieldLookupAddProgram .x (List.range' 263 256), signedFieldProgram .negY]

def adaptiveCoordinateProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 adaptiveCoordinateSegments start

def sharedAdaptiveCoordinateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (adaptiveCoordinateProgram start)

end
end ShorECDLP.Entrant.ZeroAdaptive
end

section

/-! Local conjugation proof for borrowing the enabled query root as a zero flag.
Scratch research file: not part of a candidate certificate until compiled. -/
namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def exchange : Wire ≃ Wire := Equiv.swap 836 837
def flip : Circuit := [.X 836]

def borrowed (program : AdaptiveCircuit) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary flip .done).seq (program.relabel exchange)).seq
    (.unitary flip .done)

noncomputable def division : AdaptiveCircuit := borrowed ZeroAdaptive.division
noncomputable def multiplication : AdaptiveCircuit := borrowed ZeroAdaptive.multiplication

end ShorECDLP.Entrant.BorrowFlag

/-! Append after GuardBorrow.lean (within its imports) for an incremental check.
This file is a source part, not an importable standalone module. -/
namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] ZeroAdaptive.prepare ZeroAdaptive.restore
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication

end ShorECDLP.Entrant.BorrowFlag


/-! Append after ProgramParts.lean for the borrowed coordinate source. -/
namespace ShorECDLP.Entrant.BorrowFlag
open ShorECDLP Classical Quantum Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
/-- Five sequential field-word queries, each loaded and cleared around its modular addition. -/
def coordinateSource (x y : Nat → Nat) : AdaptiveCircuit :=
  ((((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    division).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    multiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))

open ShorECDLP.Challenge ShorECDLP.Secp256k1

end
end ShorECDLP.Entrant.BorrowFlag
end

/-! Measured equality schedules: entrant improvement using protected measurement-uncomputation semantics. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
set_option linter.unusedSimpArgs false

/-- A flat compiler schedule for the library's measured clean v-chain. -/
def measuredTailOps {n : Nat} (a : Wire) :
    List Wire → Wire → List Wire → List (LookupOp n)
  | [], _, _ => []
  | [c], t, _ => [ordinaryOp [.CCX c a t]]
  | c :: d :: cs, t, w :: ws =>
      [ordinaryOp [.CCX c a w]] ++ measuredTailOps w (d :: cs) t ws ++ [.erase c a w]
  | _ :: _ :: _, _, [] => []

def measuredChainOps {n : Nat} : List Wire → Wire → List Wire → List (LookupOp n)
  | [], t, _ => [ordinaryOp [.X t]]
  | [c], t, _ => [ordinaryOp [.CX c t]]
  | a :: b :: cs, t, ws => measuredTailOps b (a :: cs) t ws

def measuredEqualityOps {n : Nat} (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    List (LookupOp n) :=
  [ordinaryOp (zeroMask r v)] ++ measuredChainOps r t ws ++ [ordinaryOp (zeroMask r v)]

end ShorECDLP.Paper2607_13816.ChallengeMigration

/-! EDITABLE. Single-trial entrant: in-place XOR correction model, circuit and semantics.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Streaming/IpxModel ====

section
/-! # In-place XOR correction: the word-level model

The streaming window addition writes `F(enc P)` into the 513-bit accumulator, where `F` is the
coordinate permutation of the affine formula for the window point `C`. It equals
`enc (P + C)` except on the four exceptional inputs `P_k ∈ [0, C, -C, -(C+C)]`.

This module replaces the five-word transposition network of the upstream certificate by an
in-place correction that keeps no endpoint word resident. With `a_k = W(F(enc P_k))` and
`b_k = W(enc (P_k + C))` (the eight endpoint words of the selected table row), it

1. computes four one-hot flags `f_k = [acc = a_k]` by XOR-ing the endpoint words into the
   accumulator and zero-testing it,
2. applies `acc ^= f_k · (a_k ^ b_k)` under each flag, and
3. clears every flag with `f_k ^= [acc = b_k]`.

Here the schedule is modelled on the accumulator word and the four flags. The circuit-level
semantics is in `IpxSemantics`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical ShorECDLP.Secp256k1 ShorECDLP.Challenge

/-- One step of the correction schedule: a table query XOR-ing endpoint word `u` (and `v`, if
present) into the accumulator, enabled by the window control or by flag `k`, or the zero test
of the accumulator into flag `k`. -/
inductive IpxOp where
  | query (control : Option (Fin 4)) (u : Fin 8) (v : Option (Fin 8))
  | test (k : Fin 4)

/-- Flags `f_k = [acc = a_k]`; afterwards the accumulator holds `acc ^ a_3`. -/
def ipxPhase1 : List IpxOp :=
  [.query none 0 none, .test 0, .query none 0 (some 1), .test 1,
   .query none 1 (some 2), .test 2, .query none 2 (some 3), .test 3]

/-- Flag-controlled updates `acc ^= f_k · (a_k ^ b_k)`. -/
def ipxPhase2 : List IpxOp :=
  [.query (some 0) 0 (some 4), .query (some 1) 1 (some 5),
   .query (some 2) 2 (some 6), .query (some 3) 3 (some 7)]

/-- Flag clearing `f_k ^= [acc = b_k]`; the final query restores the accumulator. -/
def ipxPhase3 : List IpxOp :=
  [.query none 3 (some 4), .test 0, .query none 4 (some 5), .test 1,
   .query none 5 (some 6), .test 2, .query none 6 (some 7), .test 3, .query none 7 none]

/-- Thirteen table queries and eight zero tests per correction block. -/
def ipxSchedule : List IpxOp := ipxPhase1 ++ ipxPhase2 ++ ipxPhase3

noncomputable section

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

end

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/IpxCircuit ====

section
/-! # In-place XOR correction: the circuit

Every wire of the correction block lies in the core streaming allocation:

* the accumulator ports `accumulatorPort` (263..518, 580..835, 838) are the data word;
* the one-hot flags are wires 0..3, the half-result of the split zero test is wire 4 and the
  v-chain scratch is 5..259; all of them are idle and clean between window additions
  (`Secp256k1ZeroAllowedInputValid`);
* table queries use the window's own 15-bit unary iteration (`batchWindowTree` on the address
  wires 839..853 with path wires 519..533), controlled by the window control 836 or by a flag.

A table query XORs one or two endpoint words of the selected row into the accumulator. A zero
test is three 257-bit `computeEqConst` calls: `h ^= [low = 0]`, `f ^= [(h :: high) = 1]`,
`h ^= [low = 0]`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

def ipxFlag (k : Fin 4) : Wire := k.val
def ipxHalf : Wire := 4
def ipxScratch : List Wire := List.range' 5 255
def ipxLow : List Wire := List.range' 263 256 ++ [580]
def ipxHigh : List Wire := List.range' 581 255 ++ [838]

def ipxControl : Option (Fin 4) → Wire
  | none => 836
  | some k => ipxFlag k

def ipxPorts {n : Nat} (row : Fin n) (j : Fin 8) : List (Wire × EndpointBit n) :=
  List.ofFn fun i : Fin 513 => (accumulatorPort i, exceptionalEndpointWords row j i)

def ipxPortsOpt {n : Nat} (row : Fin n) : Option (Fin 8) → List (Wire × EndpointBit n)
  | none => []
  | some j => ipxPorts row j

def ipxLeaf {n : Nat} (row : Fin n) (q : Wire) (u : Fin 8) (v : Option (Fin 8)) :
    List (TemplateGate n) :=
  endpointSelectGates q (ipxPorts row u) ++ endpointSelectGates q (ipxPortsOpt row v)

def ipxLeafCircuit {n : Nat} (read : ConstantBit n → Bool) (row : Fin n) (q : Wire)
    (u : Fin 8) (v : Option (Fin 8)) : Circuit :=
  tableXorGates q (endpointRawMask read (ipxPorts row u)) ++
    tableXorGates q (endpointRawMask read (ipxPortsOpt row v))

/-- Measured uncomputation reuses the same clean scratch wires. -/
def ipxMeasuredTestOps {n : Nat} (k : Fin 4) : List (LookupOp n) :=
  measuredEqualityOps ipxLow 0 ipxHalf ipxScratch ++
    measuredEqualityOps (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch ++
    measuredEqualityOps ipxLow 0 ipxHalf ipxScratch

noncomputable def ipxMeasuredTest (k : Fin 4) : AdaptiveCircuit :=
  ((computeEqConstAdaptive ipxLow 0 ipxHalf ipxScratch).seq
    (computeEqConstAdaptive (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch)).seq
    (computeEqConstAdaptive ipxLow 0 ipxHalf ipxScratch)

def ipxOps {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    List IpxOp → List (LookupOp n)
  | [] => []
  | .query c u v :: ops =>
    unaryLookupOps (fun l q => ipxLeaf (rows l) q u v) tree (ipxControl c) paths ++
      ipxOps rows tree paths ops
  | .test k :: ops => ipxMeasuredTestOps k ++ ipxOps rows tree paths ops

noncomputable def ipxSourceOps {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) : List IpxOp → AdaptiveCircuit
  | [] => .done
  | .query c u v :: ops =>
    (unaryAction .inc (fun l q => ipxLeafCircuit read (rows l) q u v) tree
      (ipxControl c) paths).seq (ipxSourceOps read rows tree paths ops)
  | .test k :: ops => (ipxMeasuredTest k).seq (ipxSourceOps read rows tree paths ops)

def ipxProgramOf {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (start : Nat) : (count : Nat) × Straight n start (start+count) :=
  ⟨lookupMeasurements (ipxOps rows tree paths ipxSchedule), lookupProgram n (ipxOps rows tree paths ipxSchedule) start⟩

/-- The compiled correction block of one window. -/
def ipxProgram (w : OddWindow) (start : Nat) : (count : Nat) × Straight 983040 start (start+count) :=
  ipxProgramOf (batchWindowRows w) batchWindowTree pointLookupPath start

noncomputable def ipxSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coefficientAt Q) (batchWindowRows w) batchWindowTree pointLookupPath
    ipxSchedule

/-! ## Layout facts -/

/-! ## Resources -/

/-! ## Well-formedness -/

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/IpxSemantics ====

section
/-! # In-place XOR correction: semantics

Every step of the correction block acts on the accumulator word `s ∘ accumulatorPort` and the
four flags exactly as `ipxModelStep` prescribes, keeps the path, scratch and half-result wires
clean and the window control set, and leaves every other wire unchanged. On every reachable
window state the model (`ipxModel_point`) then turns `F(enc P)` into `enc (P + C)` and clears
the flags, so the block writes `P + C` into the accumulator and restores every other wire. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

/-! ## Table queries -/

/-! ## Zero tests -/

/-! ## The schedule -/

/-! ## Coherence -/

/-! ## The window correction block -/

attribute [local irreducible] ipxSourceOps

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/IpxWindow ====

section
/-! # Windows and outer plan with the in-place XOR correction

Adapted from `ShorECDLP/Submission/2607_13816/Challenge/WindowBody.lean` (VerifiedQC/ShorECDLP,
branch `streaming-dev`, PR #551, Apache-2.0; see the repository LICENSE and NOTICE). The window
body is unchanged except that the five-word correction block `placedBatchProgram` is replaced by
`ipxProgram`, which lives entirely in the core allocation, so the round reset list is the core
`resetWires` (854 wires) instead of `batchedResetWires` (3931 wires). -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1 ShorECDLP.Entrant.ZeroAdaptive
attribute [local irreducible] sharedAdaptiveCoordinateProgram yNegateProgram ipxProgram

/-- Internal additions only; address preparation and Fourier are outside this list. -/
def ipxWindowSegments (w : OddWindow) : List (FixedSegment 983040) :=
  [sharedAdaptiveCoordinateProgram w, sharedYNegateProgram w, ipxProgram w, sharedYNegateProgram w]

noncomputable def ipxWindowSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [ShorECDLP.Entrant.ZeroAdaptive.coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
    (fun l => fieldValue (windowPoint Q w l) .y),windowYNegate,ipxSource Q w,windowYNegate]

def ipxWindowCore (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  sequenceProgram 983040 (ipxWindowSegments w) start

attribute [local irreducible] ipxWindowCore

def ipxWindowPrepared (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (ipxWindowCore w start)

/-- Address bank is relabeled to the reused 855–870 bank. -/
def actualIpxWindow (w : OddWindow) : OuterWindow 983040 :=
  closedWindow (relabelStraight (windowAddressPerm 855 (by decide)) (ipxWindowPrepared w 0).2)

def ipxLeftWindows : List (OuterWindow 983040) :=
  actualFirstWindow :: List.ofFn (fun k : Fin 15 => actualIpxWindow (.left ⟨14-k.val,by omega⟩))
def ipxRightWindows : List (OuterWindow 983040) :=
  List.ofFn (fun k : Fin 13 => actualIpxWindow (.right ⟨12-k.val,by omega⟩))

theorem ipxLeftWindows_length : ipxLeftWindows.length = 16 := by simp [ipxLeftWindows]
theorem ipxRightWindows_length : ipxRightWindows.length = 13 := by simp [ipxRightWindows]

/-- The round resets exactly the core allocation; the correction needs no extra wire. -/
def ipxOuterPlan : OuterPlan 983040 :=
  standardOuterPlan ⟨ipxLeftWindows.toArray,by simp [ipxLeftWindows_length]⟩
    ⟨ipxRightWindows.toArray,by simp [ipxRightWindows_length]⟩ resetWires

end ShorECDLP.Paper2607_13816.ChallengeMigration

end


open ShorECDLP.Entrant.ZeroAdaptive

/-! EDITABLE. Single-trial entrant: inherited resource and support lemmas.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Streaming/LookupSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/LookupSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every fixed gate slot counts, including disabled constant/record controls. -/
def lookupSlots {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + lookupSlots ops
  | .erase _ _ _ :: ops => 3 + lookupSlots ops

theorem recordGates_slots {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e) :
    (recordGates i gs next).gateSlots = gs.length + next.gateSlots := by
  induction gs <;> simp_all [recordGates,Straight.gateSlots,Nat.add_assoc,Nat.add_left_comm]

theorem lookupProgram_slots (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n ops start).gateSlots = lookupSlots ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [lookupProgram,Straight.gateSlots_append,gateProgram_slots,ih,lookupSlots]
    | erase a b t =>
      simp only [lookupProgram,castFinish_gateSlots,Straight.gateSlots_append,andEraseProgram,
        Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil,ih,lookupSlots]

theorem lookupSlots_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupSlots (xs++ys) = lookupSlots xs + lookupSlots ys := by
  induction xs with
  | nil => simp [lookupSlots]
  | cons x xs ih => cases x <;> simp_all [lookupSlots,Nat.add_assoc]

theorem unaryLookupOps_slots_le {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (bound : Nat) (hleaf : ∀ l q, (leaf l q).length ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    lookupSlots (unaryLookupOps leaf tree q anc) ≤
      bound * (tree.internalNodes+1) + 10*tree.internalNodes := by
  induction tree generalizing q anc with
  | leaf l => simpa [unaryLookupOps,lookupSlots,UnaryActionTree.internalNodes] using hleaf l q
  | node bit zero one ihz iho =>
    cases anc with
    | nil => simp [unaryLookupOps,lookupSlots]
    | cons path rest =>
      have hz := ihz path rest
      have ho := iho path rest
      simp only [unaryLookupOps,lookupSlots_append,lookupSlots,ordinaryOp,List.length_map,
        computeZeroAnd,List.length_cons,List.length_nil,UnaryActionTree.internalNodes,
        Nat.mul_add,Nat.mul_one] at *
      omega

theorem relabelStraight_slots {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    (relabelStraight e p).gateSlots = p.gateSlots := by
  induction p <;> simp_all only [relabelStraight,Straight.gateSlots]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ArithmeticSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ArithmeticSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] compareGEProgram gidneyProgram

attribute [local irreducible] uncontrolledCompareProgram

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

attribute [local irreducible] squareAddProgram squareSubProgram

attribute [local irreducible] squareProgram squareInverseProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/DecoderSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/DecoderSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACellSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACellSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEALengthSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEALengthSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAScheduleSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAScheduleSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ProductionEEASlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ProductionEEASlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] blockAForward blockAInverse blockCForward blockCInverse blockDForward blockDInverse blockFForward
  intervalTree coefficientPrefixTree quotientSwapTree remainderBlockProgram coefficientBlockProgram phaseProgram
  measuredStepProgram measuredEEAForwardProgram measuredScheduleProgram primitiveResources
  canonicalWork2Rotation canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear
  measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
  intervalProgram coefficientProgram measuredInverseStepProgram measuredEEAReverseProgram measuredInverseScheduleProgram


end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput

attribute [local irreducible] relabelCompiled measuredForwardDataBankProgram measuredReverseDataBankProgram
  divisionCleanupProgram divisionCorrectionProgram divisionAfterResetProgram divisionProgram
  multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationAfterResetProgram multiplicationProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] divisionProgram multiplicationProgram
attribute [local irreducible] zDivisionProgram zMultiplicationProgram modularNegateProgram squareSubtractProgram adaptiveCoordinateProgram

attribute [local irreducible] reindexCompiled sharedAdaptiveCoordinateProgram sharedYNegateProgram
  ipxProgram ipxWindowCore ipxWindowPrepared actualIpxWindow actualFirstWindow
  ipxLeftWindows ipxRightWindows ipxOuterPlan

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MeasurementBridge ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MeasurementBridge.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowCounts ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowCounts.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedAdaptiveCoordinateProgram yNegateProgram ipxProgram
  ipxWindowCore ipxWindowPrepared signedLookupCoordinateProgram primitiveResources
  sharedYNegateProgram actualIpxWindow ipxLeftWindows ipxRightWindows
  ipxSource windowYNegate sequenceCircuit ipxWindowSources

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/StructuralSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/StructuralSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every mentioned wire, including disabled constant-controlled gates. -/
def templateGateWires {n : Nat} : TemplateGate n → List Wire
  | .literal g => gateWires g
  | .whenBit _ _ g => gateWires g

/-- Syntactic support includes measurement targets and all record-controlled gates. -/
def straightWires {n s e : Nat} : Straight n s e → List Wire
  | .done => []
  | .gate g p => templateGateWires g ++ straightWires p
  | .recordGate _ _ g p => gateWires g ++ straightWires p
  | .measure w p => w :: straightWires p

private theorem subset_append {a b c d : List Wire} (h : a ⊆ c) (k : b ⊆ d) :
    a ++ b ⊆ c ++ d := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (h hx)
  · exact List.mem_append_right _ (k hx)

theorem templateGate_instantiate_support {n : Nat} (g : TemplateGate n)
    (read : ConstantBit n → Bool) : circuitWires (g.instantiate read) ⊆ templateGateWires g := by
  cases g <;> simp only [TemplateGate.instantiate,templateGateWires]
  · simp [circuitWires]
  · split <;> simp [circuitWires]

theorem straight_instantiate_support {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact subset_append (templateGate_instantiate_support g read) (ih history)
  | recordGate i v g p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.wires,straightWires]
    apply subset_append _ (ih history)
    split <;> simp [circuitWires]
  | measure w p ih =>
    intro x hx
    simp only [Straight.instantiate,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hx)
    · exact List.mem_cons_of_mem _ (ih _ hx)

theorem straightWires_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    straightWires (p.append q)=straightWires p ++ straightWires q := by
  induction p <;> simp_all only [Straight.append,straightWires,List.nil_append,List.append_assoc,List.cons_append]

theorem straightWires_castFinish {n s e f : Nat} (h : e=f) (p : Straight n s e) :
    straightWires (castFinish h p)=straightWires p := by subst f; rfl

theorem templateGateWires_reindex {n m : Nat} (f : Fin n → Fin m) (g : TemplateGate n) :
    templateGateWires (reindexGate f g)=templateGateWires g := by cases g <;> rfl

theorem straightWires_reindex {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    straightWires (reindexStraight f p)=straightWires p := by
  induction p <;> simp_all only [reindexStraight,straightWires,templateGateWires_reindex]

theorem gateProgram_support {n s : Nat} (gs : List (TemplateGate n)) :
    straightWires (gateProgram (cursor := s) gs)=gs.flatMap templateGateWires := by
  induction gs <;> simp_all only [gateProgram,straightWires,List.flatMap_nil,List.flatMap_cons]

theorem literalProgram_support (n start : Nat) (gs : Circuit) :
    straightWires (literalProgram (n := n) (s := start) gs)=circuitWires gs := by
  simp only [literalProgram,gateProgram_support,List.flatMap_map,templateGateWires,circuitWires]

theorem recordGates_support {n s e : Nat} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    straightWires (recordGates i gs p)=circuitWires gs ++ straightWires p := by
  induction gs <;> simp_all only [recordGates,straightWires,circuitWires,List.flatMap_nil,List.flatMap_cons,List.nil_append,List.append_assoc]

theorem templateGateWires_relabel {n : Nat} (e : Wire ≃ Wire) (g : TemplateGate n) :
    templateGateWires (relabelTemplateGate e g)=(templateGateWires g).map e := by
  cases g <;> rename_i g <;> cases g <;> rfl

theorem straightWires_relabel {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    straightWires (relabelStraight e p)=(straightWires p).map e := by
  have hg (g : Gate) : gateWires (g.relabel e)=(gateWires g).map e := by cases g <;> rfl
  induction p <;> simp_all only [relabelStraight,straightWires,templateGateWires_relabel,List.map_nil,List.map_append,List.map_cons]

def lookupOpWires {n : Nat} : LookupOp n → List Wire
  | .gates gs => gs.flatMap templateGateWires
  | .erase a b t => t :: circuitWires (controlledZ a b)

theorem lookupProgram_support (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n ops start)=ops.flatMap lookupOpWires := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [lookupProgram,straightWires_castFinish,straightWires_append,
      gateProgram_support,andEraseProgram,straightWires,recordGates_support,List.append_nil,
      List.flatMap_cons,lookupOpWires,ih]

theorem unaryLookupOps_support {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths support : List Wire)
    (hq : q ∈ support) (hp : paths ⊆ support) (hb : tree.indexWires ⊆ support)
    (hl : ∀ l c, c ∈ support → (leaf l c).flatMap templateGateWires ⊆ support) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, lookupOpWires op ⊆ support := by
  induction tree generalizing q paths with
  | leaf l => simpa only [unaryLookupOps,List.forall_mem_singleton,lookupOpWires] using hl l q hq
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hpath := hp List.mem_cons_self
      have hrest : rest ⊆ support := fun _ hx => hp (List.mem_cons_of_mem _ hx)
      have hbit : bit ∈ support := hb List.mem_cons_self
      have hz : zero.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have ho : one.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hz' := ihz path rest hpath hrest hz
      have ho' := iho path rest hpath hrest ho
      simp only [unaryLookupOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
      refine ⟨⟨⟨⟨⟨?_,fun _ => trivial⟩,hz'⟩,⟨?_,fun _ => trivial⟩⟩,ho'⟩,?_,?_,?_,?_,fun _ => trivial⟩
      all_goals simp [ordinaryOp,templateGateWires,lookupOpWires,computeZeroAnd,controlledZ,circuitWires,gateWires,hbit,hq,hpath]

theorem lookupLeafGates_support {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (support : List Wire) (hq : q ∈ support) (hp : ∀ p ∈ ports, p.2 ∈ support) :
    (lookupLeafGates q ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  simp only [lookupLeafGates,List.flatMap_map,List.mem_flatMap] at hw
  obtain ⟨p,hp',hw⟩ := hw
  simp only [templateGateWires,gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
  rcases hw with rfl | rfl
  · exact hq
  · exact hp p hp'

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] ipxProgramOf

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ArithmeticSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ArithmeticSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ControlSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ControlSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACoreSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACoreSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACenterSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACenterSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MultiplicationSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MultiplicationSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

attribute [local irreducible] squareAddProgram squareSubProgram

attribute [local irreducible] squareProgram squareInverseProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoefficientSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoefficientSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/PhaseSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/PhaseSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/IntervalSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/IntervalSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/LengthSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/LengthSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

attribute [local irreducible] zeroCellProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/StepSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/StepSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] intervalProgram rControlNonterminal coefficientProgram

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EndpointSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EndpointSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WrapperSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WrapperSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge













attribute [local irreducible] coefficientInverseProgram intervalInverseProgram phaseInverseProgram hInverseProgram
  blockAInverse blockCInverse blockDInverse blockFForward

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram

attribute [local irreducible] preprocessProgram unpreprocessProgram productionParityProgram
  measuredEEAForwardProgram measuredEEAReverseProgram
  eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation canonicalWork2InverseRotation
  terminalEpochCompression terminalWork1Clear

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] unmultiplyDataProgram multiplyDataProgram multiplyWorkProgram
  measuredForwardWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoordinateSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoordinateSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] fieldLookupAddProgram signedFieldProgram zDivisionProgram
  pointSquareProgram zMultiplicationProgram xNegateProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CompleteSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CompleteSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Static allocation includes the zero-divisor flag even though the reset list omits it. -/
def completeBatchedSupport : List Wire := 837 :: resetWires

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== bundle: Streaming/Semantics ====

open ShorECDLP.Entrant.ZeroAdaptive

/-! EDITABLE. Single-trial entrant: inherited coherent physical and Fourier lemmas.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Streaming/BatchBoundary ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchBoundary.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. The in-place XOR
correction keeps no resident endpoint workspace, so `batchWorkspace` is empty and the
five-word placement lemmas are gone. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

def batchWorkspace : List Wire := []
def BatchedPointReady (s : BasisState) : Prop := PointLookupValid s ∧ Clean batchWorkspace s

theorem batchWorkspace_outside (w : Wire) (hw : w ∈ batchWorkspace) : w ∉ pointLogicalWires := by
  simp [batchWorkspace] at hw

theorem pointWrite_batchedReady (P : Point) (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_valid P s hs.1.1,?_⟩,?_⟩
  · rw [pointWrite_frame P s 836 (by decide +kernel)]
    exact hs.1.2
  · intro w hw
    rw [pointWrite_frame P s w (batchWorkspace_outside w hw)]
    exact hs.2 w hw

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchedWindowState ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchedWindowState.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchedWindowCoherent ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchedWindowCoherent.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

theorem composeCoherent {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) P)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) R)
    (hf : ∀ s, P s → R (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) P := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket R (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

def BatchedWindowValid (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ P : Point, pointStateCoordinates s=fig14PointEncoding P

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/PreparedBatch ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/PreparedBatch.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualWindow ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualWindow.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowValidity ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowValidity.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

theorem batchedWindowValid_address_update (s : BasisState) (hs : BatchedWindowValid s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : BatchedWindowValid (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hcore (v : Wire) (hv : v < 839) : (s[w ↦ b]) v = s v := by
    simp only [upd]
    rw [if_neg (by dsimp only [Wire] at *; omega)]
  have hx : wireValues (List.range' 263 256) (s[w ↦ b]) = wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  have hy : wireValues (List.range' 580 256) (s[w ↦ b]) = wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  obtain ⟨⟨⟨hclean,hzero,hxbound,hybound⟩,hq⟩,-⟩ := hs.1
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro v hv
    rw [hcore v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)]
    exact hclean v hv
  · rw [hcore 837 (by decide)]; exact hzero
  · rw [hx]; exact hxbound
  · rw [hy]; exact hybound
  · rw [hcore 836 (by decide)]; exact hq
  · intro v hv
    simp [batchWorkspace] at hv
  · obtain ⟨P,hP⟩ := hs.2
    refine ⟨P,?_⟩
    simpa only [pointStateCoordinates,hcore 838 (by decide),hx,hy] using hP


end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/FirstValidity ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FirstValidity.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

private theorem zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]
private theorem zero_read (ws : List Wire) (s : BasisState)
    (hs : ∀ w ∈ ws, s w = false) :
    wireValues ws s = List.replicate ws.length false := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues,List.map_cons,List.length_cons,List.replicate_succ]
    rw [hs w (by simp)]
    exact congrArg (false :: ·) (ih (fun v hv => hs v (List.mem_cons_of_mem w hv)))

/-- Before direct loading, only the query flag and address register may be nonzero. -/
def FirstWindowInput (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ streamAddress → s v = false

theorem firstWindowInput_start : FirstWindowInput (zeroBasisState[836 ↦ true]) := by
  constructor
  · simp [upd]
  · intro v hv _
    simp [upd,hv,zeroBasisState]

theorem firstWindowInput_ready (s : BasisState) (hs : FirstWindowInput s) :
    BatchedPointReady s := by
  have hz (v : Wire) (hv : v < 836) : s v = false :=
    hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)
  have hx : wireValues (List.range' 263 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  have hy : wireValues (List.range' 580 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  refine ⟨⟨⟨?_,?_,?_,?_⟩,hs.1⟩,?_⟩
  · intro v hv
    exact hz v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  · exact hs.2 837 (by decide) (by simp [streamAddress])
  · rw [hx]; rw [zero_word]; norm_num [ShorECDLP.p]
  · rw [hy]; rw [zero_word]; norm_num [ShorECDLP.p]
  · intro v hv
    simp [batchWorkspace] at hv

theorem firstWindowInput_pointWrite (s : BasisState) (hs : FirstWindowInput s) (P : Point) :
    BatchedWindowValid (pointWrite P s) :=
  ⟨pointWrite_batchedReady P s (firstWindowInput_ready s hs),P,pointWrite_coordinates P s⟩



end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CrossWindowWeights ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CrossWindowWeights.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Input words use the opposite convention: the first window is most significant. -/
theorem fourierWordMSB_append (xs ys : List Bool) :
    fourierWordMSB (xs ++ ys) = fourierWordMSB xs * 2 ^ ys.length + fourierWordMSB ys := by
  induction xs with
  | nil => simp [fourierWordMSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordMSB, List.length_append, ih, pow_add]
    ring

-- Both sides of the signed-address boundary, including both extreme addresses.
example : [0, 32767, 32768, 65535].map (signedTableOdd 32768) =
    [-65535, -1, 1, 65535] := by decide +kernel

-- Two radix-65536 input windows. The fixed offset cancels both centered digits.
example : ([0, 32767, 32768, 65535] : List Nat).all (fun a =>
    [0, 32767, 32768, 65535].all (fun b =>
      65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 +
        signedTableOdd 32768 b == 2 * ((a : Int) * 65536 + b))) = true := by
  decide +kernel

example : fourierWordLSB (List.replicate 16 false ++ true :: List.replicate 15 false) =
    65536 := by decide +kernel

/-- Splitting a Fourier word at a window boundary retains all feedback phases. -/
theorem fourierBitAmplitude_append (dir : PhaseDir) (xs ys prior bs cs : List Bool)
    (hl : bs.length = xs.length) :
    fourierBitAmplitude dir (xs ++ ys) prior (bs ++ cs) =
      fourierBitAmplitude dir xs prior bs *
        fourierBitAmplitude dir ys (bs.reverse ++ prior) cs := by
  induction xs generalizing prior bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hl
    subst bs
    simp [fourierBitAmplitude]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, fourierBitAmplitude]
      rw [ih (b :: prior) bs (by simpa using hl)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      ring

/-- Product of the individual window amplitudes, with the actual newest-first
history carried from one window to the next. -/
noncomputable def windowFourierAmplitude (dir : PhaseDir) :
    List (List Bool × List Bool) → List Bool → ℂ
  | [], _ => 1
  | (input, output) :: windows, prior =>
      fourierBitAmplitude dir input prior output *
        windowFourierAmplitude dir windows (output.reverse ++ prior)

theorem windowFourierAmplitude_flatten (dir : PhaseDir)
    (windows : List (List Bool × List Bool)) (prior : List Bool)
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows prior =
      fourierBitAmplitude dir (windows.map Prod.fst).flatten prior
        (windows.map Prod.snd).flatten := by
  induction windows generalizing prior with
  | nil => simp [windowFourierAmplitude, fourierBitAmplitude]
  | cons w windows ih =>
    simp only [windowFourierAmplitude, List.map_cons, List.flatten_cons]
    rw [fourierBitAmplitude_append dir _ _ _ _ _ (hl w (by simp)),
      ih _ (fun v hv => hl v (List.mem_cons_of_mem w hv))]

/-- The entire axis has one Fourier kernel; window feedback introduces no
extra phase when the axis starts with empty history. -/
theorem windowFourierAmplitude_kernel (dir : PhaseDir)
    (windows : List (List Bool × List Bool))
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows List.nil =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ (windows.map Prod.fst).flatten.length) *
        dyadicFourierKernel dir (windows.map Prod.fst).flatten.length
          (fourierWordMSB (windows.map Prod.fst).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have he : (windows.map Prod.snd).flatten.length =
      (windows.map Prod.fst).flatten.length := by
    induction windows with
    | nil => rfl
    | cons w windows ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [hl w (by simp), ih (fun v hv => hl v (List.mem_cons_of_mem w hv))]
  rw [windowFourierAmplitude_flatten dir windows List.nil hl,
    fourierBitAmplitude_eq dir _ List.nil _ he]
  simp [fourierHistoryPhase, fourierHistoryAngle]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CrossWindowPoint ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CrossWindowPoint.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem literalProgram_wellFormed {n s : Nat} (gs : Circuit) (h : CircuitWellFormed gs) :
    (literalProgram (n:=n) (s:=s) gs).WellFormed := by
  apply gateProgram_wellFormed
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  exact h v hv

theorem reindexStraight_wellFormed {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    (reindexStraight f p).WellFormed ↔ p.WellFormed := by
  have hg (g : TemplateGate n) : (reindexGate f g).WellFormed ↔ g.WellFormed := by
    cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih => simp only [reindexStraight,Straight.WellFormed,hg,ih]
  | recordGate i v g p ih => simp only [reindexStraight,Straight.WellFormed,ih]
  | measure w p ih => exact ih

attribute [local irreducible] modularNegateProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ModularPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ModularPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] uncontrolledCompareProgram gidneyProgram

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACenterPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACenterPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] gidneyProgram uncontrolledCompareProgram

attribute [local irreducible] constMinusProgram

attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram
  eeaCenter eeaUncenter eeaLengthSetup eeaLengthUndo workRegistersPrepare workRegistersRestore

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAStructuralPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAStructuralPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] vchainProgram

attribute [local irreducible] rippleFirstProgram rippleSecondProgram

attribute [local irreducible] coefficientFirstProgram coefficientSecondProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAIntervalPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAIntervalPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume validity of the source gates;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

attribute [local irreducible] intervalTopFirstProgram intervalTopSecondProgram traversalFirstProgram traversalSecondProgram

attribute [local irreducible] intervalProgram intervalInverseProgram coefficientProgram coefficientInverseProgram
  phaseProgram phaseInverseProgram intervalAddSub intervalAddSubInverse coefficientPrefixAdaptive coefficientPrefixInverseAdaptive
  phaseUpdateEpochAdaptive phaseUpdateEpochInverseAdaptive

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram blockBAdaptive blockEAdaptive

attribute [local irreducible] indexedStepProgram indexedInverseStepProgram indexedStepAdaptive indexedStepInverseAdaptive

attribute [local irreducible] scheduleProgram inverseScheduleProgram indexedScheduleAdaptive indexedScheduleInverseAdaptive

attribute [local irreducible] eeaForwardProgram eeaReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MeasuredEEAPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MeasuredEEAPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume validity of the source gates;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram measuredIndexedStep measuredIndexedStepInverse

attribute [local irreducible] measuredScheduleProgram measuredInverseScheduleProgram measuredIndexedSchedule measuredIndexedScheduleInverse

attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/SquarePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/SquarePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

attribute [local irreducible] squareAddProgram squareSubProgram

attribute [local irreducible] squareProgram squareInverseProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlacePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlacePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

attribute [local irreducible] hornerProgram hornerInverseProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceCompletePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceCompletePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram
  measuredForwardWrapperProgram measuredReverseWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

attribute [local irreducible] divisionCleanupProgram multiplicationCleanupProgram

attribute [local irreducible] divisionAfterResetProgram multiplicationAfterResetProgram collectProgram

attribute [local irreducible] divisionProgram multiplicationProgram equalityProgram

attribute [local irreducible] squareSubtractProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoordinatePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoordinatePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

attribute [local irreducible] fieldLoadProgram modularAddProgram appendCompiled

attribute [local irreducible] fieldLookupAddProgram yNegateProgram

attribute [local irreducible] zDivisionProgram zMultiplicationProgram pointSquareProgram signedFieldProgram xNegateProgram

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Physical validity of the actual first and signed windows and their outer composition. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] adaptiveCoordinateProgram

attribute [local irreducible] sharedAdaptiveCoordinateProgram sharedYNegateProgram ipxProgram

attribute [local irreducible] ipxWindowCore

attribute [local irreducible] ipxWindowPrepared

attribute [local irreducible] firstLookupProgram

attribute [local irreducible] actualIpxWindow actualFirstWindow

attribute [local irreducible] ipxOuterPlan

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/HistoryExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/HistoryExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/OuterExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/OuterExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

attribute [local irreducible] fourierProgram prepareOuterBank

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

attribute [local irreducible] ipxLeftWindows ipxRightWindows

attribute [local irreducible] ipxOuterPlan

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/TaggedProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TaggedProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] fourierOutcomes streamAddress

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/AxisProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/AxisProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/TwoAxisProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TwoAxisProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/FixedWord ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FixedWord.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The evaluator reads exactly the supplied chronological bits, with its fixed LSB convention. -/
theorem readWord_of_actual_bits (history : List Bool) (positions : List Nat) (bits : List Bool)
    (h : positions.map (fun i => history[i]?) = bits.map some) :
    readWord history positions = some (fourierWordLSB bits) := by
  induction positions generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bits => simp at h
  | cons i positions ih =>
    cases bits with
    | nil => simp at h
    | cons b bits =>
      have hh : history[i]? = some b ∧
          positions.map (fun j => history[j]?) = bits.map some := by
        simpa only [List.map_cons,List.cons.injEq] using h
      simp only [readWord,hh.1,ih bits hh.2,fourierWordLSB]
      cases b <;> rfl

theorem actual_bits_range (before bits after : List Bool) :
    (List.range' before.length bits.length).map
      (fun i => (before ++ bits ++ after)[i]?) = bits.map some := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range'] at hi
    simp only [List.getElem_map,List.getElem_range']
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.one_mul]
    rw [List.getElem?_append_left hi,List.getElem?_eq_getElem hi]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowBranchSum ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowBranchSum.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. The per-round lower
bound `wrappedIdeal_mass_lower` is now the averaged bound `27/50` of `AveragedSuccess` instead of
the protected pointwise bound `163/1000`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes

/-- Physical Fourier coefficients retain the full previous measurement history. -/
theorem branchCoeff_amplitude (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih hws.tail]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem window_branch_uniform (dir : PhaseDir) (ws : List Wire) (hn : ws.Nodup)
    (f : BasisState → BasisState) (prior output : List Bool)
    (s : BasisState) (hz : Clean ws s)
    (hf : ∀ input ∈ fourierOutcomes ws.length,
      ws.map (f (phaseWordState ws input s)) = input) :
    fourierBranch dir ws.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ f (Quantum.run (ws.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ws.length) •
        ((fourierOutcomes ws.length).map (fun input =>
          fourierBitAmplitude dir input.reverse prior output •
            ket (fourierClear ws.reverse (f (phaseWordState ws input s))))).sum := by
  classical
  rw [phaseHadamards_uniform ws hn s hz, map_smul, map_smul]
  congr 1
  simp only [phaseUniformSum, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [show Finsupp.lmapDomain ℂ ℂ f (ket (phaseWordState ws input s)) =
      ket (f (phaseWordState ws input s)) by simp [ket],
    fourierBranch_ket, branchCoeff_amplitude dir ws.reverse (List.nodup_reverse.mpr hn)]
  rw [List.map_reverse, hf input hi]

theorem phaseWordState_preserves (V : BasisState → Prop) (ws : List Wire)
    (hV : ∀ s, V s → ∀ w ∈ ws, ∀ b, V (s[w ↦ b]))
    (input : List Bool) (s : BasisState) (hs : V s) :
    V (phaseWordState ws input s) := by
  induction ws generalizing s input with
  | nil => exact hs
  | cons w ws ih =>
    cases input with
    | nil => exact hs
    | cons b input =>
      exact ih (fun t ht v hv c => hV t ht v (List.mem_cons_of_mem w hv) c)
        input _ (hV s hs w (by simp) b)

theorem clear_assigned_point (ws : List Wire) (input : List Bool) (s : BasisState)
    (hz : Clean ws s) (hd : ∀ v ∈ ws, v ∉ pointLogicalWires) (P : Point) :
    fourierClear ws.reverse (pointWrite P (phaseWordState ws input s)) = pointWrite P s := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ ws
  · have hp := hd v hv
    simp only [List.mem_reverse, hv, if_true, pointWrite, if_neg hp]
    exact (hz v hv).symm
  · simp only [List.mem_reverse, hv, if_false, pointWrite]
    split
    · rfl
    · exact phaseWordState_frame ws input s v hv

theorem assigned_window_digit (input : List Bool) (hi : input.length = streamAddress.length)
    (s : BasisState) :
    windowRawDigit 0 (phaseWordState streamAddress input s) = boolWordToNat input := by
  have ha (t : BasisState) : tableAddressValue streamAddress t = windowRawDigit 0 t := by
    simp [streamAddress, tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  rw [← ha]
  have word := phaseWordState_word streamAddress (by decide +kernel) input hi s
  change boolWordToNat (wireValues streamAddress (phaseWordState streamAddress input s)) = _
  rw [word]


theorem phaseWordState_pointWrite (ws : List Wire) (hd : ∀ w ∈ ws, w ∉ pointLogicalWires)
    (input : List Bool) (P : Point) (s : BasisState) :
    phaseWordState ws input (pointWrite P s) = pointWrite P (phaseWordState ws input s) := by
  induction ws generalizing input s with
  | nil => rfl
  | cons w ws ih =>
    cases input with
    | nil => rfl
    | cons b input =>
      have he : (pointWrite P s)[w ↦ b] = pointWrite P (s[w ↦ b]) := by
        funext v
        have hw := hd w (by simp)
        by_cases hv : v = w
        · subst v; simp [pointWrite, hw, upd]
        · by_cases hp : v ∈ pointLogicalWires <;> simp [pointWrite, hp, upd, hv]
      simp only [phaseWordState, he]
      exact ih (fun v hv => hd v (List.mem_cons_of_mem w hv)) input _

end
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== bundle: Single/Physical ====

set_option linter.unusedSectionVars false

open ShorECDLP.Entrant.ZeroAdaptive

/-! Deterministic classical rounding encoded as ordinary recorded gates.
All gates are Clifford gates on two previously reset wires. -/
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- One full-adder step: record the next carry, then the sum bit.
Input and carry controls refer only to existing measurement records. -/
def addStep {n start : Nat} (carry bit : Fin start) : Straight n start (start + 2) :=
  .recordGate carry true (.X 0)
    (.recordGate bit true (.CX 0 1)
      (.gate (.literal (.H 1))
        (.measure 1
          (.recordGate carry.castSucc true (.X 0)
            (.recordGate bit.castSucc true (.X 1)
              (.recordGate carry.castSucc true (.X 1)
                (.gate (.literal (.H 1)) (.measure 1 .done))))))))

def liftTwo {start : Nat} (i : Fin start) : Fin (start + 2) :=
  ⟨i.val, by omega⟩

/-- Carry begins with the highest discarded Fourier bit. -/
def addWord {n : Nat} : (start : Nat) → Fin start → (bits : List (Fin start)) →
    Straight n start (start + 2 * bits.length)
  | start, carry, [] => .done
  | start, carry, bit :: bits => castFinish (by simp; omega)
      ((addStep carry bit).append
        (addWord (start + 2) ⟨start, by omega⟩ (bits.map liftTwo)))
termination_by _ _ bits => bits.length

def carryBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits => (carry && bit) :: (bit ^^ carry) :: carryBits (carry && bit) bits

def sumBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits => (bit ^^ carry) :: sumBits (carry && bit) bits

theorem addStep_wellFormed {n start : Nat} (carry bit : Fin start) :
    (addStep (n := n) carry bit).WellFormed := by
  simp [addStep, Straight.WellFormed, TemplateGate.WellFormed, Gate.WellFormed]

theorem addStep_slots {n start : Nat} (carry bit : Fin start) :
    (addStep (n := n) carry bit).gateSlots = 7 := rfl

theorem addWord_wellFormed {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    (addWord (n := n) start carry bits).WellFormed
  | _, _, [] => by simp [addWord, Straight.WellFormed]
  | start, carry, bit :: bits => by
      rw [addWord, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (addStep_wellFormed _ _)
        (addWord_wellFormed (start + 2) _ _)
termination_by _ _ bits => bits.length

theorem addWord_slots {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    (addWord (n := n) start carry bits).gateSlots = 7 * bits.length
  | _, _, [] => by simp [addWord, Straight.gateSlots]
  | start, carry, bit :: bits => by
      rw [addWord, castFinish_gateSlots, Straight.gateSlots_append, addStep_slots,
        addWord_slots (start + 2)]
      simp
      omega
termination_by _ _ bits => bits.length

noncomputable section

/-- An H before the protected X reset records the computational-basis bit. -/
theorem zRecord_ket (w : Wire) (outcome : Bool) (s : BasisState) :
    xResetKraus w outcome (applyGate (.H w) (ket s)) =
      if outcome = s w then ket (s[w ↦ false]) else 0 := by
  have hh := applyGate_adjoint_applyGate (.H w) (by trivial) (ket s)
  change applyGate (.H w) (applyGate (.H w) (ket s)) = ket s at hh
  rw [xResetKraus, LinearMap.comp_apply, LinearMap.comp_apply, hh, projectZ_ket]
  by_cases he : outcome = s w
  · rw [if_pos he.symm, if_pos he]
    cases outcome with
    | false =>
      simp only [resetCircuit, Bool.false_eq_true, ↓reduceIte, Quantum.run, LinearMap.id_apply]
      congr 1
      funext i
      by_cases hi : i = w
      · subst i; simp [he.symm]
      · simp [upd, hi]
    | true => simp [resetCircuit, Quantum.run, onKet, he.symm]
  · rw [if_neg (Ne.symm he), if_neg he, map_zero]


theorem run_done_data : AdaptiveCircuit.done.run = [⟨[], LinearMap.id⟩] := rfl

theorem update_twice (s : BasisState) (w : Wire) (a b : Bool) :
    s[w ↦ a][w ↦ b] = s[w ↦ b] := by
  funext i
  by_cases h : i = w <;> simp [upd, h]

theorem updates_commute01 (s : BasisState) (a b : Bool) :
    s[0 ↦ a][1 ↦ b] = s[1 ↦ b][0 ↦ a] := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [upd, h0, h1]

def andMap (carry bit out : Bool) : State →ₗ[ℂ] State :=
  (xResetKraus 1 out).comp ((applyGate (.H 1)).comp
    ((Quantum.run (if bit then [.CX 0 1] else [])).comp
      (Quantum.run (if carry then [.X 0] else []))))

def sumMap (carry bit out : Bool) : State →ₗ[ℂ] State :=
  (xResetKraus 1 out).comp ((applyGate (.H 1)).comp
    ((Quantum.run (if carry then [.X 1] else [])).comp
      ((Quantum.run (if bit then [.X 1] else [])).comp
        (Quantum.run (if carry then [.X 0] else [])))))

theorem run_singleton_map (g : Gate) : Quantum.run [g] = applyGate g := by
  ext ψ; rfl

attribute [local irreducible] xResetKraus applyGate Quantum.run

@[irreducible] def stepTail (carry bit : Bool) : AdaptiveCircuit :=
  .unitary (if carry then [.X 0] else [])
    (.unitary (if bit then [.X 1] else [])
      (.unitary (if carry then [.X 1] else [])
        (.unitary [.H 1] (.xMeasureReset 1 .done .done))))

@[irreducible] def stepSource (carry bit : Bool) : AdaptiveCircuit :=
  .unitary (if carry then [.X 0] else [])
    (.unitary (if bit then [.CX 0 1] else [])
      (.unitary [.H 1] (.xMeasureReset 1 (stepTail carry bit) (stepTail carry bit))))

theorem addStep_instantiate {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (addStep carry bit).instantiate read history = stepSource (history carry) (history bit) := by
  simp only [addStep, Straight.instantiate, Fin.lastCases_castSucc, TemplateGate.instantiate,
    stepSource, stepTail]

theorem two_record_run (w : Wire) (A B C D E F H : Circuit) :
    (AdaptiveCircuit.unitary A (.unitary B (.unitary C (.xMeasureReset w
      (.unitary D (.unitary E (.unitary F (.unitary H (.xMeasureReset w .done .done)))))
      (.unitary D (.unitary E (.unitary F (.unitary H (.xMeasureReset w .done .done))))))))).run =
    let first (x : Bool) := (xResetKraus w x).comp ((Quantum.run C).comp ((Quantum.run B).comp (Quantum.run A)))
    let last (y : Bool) := (xResetKraus w y).comp ((Quantum.run H).comp ((Quantum.run F).comp
      ((Quantum.run E).comp (Quantum.run D))))
    show Instrument from [⟨[false,false], (last false).comp (first false)⟩,
     ⟨[false,true], (last true).comp (first false)⟩,
     ⟨[true,false], (last false).comp (first true)⟩,
     ⟨[true,true], (last true).comp (first true)⟩] := by
  rfl

theorem stepSource_run (carry bit : Bool) :
    (stepSource carry bit).run =
      [⟨[false,false], (sumMap carry bit false).comp
        (andMap carry bit false)⟩,
       ⟨[false,true], (sumMap carry bit true).comp
        (andMap carry bit false)⟩,
       ⟨[true,false], (sumMap carry bit false).comp
        (andMap carry bit true)⟩,
       ⟨[true,true], (sumMap carry bit true).comp
        (andMap carry bit true)⟩] := by
  have h := two_record_run 1 (if carry then [.X 0] else [])
    (if bit then [.CX 0 1] else []) ([.H 1])
    (if carry then [.X 0] else []) (if bit then [.X 1] else [])
    (if carry then [.X 1] else []) ([.H 1])
  simpa only [stepSource, stepTail, andMap, sumMap, run_singleton_map] using h


theorem addStep_run {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((addStep carry bit).instantiate read history).run =
      [⟨[false,false], (sumMap (history carry) (history bit) false).comp
        (andMap (history carry) (history bit) false)⟩,
       ⟨[false,true], (sumMap (history carry) (history bit) true).comp
        (andMap (history carry) (history bit) false)⟩,
       ⟨[true,false], (sumMap (history carry) (history bit) false).comp
        (andMap (history carry) (history bit) true)⟩,
       ⟨[true,true], (sumMap (history carry) (history bit) true).comp
        (andMap (history carry) (history bit) true)⟩] := by
  rw [addStep_instantiate, stepSource_run]


theorem andMap_ket (carry bit out : Bool) (s : BasisState)
    (hs0 : s 0 = false) (hs1 : s 1 = false) :
    andMap carry bit out (ket s) =
      if out = (carry && bit) then ket (s[0 ↦ carry]) else 0 := by
  have h0 : s[0 ↦ false] = s := by funext i; by_cases h : i = 0 <;> simp [upd, h, hs0]
  have h1 : s[1 ↦ false] = s := by funext i; by_cases h : i = 1 <;> simp [upd, h, hs1]
  cases carry <;> cases bit <;> cases out <;>
    simp only [andMap, LinearMap.comp_apply, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, run_nil, run_singleton, applyGate_X_ket, applyGate_CX_ket,
      zRecord_ket, hs0, hs1, h0, h1, upd_same, update_twice, updates_commute01,
      Bool.false_and, Bool.true_and, Bool.xor_false,
      Bool.xor_true, Bool.not_false,
      upd_other _ _ _ (by decide : (1 : Nat) ≠ 0)]

theorem sumMap_ket (carry bit out : Bool) (s : BasisState)
    (hs0 : s 0 = false) (hs1 : s 1 = false) :
    sumMap carry bit out (ket (s[0 ↦ carry])) =
      if out = (bit ^^ carry) then ket s else 0 := by
  have h0 : s[0 ↦ false] = s := by funext i; by_cases h : i = 0 <;> simp [upd, h, hs0]
  have h1 : s[1 ↦ false] = s := by funext i; by_cases h : i = 1 <;> simp [upd, h, hs1]
  cases carry <;> cases bit <;> cases out <;>
    simp only [sumMap, LinearMap.comp_apply, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, run_nil, run_singleton, applyGate_X_ket, zRecord_ket,
      hs1, h0, h1, upd_same, update_twice, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true]


def CleanReadout (s : BasisState) : Prop := s 0 = false ∧ s 1 = false

theorem stepMap_state (carry bit x y : Bool) (ψ : State) (hψ : SupportedOn CleanReadout ψ) :
    sumMap carry bit y (andMap carry bit x ψ) =
      if x = (carry && bit) ∧ y = (bit ^^ carry) then ψ else 0 := by
  let L := (sumMap carry bit y).comp (andMap carry bit x)
  let c : ℂ := if x = (carry && bit) ∧ y = (bit ^^ carry) then 1 else 0
  have h : BranchCoherentOn LinearMap.id CleanReadout (⟨[], L⟩ : InstrumentBranch) c := by
    intro s hs
    change sumMap carry bit y (andMap carry bit x (ket s)) = c • ket s
    rw [andMap_ket _ _ _ s hs.1 hs.2]
    by_cases hx : x = (carry && bit)
    · rw [if_pos hx, sumMap_ket _ _ _ s hs.1 hs.2]
      simp only [c, hx, true_and]
      split_ifs <;> simp
    · rw [if_neg hx, map_zero]
      simp [c, hx]
  have hs := h.on_supported hψ
  change sumMap carry bit y (andMap carry bit x ψ) = c • ψ at hs
  rw [hs]
  dsimp only [c]
  split_ifs <;> simp

theorem addStep_branch {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((addStep carry bit).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    b.kraus ψ = ψ ∧ b.history = [history carry && history bit, history bit ^^ history carry] := by
  rw [addStep_run] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  all_goals
    simp only [LinearMap.comp_apply, stepMap_state _ _ _ _ ψ hψ] at hn ⊢
    split_ifs at hn with h
    · simp only [if_pos h]
      exact ⟨True.intro, by rw [← h.1, ← h.2]⟩
    · exact (hn rfl).elim


theorem addWord_branch {n : Nat} : ∀ (start : Nat) (carry : Fin start)
    (bits : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (_hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch),
    b ∈ ((addWord start carry bits).instantiate read history).run → b.kraus ψ ≠ 0 →
    b.kraus ψ = ψ ∧ b.history = carryBits (history carry) (bits.map history)
  | _, _, [], _, _, _, _, b, hb, _ => by
      simp only [addWord, Straight.instantiate, run_done_data, List.mem_singleton] at hb
      subst b
      simp [carryBits]
  | start, carry, bit :: bits, read, history, ψ, hψ, b, hb, hn => by
      rw [addWord, castFinish_instantiate] at hb
      obtain ⟨mid, a, c, ha, hc, he, rfl⟩ := straight_append_branch _ _ read history b hb
      have han : a.kraus ψ ≠ 0 := by
        intro h
        apply hn
        simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
      obtain ⟨hastate, hahist⟩ := addStep_branch carry bit read history ψ hψ a ha han
      have hcn : c.kraus ψ ≠ 0 := by
        simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hastate] using hn
      have hi := addWord_branch (start + 2) ⟨start, by omega⟩ (bits.map liftTwo)
        read mid ψ hψ c hc hcn
      have hold (i : Fin start) : mid (liftTwo i) = history i := by
        have h := congrArg (fun xs : List Bool => xs[i.val]?) he
        dsimp only at h
        have hlt : i.val < start + 2 := by omega
        rw [List.getElem?_append_left (by simp)] at h
        simpa only [List.getElem?_ofFn, i.isLt, hlt, ↓reduceDIte,
          Option.some.injEq, liftTwo] using h
      have hcarry : mid ⟨start, by omega⟩ = (history carry && history bit) := by
        rw [hahist] at he
        have h := congrArg (fun xs : List Bool => xs[start]?) he
        dsimp only at h
        have hlt : start < start + 2 := by omega
        rw [List.getElem?_append_right (by simp)] at h
        simpa only [List.getElem?_ofFn, hlt, ↓reduceDIte, List.length_ofFn, Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] using h
      have hbits : (bits.map liftTwo).map mid = bits.map history := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hold i
      constructor
      · simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hastate] using hi.1
      · simp only [InstrumentBranch.seq, hahist, hi.2, hcarry, hbits,
          List.map_cons, carryBits, List.cons_append, List.nil_append]
termination_by _ _ bits => bits.length

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816

theorem sumBits_eq_increment (carry : Bool) (bits : List Bool) :
    sumBits carry bits = incrementBits carry bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp only [sumBits, incrementBits, ih, Bool.and_comm]

theorem sumBits_length (carry : Bool) (bits : List Bool) :
    (sumBits carry bits).length = bits.length := by
  rw [sumBits_eq_increment, incrementBits_length]

theorem sumBits_value (carry : Bool) (bits : List Bool) :
    boolWordToNat (sumBits carry bits) = (carry.toNat + boolWordToNat bits) % 2^bits.length := by
  rw [sumBits_eq_increment, boolWordToNat_incrementBits]

theorem carryBits_odd (carry : Bool) (bits : List Bool) (i : Nat) :
    (carryBits carry bits)[2*i+1]? = (sumBits carry bits)[i]? := by
  induction bits generalizing carry i with
  | nil => simp [carryBits, sumBits]
  | cons bit bits ih =>
    cases i with
    | zero => simp [carryBits, sumBits]
    | succ i =>
      simp only [carryBits, sumBits]
      rw [show 2*(i+1)+1 = (2*i+1)+2 by omega]
      simpa only [List.getElem?_cons_succ, Nat.add_assoc] using ih (carry && bit) i

end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816.ChallengeMigration

theorem addStep_support {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((addStep carry bit).instantiate read history).wires ⊆ [0, 1] := by
  cases hc : history carry <;> cases hb : history bit <;>
    simp [addStep, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires,
      circuitWires, gateWires, hc, hb, List.subset_def]

theorem addWord_support {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool),
    ((addWord start carry bits).instantiate read history).wires ⊆ [0, 1]
  | _, _, [], _, _ => by simp [addWord, Straight.instantiate, AdaptiveCircuit.wires]
  | start, carry, bit :: bits, read, history => by
      rw [addWord, castFinish_instantiate]
      exact outer_append_support _ _ read history ([0, 1]) (addStep_support _ _ _ _)
        (fun h => addWord_support (start + 2) _ _ read h)
termination_by _ _ bits => bits.length
end ShorECDLP.Entrant.RoundedReadout


section
/-! Source part after CoordinateParts; requires Entrant Streaming Resources/Semantics imports. -/
namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] Paper2607_13816.ChallengeMigration.divisionProgram
  Paper2607_13816.ChallengeMigration.multiplicationProgram equalityProgram

attribute [local irreducible]
  fieldLookupAddProgram yNegateProgram pointSquareProgram signedFieldProgram xNegateProgram

end ShorECDLP.Entrant.BorrowFlag

namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.BorrowFlag

end

/-! EDITABLE. Single-trial entrant: mixed-width circuit and resource proofs.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Coordinate ====

section
/-! Table-parametric instantiations of the Apache-2.0 licensed Streaming
compilation lemmas. Arithmetic circuits and their coherent proofs are reused.
Only the public coefficient read function is generalized here. -/

namespace ShorECDLP.Entrant.Single.Physical
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] fieldLoadProgram modularAddProgram divisionProgram multiplicationProgram
  squareSubtractProgram modularNegateProgram secp256k1InPlaceDivision secp256k1InPlaceMultiplication

noncomputable def tablePoint (coeffs : Fin 32768 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a % 32768, Nat.mod_lt _ (by decide)⟩)

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Batch ====

section
/-! Table-parametric in-place exceptional correction. The correction and
its semantic proof adapt the Streaming construction (VerifiedQC PR #551,
Apache-2.0) to the mixed-width coefficient table. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def tableRows (label : Nat) : Fin 32768 := ⟨label % 32768, Nat.mod_lt _ (by decide)⟩

noncomputable def placedBatchSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coeffs Q) tableRows batchWindowTree pointLookupPath ipxSchedule

attribute [local irreducible] ipxSourceOps

theorem tablePoint_order (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0) (a : Nat) :
    order • tablePoint coeffs Q a = 0 := by
  unfold tablePoint constantPoint
  rw [nsmul_add, smul_comm order, smul_comm order, generator_nsmul_eq_zero, hQ, nsmul_zero, nsmul_zero, add_zero]

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/State ====

section
/-! Table-parametric boundary composition adapted from the Apache-2.0
licensed Streaming `BatchedWindowState` module. Point arithmetic and its
exceptional cases are supplied by the existing coordinate and batch results. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Body ====

section
/-! The existing full-size corrected physical body, with table rows supplied
by the caller. Adapted from the Apache-2.0 licensed Streaming WindowBody. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] batchWindowTree
attribute [local irreducible] yNegateProgram
  ipxProgramOf sequenceProgram surroundCompiled relabelCompiled

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Coherent ====

section
/-! Coherent composition of the full-size physical windows for arbitrary
public row values. Adapted from the Apache-2.0 licensed Streaming boundary
and address-placement proofs. The library supplies all arithmetic coherence. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

end ShorECDLP.Entrant.Single.Physical

end

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
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

attribute [class] WindowBody

/-- Optional producer support and terminal-readout evidence; the body contract is unchanged. -/
class ProducerResources (b : WindowBody) where
  support : List Wire
  body_wires : ∀ start, straightWires (b.program start) ⊆ support
  initial_support : resetWires ⊆ support
  reset_support : b.reset ⊆ support
  reset_nodup : b.reset.Nodup
  reset_zero : (0 : Wire) ∈ b.reset
  reset_one : (1 : Wire) ∈ b.reset



variable [b : WindowBody]


end ShorECDLP.Entrant.Single
end

-- ==== part: Single/Schedule ====

section
/-! A 266-bit axis uses eight 16-bit windows followed by nine 15-bit windows.
The address definition below reuses the signed-address convention of the
Apache-2.0 licensed 2607_13816 submission. -/

namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open ShorECDLP.Paper2607_13816

@[irreducible] def widths : List Nat :=
  [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15]

@[irreducible] def exponents : List Nat :=
  [250, 234, 218, 202, 186, 170, 154, 138, 122, 106, 90, 75, 60, 45, 30, 15, 0]

@[irreducible] def rightWidths : List Nat := List.replicate 13 16

@[irreducible] def rightExponents : List Nat :=
  [192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0]

theorem rightWidths_sum : rightWidths.sum = 208 := by simp [rightWidths]

theorem widths_sum : widths.sum = 266 := by
  simp [widths]

/-- Static positions for variable-width windows with fixed body record counts. -/
def positions : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | (count, width) :: ws, start =>
      List.range' (start + count) width ++ positions ws (start + count + width)

def recordCount : List (Nat × Nat) → Nat
  | [] => 0
  | (count, width) :: ws => count + width + recordCount ws

theorem positions_length (ws : List (Nat × Nat)) (start : Nat) :
    (positions ws start).length = (ws.map Prod.snd).sum := by
  induction ws generalizing start with
  | nil => simp [positions]
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp [positions, ih]

theorem positions_bounds (ws : List (Nat × Nat)) (start i : Nat)
    (hi : i ∈ positions ws start) : start ≤ i ∧ i < start + recordCount ws := by
  induction ws generalizing start with
  | nil => simp [positions] at hi
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp only [positions, List.mem_append] at hi
    rcases hi with hi | hi
    · have h := List.mem_range'.mp hi
      simp only [recordCount]
      omega
    · have h := ih _ hi
      simp only [recordCount]
      omega

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Outer ====

section
/-! Variable-width outer-axis skeleton adapted from the Apache-2.0 licensed
2607_13816 challenge migration. The caller must establish each window's
coherent semantics and bank cleanliness. -/

namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

structure Window (n : Nat) where
  wires : List Wire
  count : Nat
  program : (start : Nat) → Straight n start (start + count)

def axisCount {n : Nat} : List (Window n) → Nat
  | [] => 0
  | w :: ws => w.count + w.wires.length + axisCount ws

def nextPrior {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    List (Fin (start + count + width)) :=
  (List.ofFn (fun i : Fin width =>
    (⟨start + count + i.val, by omega⟩ : Fin (start + count + width)))).reverse ++
    prior.map (fun i => ⟨i.val, by omega⟩)

/-- Within an axis, feedback tracks only preceding Fourier outputs. -/
def axis {n : Nat} :
    (ws : List (Window n)) → (start : Nat) → List (Fin start) →
      Straight n start (start + axisCount ws)
  | [], _, _ => .done
  | w :: ws, start, prior =>
    let fourier : Straight n (start+w.count) (start+w.count+w.wires.length) :=
      castFinish (by simp) (fourierProgram n .inverse w.wires (start+w.count) (bankPrior w.count prior))
    castFinish (by simp only [axisCount]; omega)
      ((prepareOuterBank w.wires.reverse (w.program start)).append (fourier.append
        (axis ws (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior))))

def axisPositions {n : Nat} (ws : List (Window n)) (start : Nat) : List Nat :=
  positions (ws.map (fun w => (w.count, w.wires.length))) start

theorem recordCount_eq_axisCount {n : Nat} (ws : List (Window n)) :
    recordCount (ws.map (fun w => (w.count, w.wires.length))) = axisCount ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [recordCount, axisCount, ih]

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Plan ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

@[irreducible] def leftMetadata : List (Nat × Nat) :=
  (65535, 16) :: List.replicate 10 (b.records, 16) ++ List.replicate 6 (b.records, 15)

@[irreducible] def rightMetadata : List (Nat × Nat) :=
  List.replicate 13 (b.records, 16)

theorem left_widths : leftMetadata.map Prod.snd = widths := by
  simp [leftMetadata, widths]

theorem right_widths : rightMetadata.map Prod.snd = rightWidths := by
  simp [rightMetadata, rightWidths]

theorem left_record_count : recordCount leftMetadata = (65535 + 16 * b.records + 266) := by
  simp [leftMetadata, recordCount, List.replicate]; omega

theorem right_record_count : recordCount rightMetadata = (13 * b.records + 208) := by
  simp [rightMetadata, recordCount, List.replicate]; omega

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 266 := by
  rw [positions_length, left_widths, widths_sum]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length, right_widths, rightWidths_sum]

theorem projected_rows : 65536 + 23 * 32768 + 6 * 16384 = 917504 := by omega

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Rows ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological signed windows after the direct first load. -/
inductive SignedWindow where
  | left16 (index : Fin 10)
  | left15 (index : Fin 6)
  | right16 (index : Fin 13)

def firstRow (a : Fin 65536) : Fin 917504 := ⟨a.val, by omega⟩

/-- Each width-15 window aliases the two physical address halves. -/
def signedRow : SignedWindow → Fin 32768 → Fin 917504
  | .left16 j, a => ⟨65536 + j.val * 32768 + a.val, by omega⟩
  | .left15 j, a => ⟨393216 + j.val * 16384 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩
  | .right16 j, a => ⟨491520 + j.val * 32768 + a.val, by omega⟩

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Interface ====

section
/-! The mixed-width window contract. Distribution proofs may take `WindowLaw`
as a hypothesis; the concrete implementation supplies this same contract.
The physical arithmetic and its exceptional cases are inherited from the
Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def leftSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 10 => SignedWindow.left16 j) ++
    List.ofFn (fun j : Fin 6 => SignedWindow.left15 j)

@[irreducible] def rightSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 13 => SignedWindow.right16 j)

def SignedWindow.width : SignedWindow → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ => 15

def SignedWindow.exponent : SignedWindow → Nat
  | .left16 j => 234 - 16 * j.val
  | .right16 j => 192 - 16 * j.val
  | .left15 j => 75 - 15 * j.val

def SignedWindow.base (Q : Point) : SignedWindow → Point
  | .left16 _ | .left15 _ => G
  | .right16 _ => Q

def bank (width : Nat) : List Wire :=
  if width = 15 then List.range' 855 14 ++ [870] else List.range' 855 16

def digit (width : Nat) (s : BasisState) : Nat := tableAddressValue (bank width) s

def halfOrder : Nat := (order + 1) / 2

def offsetScalar (width exponent : Nat) : Nat :=
  (2^(width-1) + order - halfOrder) * 2^exponent

@[irreducible] def leftOffset : Nat := ((widths.zip exponents).drop 1).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] def rightOffset : Nat := (rightWidths.zip rightExponents).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^250 + leftOffset) • G + rightOffset • Q

noncomputable def increment (Q : Point) (w : SignedWindow) (v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^w.width + 1) : Int) •
    ((halfOrder * 2^w.exponent) • w.base Q)

noncomputable def firstUpdate (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (initialPoint Q (digit 16 s)) s

/-- A graph form avoids choosing a point from arbitrary invalid coordinates. -/
def WindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : Window n) (update : Point → BasisState → BasisState)
    (valid : BasisState → Prop) : Prop :=
  ∀ (Q : Point), order • Q = 0 → Q ≠ 0 → ∀ start history,
    CoherentlyImplementsOn ((physical.program start).instantiate
      (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (update Q)) valid

def WindowValid (w : SignedWindow) (s : BasisState) : Prop :=
  BodyValid b s ∧ (w.width = 15 → s 869 = false)

/-- The signed law names its ideal state map and fixes that map on every valid
point encoding. Its branch coefficients are uniform across input basis states. -/
structure SignedWindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : SignedWindow → Window n) where
  update : Point → SignedWindow → BasisState → BasisState
  correct : ∀ Q w s, order • Q = 0 → Q ≠ 0 → WindowValid w s → ∀ P,
    pointStateCoordinates s = fig14PointEncoding P →
    update Q w s = pointWrite (P + increment Q w (digit w.width s)) s
  coherent : ∀ w, WindowLaw coeffs (physical w) (fun Q => update Q w) (WindowValid w)

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Coefficients ====

section
/-! Mixed-width public coefficients. The coefficient encoding and torsion
identities reuse the Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The first lookup directly loads the accumulator, including infinity. -/
@[irreducible] def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^250 + leftOffset) rightOffset

@[irreducible] def oddScalar (exponent address : Nat) : Nat :=
  (2 * address + 1) * 2^exponent * halfOrder

@[irreducible] def mixedCoefficientAt (i : Fin 917504) : PointCoeff :=
  if i.val < 65536 then initialCoefficients i.val
  else if i.val < 393216 then
    coefficients (oddScalar (234 - 16 * ((i.val - 65536) / 32768)) ((i.val - 65536) % 32768)) 0
  else if i.val < 491520 then
    coefficients (oddScalar (75 - 15 * ((i.val - 393216) / 16384)) ((i.val - 393216) % 16384)) 0
  else coefficients 0 (oddScalar (192 - 16 * ((i.val - 491520) / 32768)) ((i.val - 491520) % 32768))

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Padding ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/First ====

section
/-! Direct loading with the mixed-width offsets. Adapted from the Apache-2.0
licensed Streaming PointTable; the physical theorem permits infinity. -/

namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def firstWindow : Window 917504 :=
  ⟨(bank 16).reverse, 65535, fun start => reindexStraight firstRow (firstLookupProgram start)⟩

/- The following uniform cost argument is adapted from the Apache-2.0
licensed Streaming UniformT module. -/

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Windows ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def signedWindow (w : SignedWindow) : Window 917504 :=
  ⟨(bank w.width).reverse, b.records,
    fun start => reindexStraight (signedRow w) (b.program start)⟩

theorem signedWindow_wires (w : SignedWindow) : (signedWindow w).wires = (bank w.width).reverse := by
  unfold signedWindow
  rfl

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/BodyCounts ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] yNegateProgram
  ShorECDLP.Entrant.BorrowFlag.coordinateSource placedBatchSource windowYNegate ipxProgramOf
  sequenceProgram surroundCompiled relabelCompiled

end ShorECDLP.Entrant.Single.Physical

end


-- ==== part: Single/WindowCounts ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem signedWindow_count (w : SignedWindow) : (signedWindow w).count = b.records := by
  unfold signedWindow
  rfl

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Layout ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]

open ShorECDLP.Challenge

def params : DecoderParams := ⟨266, 208, by omega, by omega, by omega, by omega⟩

/-- The first right bank follows the complete left-axis transcript. -/
def trialPositions : TrialPositions params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (65535 + 16 * b.records + 266)).toArray, by
    simpa only [List.size_toArray, params] using right_positions_length (65535 + 16 * b.records + 266)⟩

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (65535 + 16 * b.records + 266) ≤ i ∧ i < 65535 + 29 * b.records + 474 := by
  have h := positions_bounds rightMetadata (65535 + 16 * b.records + 266) i
    (show i ∈ positions rightMetadata (65535 + 16 * b.records + 266) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/OuterProperties ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

def metadataT : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (cost, width) :: ws, prior =>
      cost + fourierSlots width prior + metadataT ws (prior + width)

def metadataSlots (slots : Nat) : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (_, width) :: ws, prior =>
      slots + width + fourierSlots width prior + metadataSlots slots ws (prior + width)

theorem nextPrior_length {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    (nextPrior count width prior).length = prior.length + width := by
  simp [nextPrior, Nat.add_comm]

theorem axis_wellFormed {n : Nat} (ws : List (Window n))
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).WellFormed) (start : Nat)
    (prior : List (Fin start)) : (axis ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [axis, castFinish_wellFormed]
    apply straight_append_wellFormed _ _ (prepareOuterBank_wellFormed _ _ (hw w (by simp) start))
    apply straight_append_wellFormed
    · simpa only [castFinish_wellFormed] using fourierProgram_wellFormed n .inverse w.wires _ _
    · exact ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ _

theorem axis_slots {n : Nat} (ws : List (Window n)) (slots : Nat)
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).gateSlots ≤ slots)
    (start : Nat) (prior : List (Fin start)) :
    (axis ws start prior).gateSlots ≤
      metadataSlots slots (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, metadataSlots, Straight.gateSlots]
  | cons w ws ih =>
    simp only [axis, castFinish_gateSlots, Straight.gateSlots_append,
      prepareOuterBank_slots, List.length_reverse, fourierProgram_slots, bankPrior_length]
    have h := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    have hg := hw w (by simp) start
    simp only [nextPrior_length] at h
    simp only [List.map_cons, metadataSlots]
    omega

theorem axis_support {n : Nat} (ws : List (Window n)) (support : List Wire)
    (hb : ∀ w ∈ ws, w.wires ⊆ support)
    (hp : ∀ w ∈ ws, ∀ start read history,
      ((w.program start).instantiate read history).wires ⊆ support)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((axis ws start prior).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate]
    apply outer_append_support
    · apply prepareOuterBank_support
      · intro v hv; exact hb w (by simp) (List.mem_reverse.mp hv)
      · exact hp w (by simp) start read history
    · intro h
      apply outer_append_support
      · simp only [castFinish_instantiate]
        exact fourierProgram_support n .inverse w.wires _ _ read h support (hb w (by simp))
      · intro h₂
        exact ih (fun v hv => hb v (List.mem_cons_of_mem w hv))
          (fun v hv => hp v (List.mem_cons_of_mem w hv)) _ _ h₂

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Framing ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- A fixed query flag surrounds two axes and a reset. -/
@[irreducible] def framed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) : Straight n s f :=
  .gate (.literal (.X 836)) (castFinish h (p.append (q.append (.gate (.literal (.X 836)) r))))

theorem framed_wellFormed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (hp : p.WellFormed) (hq : q.WellFormed) (hr : r.WellFormed) :
    (framed p q r h).WellFormed := by
  unfold framed
  refine ⟨trivial, ?_⟩
  rw [castFinish_wellFormed]
  exact straight_append_wellFormed _ _ hp (straight_append_wellFormed _ _ hq ⟨trivial, hr⟩)

theorem framed_slots {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    (framed p q r h).gateSlots = p.gateSlots + q.gateSlots + r.gateSlots + 2 := by
  unfold framed
  simp only [Straight.gateSlots, castFinish_gateSlots, Straight.gateSlots_append]
  omega

theorem framed_support {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (support : List Wire) (hx : (836 : Wire) ∈ support)
    (hp : (p.instantiate read history).wires ⊆ support)
    (hq : ∀ history, (q.instantiate read history).wires ⊆ support)
    (hr : ∀ history, (r.instantiate read history).wires ⊆ support) :
    ((framed p q r h).instantiate read history).wires ⊆ support := by
  have x_support {a b : Nat} (p : Straight n a b) (history : Fin a → Bool)
      (hp : (p.instantiate read history).wires ⊆ support) :
      ((Straight.gate (.literal (.X 836)) p).instantiate read history).wires ⊆ support := by
    intro v hv
    change v ∈ circuitWires [.X 836] ++ _ at hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v = 836 := by simpa [circuitWires, gateWires] using hv
      exact he ▸ hx
    · exact hp hv
  unfold framed
  apply x_support
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history support hp
  intro hq'
  exact outer_append_support _ _ read hq' support (hq hq') (fun hr' => x_support r hr' (hr hr'))

theorem framed_run {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((framed p q r h).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836]
        ((p.append (q.append (.gate (.literal (.X 836)) r))).instantiate read history)).run := by
  unfold framed
  simp only [Straight.instantiate, TemplateGate.instantiate, castFinish_instantiate]

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Program ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] resetProgram

@[irreducible] def leftWindows : List (Window 917504) :=
  firstWindow :: leftSigned.map signedWindow

@[irreducible] def rightWindows : List (Window 917504) := rightSigned.map signedWindow

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, firstWindow, leftMetadata]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, rightMetadata]

theorem left_count : axisCount leftWindows = (65535 + 16 * b.records + 266) := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = (13 * b.records + 208) := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

@[irreducible] def resetBody (start : Nat) : Straight 917504 start (start + b.reset.length) :=
  resetProgram 917504 start b.reset

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + b.reset.length

theorem trialCount_eq : trialCount = (65535 + 29 * b.records + 474 + b.reset.length) := by
  rw [trialCount, left_count, right_count]
  omega

/-- One trial, with independent same-axis feedback histories and a final reset. -/
@[irreducible] def trial (start : Nat) : Straight 917504 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

@[irreducible] def program : Straight 917504 0 (65535 + 29 * b.records + 474 + b.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/BodyPhysical ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] yNegateProgram ipxProgramOf

end ShorECDLP.Entrant.Single.Physical

end


-- ==== part: Single/WindowProperties ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] firstLookupProgram

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Validity ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/ResourceArithmetic ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/TrialValidity ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/ProgramShape ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


-- ==== part: Single/Resources ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end


namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def ProducerResources.ofBody (body : WindowBody) (hn : body.reset.Nodup)
    (h0 : (0 : Wire) ∈ body.reset) (h1 : (1 : Wire) ∈ body.reset) : ProducerResources body where
  support := body.support
  body_wires := body.wires
  initial_support := (List.subset_cons_of_subset 837 (List.Subset.refl _)).trans body.skeleton_support
  reset_support := body.reset_support
  reset_nodup := hn
  reset_zero := h0
  reset_one := h1

end ShorECDLP.Entrant.Single

-- ==== bundle: Single/Fourier ====

set_option linter.unusedSectionVars false


/-! Circular Fourier concentration and recorded half-bin rounding.
The sharp pointwise Fourier estimate is inherited from the
single-trial certificate 8c5e5431, retaining its original attribution. -/

-- ==== part: Single/WindowMassSharp ====

section
/- Copied from public promoted submission commit 8321638bca0ea97505a1fae2e711c0f52b0d2a2e. -/

/-! Sharp window mass for quantum phase estimation.

With `N = 2 ^ t ≥ 128 r` outcomes, the QPE outcome distribution for the phase `n / r`
puts mass at least `200 / 201` on the outcomes `a` whose rounding `round (r a / N)`
equals `n`.  Compared with `WindowMass.lean`, the pointwise estimate uses
`sin z ≥ z - z ^ 3 / 6` and `sin z = cos (π / 2 - z) ≥ 1 - (π / 2 - z) ^ 2 / 2`, giving
`1 / sin² z ≤ (3 / 2) (1 / z² + 1 / (π - z)²)` on `(0, π)`, so that
`|amplitude a|² ≤ 3 / (2 π²) (1 / u² + 1 / (N - u)²)`.  The two families of terms are
regrouped by the wrapped distances `phiR`, `phiL` (each injective with values `≥ L`), and a
telescoping estimate bounds the tail by `3 / (π² (L - 1)) < 1 / 201` for `L ≥ 64`. -/

namespace ShorECDLP.Entrant

namespace WindowMassSharpProof

open Finset

lemma nat_eq_of_abs_lt (a b : ℕ) (h : |(a : ℝ) - b| < 1) : a = b := by
  rw [abs_lt] at h
  rcases lt_trichotomy a b with hab | hab | hab
  · have h1 : a + 1 ≤ b := hab
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h1
    linarith [h.1]
  · exact hab
  · have h1 : b + 1 ≤ a := hab
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h1
    linarith [h.2]

lemma sum_range_inv_sq_le (L : ℝ) (hL : 1 < L) (M : ℕ) :
    ∑ k ∈ range M, 1 / (L + k) ^ 2 ≤ 1 / (L - 1) - 1 / (L - 1 + M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : 0 < L - 1 + M := by linarith
    have h2 : 0 < L + M := by linarith
    have : 1 / (L + M) ^ 2 ≤
        1 / (L - 1 + M) - 1 / (L - 1 + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [show L - 1 + (M + 1) = L + M by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (S : Finset ℕ) (φ : ℕ → ℝ) (L : ℝ) (hL : 1 < L)
    (hφ : ∀ a ∈ S, L ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ 1 / (L - 1) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - L⌋₊ with hg
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - L)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - L)
    simp only [hg] at hab
    rw [hab] at h1 h2
    apply hsep a ha b hb
    rw [abs_lt]; constructor <;> linarith
  have step1 : ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ ∑ a ∈ S, 1 / (L + g a) ^ 2 := by
    apply sum_le_sum
    intro a ha
    have h1 : (g a : ℝ) ≤ φ a - L := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : (0 : ℝ) ≤ g a := Nat.cast_nonneg _
    have h2 : 0 < L + g a := by linarith
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have step2 : ∑ a ∈ S, 1 / (L + g a) ^ 2 = ∑ k ∈ S.image g, 1 / (L + k) ^ 2 := by
    rw [sum_image hinj]
  have step3 : ∑ k ∈ S.image g, 1 / (L + k) ^ 2 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / (L + k) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      exact Nat.lt_succ_of_le (le_sup ha)
    · intro k _ _
      positivity
  have h4 := sum_range_inv_sq_le L hL (S.sup g + 1)
  have h5 : 0 ≤ 1 / (L - 1 + ((S.sup g + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < L - 1 + ((S.sup g + 1 : ℕ) : ℝ) := by linarith
    positivity
  linarith

lemma sin_ge_cubic (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun x => Real.sin x - x + x ^ 3 / 6
  have hd : ∀ x, HasDerivAt f (Real.cos x - 1 + x ^ 2 / 2) x := by
    intro x
    have := ((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 3 x).div_const 6)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have h := hmono hx
  simp only [f, Real.sin_zero] at h
  linarith

lemma inv_sq_add_inv_sq_ge (z w : ℝ) (hz : 0 < z) (hw : 0 < w) :
    8 / (z + w) ^ 2 ≤ 1 / z ^ 2 + 1 / w ^ 2 := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (z - w), mul_pos hz hw, mul_pos (mul_pos hz hw) (mul_pos hz hw),
    mul_nonneg (mul_pos hz hw).le (sq_nonneg (z - w))]

lemma sin_sq_mul_ge_half (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ Real.pi / 2) :
    2 / 3 ≤ Real.sin z ^ 2 * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hw : 0 < Real.pi - z := by linarith
  have hcub := sin_ge_cubic z hz0.le
  rcases le_total z 1 with h1 | h1
  · -- z ≤ 1
    have hs : 5 * z / 6 ≤ Real.sin z := by nlinarith [mul_pos hz0 hz0]
    have ha : 25 / 36 ≤ Real.sin z ^ 2 * (1 / z ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hb : 0 ≤ Real.sin z ^ 2 * (1 / (Real.pi - z) ^ 2) := by positivity
    rw [mul_add]
    linarith
  rcases le_total z (6 / 5) with h2 | h2
  · -- 1 ≤ z ≤ 6/5
    have hs : 19 * z / 25 ≤ Real.sin z := by nlinarith [mul_pos hz0 hz0]
    have hs2 : 361 * z ^ 2 / 625 ≤ Real.sin z ^ 2 := by nlinarith
    have ha : 361 / 625 ≤ Real.sin z ^ 2 * (1 / z ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hb : 5776 / 46225 ≤ Real.sin z ^ 2 * (1 / (Real.pi - z) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (Real.pi - z) ^ 2 ≤ (43 / 20) ^ 2 := by
        apply pow_le_pow_left₀ hw.le
        norm_num at hpi2 ⊢
        linarith
      nlinarith
    rw [mul_add]
    linarith
  · -- 6/5 ≤ z ≤ π/2
    have hy0 : 0 ≤ Real.pi / 2 - z := by linarith
    have hy1 : Real.pi / 2 - z ≤ 3 / 8 := by norm_num at hpi2; linarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - z)
    rw [Real.cos_pi_div_two_sub] at hcos
    have hs : 7437 / 8000 ≤ Real.sin z := by nlinarith
    have hs2 : 86 / 100 ≤ Real.sin z ^ 2 := by nlinarith
    have hT := inv_sq_add_inv_sq_ge z (Real.pi - z) hz0 hw
    rw [show z + (Real.pi - z) = Real.pi by ring] at hT
    have hT' : 8 / 10 ≤ 8 / Real.pi ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      norm_num at hpi2
      nlinarith
    have hT0 : 0 ≤ 1 / z ^ 2 + 1 / (Real.pi - z) ^ 2 := by positivity
    nlinarith

lemma sin_sq_mul_ge (z : ℝ) (hz0 : 0 < z) (hz1 : z < Real.pi) :
    2 / 3 ≤ Real.sin z ^ 2 * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) := by
  rcases le_total z (Real.pi / 2) with h | h
  · exact sin_sq_mul_ge_half z hz0 h
  · have := sin_sq_mul_ge_half (Real.pi - z) (by linarith) (by linarith)
    rw [Real.sin_pi_sub, sub_sub_cancel] at this
    linarith [add_comm (1 / (Real.pi - z) ^ 2) (1 / z ^ 2)]

lemma amp_normSq_le (N : ℕ) (x : ℝ) (hs : Real.sin (x / 2) ≠ 0) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ (1 / ((N : ℝ) * |Real.sin (x / 2)|)) ^ 2 := by
  set ω := Complex.exp (Complex.I * (x : ℂ)) with hωdef
  have hω1 : ‖ω - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [hωdef, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  have hpos : 0 < |Real.sin (x / 2)| := abs_pos.mpr hs
  have hω : ω ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hω1
    linarith
  have hωn : ‖ω‖ = 1 := Complex.norm_exp_I_mul_ofReal x
  have hnum : ‖ω ^ N - 1‖ ≤ 2 := by
    calc ‖ω ^ N - 1‖ ≤ ‖ω ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hωn]; norm_num
  rw [geom_sum_eq hω, Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_inv,
    Complex.norm_natCast, hω1]
  apply pow_le_pow_left₀ (by positivity)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [one_div, mul_inv, ← div_eq_inv_mul, ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ hNr.le
  rw [div_le_iff₀ (by positivity)]
  have e : |Real.sin (x / 2)|⁻¹ * (2 * |Real.sin (x / 2)|) = 2 := by
    field_simp
  rw [e]
  exact hnum

lemma orth (N : ℕ) (hN : 0 < N) (y y' : ℕ) (hy : y < N) (hy' : y' < N) :
    ∑ a ∈ range N, Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a =
      if y = y' then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · set z := Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) with hzdef
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hz : z ^ N = 1 := by
      rw [hzdef, ← Complex.exp_nat_mul]
      have : (N : ℂ) * (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) =
          (((y' : ℤ) - y : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hzdef, Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have h2pi : (2 * Real.pi * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hc : ((y' : ℂ) - y) = m * N := by
        have := congrArg (fun w => w * N / (2 * Real.pi * Complex.I)) hm
        simp only at this
        field_simp at this
        linear_combination this
      have hi : ((y' : ℤ) - y) = m * N := by exact_mod_cast hc
      have hN' : (0 : ℤ) < N := by exact_mod_cast hN
      have hm1 : m < 1 := by
        by_contra hc'
        push_neg at hc'
        nlinarith
      have hm2 : -1 < m := by
        by_contra hc'
        push_neg at hc'
        nlinarith
      have hm0 : m = 0 := by omega
      subst hm0
      apply h
      omega
    rw [geom_sum_eq hz1, hz, sub_self, zero_div]

/-- The squared QPE amplitude at outcome `a`, for phase `β`. -/
noncomputable def ampSq (N : ℕ) (β : ℝ) (a : ℕ) : ℝ :=
  Complex.normSq (((N : ℂ)⁻¹) * ∑ y ∈ range N,
    Complex.exp (Complex.I * ((2 * Real.pi * (β - (a : ℝ) / (N : ℝ)) : ℝ) : ℂ)) ^ y)

lemma ampSq_expand (N : ℕ) (β : ℝ) (a : ℕ) :
    ((ampSq N β a : ℝ) : ℂ) = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
        Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
  unfold ampSq
  rw [← Complex.mul_conj, map_mul, map_inv₀, Complex.conj_natCast, map_sum,
    mul_mul_mul_comm, ← pow_two, sum_mul_sum]
  congr 1
  refine sum_congr rfl (fun y _ => sum_congr rfl (fun y' _ => ?_))
  simp only [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
  push_cast
  ring

lemma parseval (N : ℕ) (hN : 0 < N) (β : ℝ) :
    ∑ a ∈ range N, ampSq N β a = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply Complex.ofReal_injective
  calc (((∑ a ∈ range N, ampSq N β a : ℝ)) : ℂ)
      = ∑ a ∈ range N, ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
        push_cast
        exact sum_congr rfl (fun a _ => ampSq_expand N β a)
    _ = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            ∑ a ∈ range N, Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
        rw [← mul_sum]
        congr 1
        rw [sum_comm]
        refine sum_congr rfl (fun y _ => ?_)
        rw [sum_comm]
        refine sum_congr rfl (fun y' _ => ?_)
        rw [mul_sum]
    _ = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            (if y = y' then (N : ℂ) else 0) := by
        congr 1
        refine sum_congr rfl (fun y hy => sum_congr rfl (fun y' hy' => ?_))
        rw [orth N hN y y' (mem_range.mp hy) (mem_range.mp hy')]
    _ = ((1 : ℝ) : ℂ) := by
        simp only [mul_ite, mul_zero, sum_ite_eq, mem_range, sub_self, mul_zero,
          Complex.exp_zero, one_mul]
        rw [sum_ite_of_true (fun y hy => mem_range.mp hy), sum_const, card_range, nsmul_eq_mul]
        field_simp
        simp

lemma point_bound_sharp (N : ℕ) (hN : 0 < N) (x u : ℝ) (hu0 : 0 < u) (huN : u < N)
    (hx : x / 2 = Real.pi * u / N ∨ x / 2 = -(Real.pi * u / N)) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ 3 / (2 * Real.pi ^ 2) * (1 / u ^ 2 + 1 / ((N : ℝ) - u) ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set z := Real.pi * u / N with hz
  have hz0 : 0 < z := by positivity
  have hzπ : z < Real.pi := by
    rw [hz, div_lt_iff₀ hNR]
    nlinarith [Real.pi_pos]
  have hspos : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz0 hzπ
  have habs : |Real.sin (x / 2)| = Real.sin z := by
    rcases hx with hx | hx <;> rw [hx]
    · exact abs_of_pos hspos
    · rw [Real.sin_neg, abs_neg]; exact abs_of_pos hspos
  have hne : Real.sin (x / 2) ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; linarith
  have h1 := amp_normSq_le N x hne
  rw [habs] at h1
  refine h1.trans ?_
  have key := sin_sq_mul_ge z hz0 hzπ
  have hNu : (N : ℝ) - u ≠ 0 := by linarith
  have hz' : Real.pi - z = Real.pi * ((N : ℝ) - u) / N := by
    rw [hz]; field_simp
  have e : 3 / (2 * Real.pi ^ 2) * (1 / u ^ 2 + 1 / ((N : ℝ) - u) ^ 2) =
      (3 / 2) * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) / (N : ℝ) ^ 2 := by
    rw [hz', hz]
    field_simp
  rw [e, div_pow, one_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg (N : ℝ))]

/-- Wrapped distance from `c` going right (mod `N`). -/
noncomputable def phiR (N : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  if c ≤ (a : ℝ) then (a : ℝ) - c else (N : ℝ) - c + a

/-- Wrapped distance from `c` going left (mod `N`). -/
noncomputable def phiL (N : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  if (a : ℝ) ≤ c then c - (a : ℝ) else (N : ℝ) + c - a

lemma phiR_sep (N : ℕ) (c : ℝ) (a b : ℕ) (ha : a < N) (hb : b < N)
    (h : |phiR N c a - phiR N c b| < 1) : a = b := by
  have ha' : a + 1 ≤ N := ha
  have hb' : b + 1 ≤ N := hb
  have ha1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb1 : (b : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  apply nat_eq_of_abs_lt
  unfold phiR at h
  rw [abs_lt] at h ⊢
  split_ifs at h <;> constructor <;> linarith [h.1, h.2]

lemma phiL_sep (N : ℕ) (c : ℝ) (a b : ℕ) (ha : a < N) (hb : b < N)
    (h : |phiL N c a - phiL N c b| < 1) : a = b := by
  have ha' : a + 1 ≤ N := ha
  have hb' : b + 1 ≤ N := hb
  have ha1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb1 : (b : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  apply nat_eq_of_abs_lt
  unfold phiL at h
  rw [abs_lt] at h ⊢
  split_ifs at h <;> constructor <;> linarith [h.1, h.2]

lemma window_cases (r N n a : ℕ) (hN : 0 < N) (h : ¬ (2 * r * a + N) / (2 * N) = n) :
    2 * N * n + N ≤ 2 * r * a ∨ 2 * r * a + N < 2 * N * n := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · right
    rw [Nat.div_lt_iff_lt_mul (by omega)] at h
    linarith [h]
  · left
    have h' : n + 1 ≤ (2 * r * a + N) / (2 * N) := h
    rw [Nat.le_div_iff_mul_le (by omega)] at h'
    linarith [h']

end WindowMassSharpProof

end ShorECDLP.Entrant

end

namespace ShorECDLP.Entrant.WindowMassSharpProof
open Finset
noncomputable section

/-- Concentration in a circular interval, including phases near zero. -/
theorem circular_mass (N : Nat) (hN : 0 < N) (β L : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hL : 1 < L) :
    1 - 3 / (Real.pi ^ 2 * (L - 1)) ≤
      ∑ a ∈ range N,
        if phiR N (N * β) a < L ∨ phiL N (N * β) a < L
        then ampSq N β a else 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let c : ℝ := N * β
  have hc0 : 0 ≤ c := mul_nonneg hNR.le hβ0
  have hcN : c < N := by dsimp [c]; nlinarith
  let S := (range N).filter (fun a => ¬ (phiR N c a < L ∨ phiL N c a < L))
  have hSN : ∀ a ∈ S, a < N := fun a ha => mem_range.mp (mem_filter.mp ha).1
  have hR : ∀ a ∈ S, L ≤ phiR N c a := by
    intro a ha
    exact le_of_not_gt (fun h => (mem_filter.mp ha).2 (Or.inl h))
  have hL' : ∀ a ∈ S, L ≤ phiL N c a := by
    intro a ha
    exact le_of_not_gt (fun h => (mem_filter.mp ha).2 (Or.inr h))
  have hpt : ∀ a ∈ S, ampSq N β a ≤
      3 / (2 * Real.pi ^ 2) * (1 / (phiR N c a) ^ 2 + 1 / (phiL N c a) ^ 2) := by
    intro a ha
    have haN : (a : ℝ) < N := by exact_mod_cast hSN a ha
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hR' := hR a ha
    have hL'' := hL' a ha
    by_cases hca : c ≤ (a : ℝ)
    · have e1 : phiR N c a = (a : ℝ) - c := by simp [phiR, hca]
      have hu : 0 < (a : ℝ) - c := by rw [e1] at hR'; linarith
      have e2 : phiL N c a = (N : ℝ) - ((a : ℝ) - c) := by
        rw [phiL, if_neg (by linarith)]; ring
      rw [e1, e2]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) ((a : ℝ) - c)
        hu (by linarith) (Or.inr (by dsimp [c]; field_simp; ring))
    · have hca' : (a : ℝ) < c := lt_of_not_ge hca
      have e1 : phiR N c a = (N : ℝ) - (c - (a : ℝ)) := by
        rw [phiR, if_neg hca]; ring
      have e2 : phiL N c a = c - (a : ℝ) := by simp [phiL, hca'.le]
      rw [e1, e2, add_comm (1 / ((N : ℝ) - (c - (a : ℝ))) ^ 2)]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) (c - (a : ℝ))
        (by linarith) (by linarith) (Or.inl (by dsimp [c]; field_simp))
  have sR := sum_inv_sq_le S (phiR N c) L hL hR
    (fun a ha b hb h => phiR_sep N c a b (hSN a ha) (hSN b hb) h)
  have sL := sum_inv_sq_le S (phiL N c) L hL hL'
    (fun a ha b hb h => phiL_sep N c a b (hSN a ha) (hSN b hb) h)
  have htail : ∑ a ∈ S, ampSq N β a ≤ 3 / (Real.pi ^ 2 * (L - 1)) := by
    calc
      _ ≤ 3 / (2 * Real.pi ^ 2) * (1 / (L - 1) + 1 / (L - 1)) := by
        refine (sum_le_sum hpt).trans ?_
        rw [← mul_sum, sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (add_le_add sR sL) (by positivity)
      _ = _ := by field_simp; ring
  have hsplit : (∑ a ∈ range N,
      if phiR N c a < L ∨ phiL N c a < L then ampSq N β a else 0) =
      (∑ a ∈ range N, ampSq N β a) - ∑ a ∈ S, ampSq N β a := by
    rw [eq_sub_iff_add_eq, show ∑ a ∈ S, ampSq N β a =
      ∑ a ∈ range N, if ¬ (phiR N c a < L ∨ phiL N c a < L) then ampSq N β a else 0
      from sum_filter _ _]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  change _ ≤ ∑ a ∈ range N, if phiR N c a < L ∨ phiL N c a < L then _ else _
  rw [hsplit, parseval N hN β]
  linarith

end
end ShorECDLP.Entrant.WindowMassSharpProof

namespace ShorECDLP.Entrant.RoundedReadout
noncomputable section

/-- Exact arithmetic for the proposed public resource bounds. -/
theorem target_score : 855 * 15398440784 = 13165666870320 := by norm_num

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open Finset
noncomputable section

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section

theorem round_nat_ratio (n r : Nat) (hr : 0 < r) :
    round ((n : ℝ) / r) = ((2 * n + r) / (2 * r) : Nat) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlo := Nat.div_mul_le_self (2 * n + r) (2 * r)
  have hhi := Nat.lt_mul_div_succ (2 * n + r) (by omega : 0 < 2 * r)
  have hl : ((2 * n + r) / (2 * r) : Nat) * (2 * (r : ℝ)) ≤ 2 * n + r := by exact_mod_cast hlo
  have hh : 2 * (n : ℝ) + r < 2 * r * (((2 * n + r) / (2 * r) : Nat) + 1) := by exact_mod_cast hhi
  apply round_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor
  · rw [le_div_iff₀ hrR]; nlinarith
  · rw [div_lt_iff₀ hrR]; nlinarith

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open scoped BigOperators
noncomputable section

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section

set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816
open scoped BigOperators
noncomputable section
set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.RoundedReadout





namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300

/-- Taylor's lower estimate is stronger than the coefficient3 bound at1/16. -/
theorem sin_pi_mul_ge_three (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/16) :
    3*u ≤ Real.sin (Real.pi*u) := by
  have hpL : (31 : ℝ)/10 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpU : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpu0 : 0 ≤ Real.pi*u := mul_nonneg Real.pi_pos.le hu0
  have hpu : Real.pi*u ≤ 4*u := mul_le_mul_of_nonneg_right hpU hu0
  have hu2 : u^2 ≤ (1/16 : ℝ)^2 := pow_le_pow_left₀ hu0 hu 2
  have hu3 : u^3 ≤ u/256 := by
    have h := mul_le_mul_of_nonneg_left hu2 hu0
    nlinarith
  have hcube : (Real.pi*u)^3 ≤ u/4 := by
    calc
      _ ≤ (4*u)^3 := pow_le_pow_left₀ hpu0 hpu 3
      _ = 64*u^3 := by ring
      _ ≤ 64*(u/256) := mul_le_mul_of_nonneg_left hu3 (by norm_num)
      _ = u/4 := by ring
  have hs := sin_ge_cubic (Real.pi*u) hpu0
  have hp := mul_le_mul_of_nonneg_right hpL hu0
  nlinarith

theorem table_budget : 65536+(10+13)*32768+6*16384 ≤ 983040 := by norm_num

theorem left_width : 16+10*16+6*15=266 := by norm_num
theorem right_width : 13*16=208 := by norm_num

end
end ShorECDLP.Entrant.NeighborReadout

/- Append after Core.lean; only existing sharp-window interfaces are used. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

private theorem sine_positive_local (u : ℝ) (hu0 : 0<u) (hu : u≤1/16) :
    0<Real.sin (Real.pi*u) :=
  lt_of_lt_of_le (by positivity) (sin_pi_mul_ge_three u hu0.le hu)

/-- Both directed circular distances give the same absolute sine denominator. -/
theorem abs_sin_phiR (N : Nat) (hN : 0<N) (β : ℝ) (a : Nat)
    (hd : 0<phiR N ((N : ℝ)*β) a)
    (hsmall : phiR N ((N : ℝ)*β) a/(N : ℝ)≤1/16) :
    |Real.sin (Real.pi*(β-(a : ℝ)/N))| =
      Real.sin (Real.pi*(phiR N ((N : ℝ)*β) a/(N : ℝ))) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hs := sine_positive_local _ (div_pos hd hNR) hsmall
  by_cases hca : (N : ℝ)*β≤a
  · have he : Real.pi*(β-(a : ℝ)/N) =
        -(Real.pi*(phiR N ((N : ℝ)*β) a/(N : ℝ))) := by
      simp only [phiR,if_pos hca]
      field_simp
      ring
    rw [he,Real.sin_neg,abs_neg,abs_of_pos hs]
  · have he : Real.pi*(β-(a : ℝ)/N) =
        Real.pi-Real.pi*(phiR N ((N : ℝ)*β) a/(N : ℝ)) := by
      simp only [phiR,if_neg hca]
      field_simp
      ring
    rw [he,Real.sin_pi_sub,abs_of_pos hs]

theorem abs_sin_phiL (N : Nat) (hN : 0<N) (β : ℝ) (a : Nat)
    (hd : 0<phiL N ((N : ℝ)*β) a)
    (hsmall : phiL N ((N : ℝ)*β) a/(N : ℝ)≤1/16) :
    |Real.sin (Real.pi*(β-(a : ℝ)/N))| =
      Real.sin (Real.pi*(phiL N ((N : ℝ)*β) a/(N : ℝ))) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hs := sine_positive_local _ (div_pos hd hNR) hsmall
  by_cases hca : (a : ℝ)≤(N : ℝ)*β
  · have he : Real.pi*(β-(a : ℝ)/N) =
        Real.pi*(phiL N ((N : ℝ)*β) a/(N : ℝ)) := by
      simp only [phiL,if_pos hca]
      field_simp
    rw [he,abs_of_pos hs]
  · have he : Real.pi*(β-(a : ℝ)/N) =
        Real.pi*(phiL N ((N : ℝ)*β) a/(N : ℝ))-Real.pi := by
      simp only [phiL,if_neg hca]
      field_simp
      ring
    rw [he,Real.sin_sub_pi,abs_neg,abs_of_pos hs]

end
end ShorECDLP.Entrant.NeighborReadout

/- Append after Core; sharpen the existing proof before its coarse numeric weakening. -/
namespace ShorECDLP.Entrant.WindowMassSharpProof
open Finset
noncomputable section

end
end ShorECDLP.Entrant.WindowMassSharpProof

/- Append after Core+Geometry. Requires accepted precision circular_mass. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000

end
end ShorECDLP.Entrant.NeighborReadout

/- Append after Core+Geometry+LeftMass+Tail. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300

def neighborWord (b : Nat) (j : ℤ) : Nat :=
  (((b : ℤ)+j)%(2^208 : Nat)).toNat

end
end ShorECDLP.Entrant.NeighborReadout

/- Append after Coverage. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.NeighborReadout

/-! EDITABLE. Single-trial entrant: mixed-width distribution and decoder proofs.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/History ====

section
/-! Dynamic histories for compositional straight-program distribution proofs.
The protected straight semantics and record decomposition are Apache-2.0;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Total extension; actual branches have exactly the required record length. -/
def historyAfter {start : Nat} (finish : Nat) (history : Fin start → Bool)
    (bits : List Bool) : Fin finish → Bool :=
  fun i => ((List.ofFn history ++ bits)[i.val]?).getD false

theorem historyAfter_nil {start : Nat} (history : Fin start → Bool) :
    historyAfter start history List.nil = history := by
  funext i
  simp [historyAfter]

theorem historyAfter_step {start : Nat} (finish : Nat) (history : Fin start → Bool)
    (bit : Bool) (bits : List Bool) :
    historyAfter finish (Fin.lastCases bit history) bits =
      historyAfter finish history (bit :: bits) := by
  funext i
  simp only [historyAfter, List.ofFn_succ', Fin.lastCases_castSucc, Fin.lastCases_last,
    List.concat_eq_append, List.append_assoc, List.singleton_append]

theorem historyAfter_list {start finish : Nat} (history : Fin start → Bool)
    (bits : List Bool) (hlen : start + bits.length = finish) :
    List.ofFn (historyAfter finish history bits) = List.ofFn history ++ bits := by
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, historyAfter]
    rw [List.getElem?_eq_getElem hj, Option.getD_some]

/-- Exact branch enumeration, retaining the history used by the suffix. -/
theorem append_run_history {n start mid finish : Nat}
    (p : Straight n start mid) (q : Straight n mid finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((p.append q).instantiate read history).run =
      ((p.instantiate read history).run).flatMap (fun a =>
        ((q.instantiate read (historyAfter mid history a.history)).run).map a.seq) := by
  induction p with
  | done =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, historyAfter_nil]
    apply Eq.symm
    apply List.map_id'
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro b hb
    rfl
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro b hb
    rfl
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
      List.flatMap_append]
    congr 1 <;>
      (apply List.flatMap_congr; intro a ha
       simp only [historyAfter_step]
       apply List.map_congr_left; intro b hb; rfl)

theorem historyAfter_old {start finish : Nat} (history : Fin start → Bool)
    (bits : List Bool) (hle : start ≤ finish) (i : Fin start) :
    historyAfter finish history bits ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = history i := by
  simp only [historyAfter]
  rw [List.getElem?_append_left (show i.val < (List.ofFn history).length by
    simpa only [List.length_ofFn] using i.isLt)]
  simp

theorem bankPrior_map {start : Nat} (count : Nat) (prior : List (Fin start))
    (history : Fin start → Bool) (bits : List Bool) :
    (bankPrior count prior).map (historyAfter (start + count) history bits) = prior.map history := by
  simp only [bankPrior, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  exact historyAfter_old history bits (by omega) i

theorem nextPrior_map {start : Nat} (count width : Nat) (prior : List (Fin start))
    (history : Fin start → Bool) (arith bits : List Bool)
    (ha : arith.length = count) (hb : bits.length = width) :
    (nextPrior count width prior).map
      (historyAfter (start + count + width)
        (historyAfter (start + count) history arith) bits) = bits.reverse ++ prior.map history := by
  let h₁ := historyAfter (start + count) history arith
  have hold (i : Fin start) :
      historyAfter (start + count + width) h₁ bits ⟨i.val, by omega⟩ = history i := by
    rw [historyAfter_old h₁ bits (by omega) ⟨i.val, by omega⟩]
    exact historyAfter_old history arith (by omega) i
  have hbits : List.ofFn (fun i : Fin width =>
      historyAfter (start + count + width) h₁ bits ⟨start + count + i.val, by omega⟩) = bits := by
    apply List.ext_getElem
    · simp [hb]
    · intro i hi hj
      simp only [List.getElem_ofFn, historyAfter]
      rw [List.getElem?_append_right (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [nextPrior, List.map_append, List.map_reverse, List.map_ofFn, List.map_map,
    Function.comp_def]
  rw [hbits]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hold i

/-- Preparation contributes no records and is an ordinary Hadamard prefix. -/
theorem prepare_run {n start finish : Nat} (ws : List Wire) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((prepareOuterBank ws p).instantiate read history).run =
      ((p.instantiate read history).run).map (fun b =>
        ({ history := List.nil, kraus := Quantum.run (ws.map Gate.H) } : InstrumentBranch).seq b) := by
  induction ws with
  | nil =>
    simp only [prepareOuterBank, List.foldr_nil, List.map_nil, Quantum.run]
    apply Eq.symm
    apply List.map_id'
  | cons w ws ih =>
    change (AdaptiveCircuit.unitary [.H w]
      ((prepareOuterBank ws p).instantiate read history)).run = _
    simp only [AdaptiveCircuit.run, ih, List.map_map, Function.comp_def, List.map_cons]
    apply List.map_congr_left
    intro b hb
    rfl

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Transcript ====

section
/-! Mixed-width transcript extraction, adapted from the Apache-2.0 licensed
Streaming fixed-word proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

inductive Transcript : List (Nat × Nat) → List Bool → List Bool → Prop
  | nil : Transcript List.nil List.nil List.nil
  | cons (count width : Nat) (ws : List (Nat × Nat)) (a bits rest out : List Bool)
      (ha : a.length = count) (hb : bits.length = width)
      (ht : Transcript ws rest out) :
      Transcript ((count, width) :: ws) (a ++ bits ++ rest) (bits ++ out)

theorem Transcript.actual_bits {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) (before after : List Bool) :
    (positions ws before.length).map (fun i => (before ++ history ++ after)[i]?) = bits.map some := by
  induction h generalizing before with
  | nil => rfl
  | cons count width ws a bs rest out ha hb ht ih =>
    rw [positions, List.map_append, List.map_append]
    have hhead := actual_bits_range (before ++ a) bs (rest ++ after)
    have htail := ih (before ++ a ++ bs)
    simp only [List.length_append, ha, hb, List.append_assoc] at hhead htail
    simp only [List.append_assoc, Nat.add_assoc]
    rw [hhead, htail]

theorem Transcript.readWord {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) (before after : List Bool) :
    ShorECDLP.Challenge.readWord (before ++ history ++ after) (positions ws before.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (h.actual_bits before after)

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Words ====

section
/-! Mixed-radix path enumeration. Adapted from the Apache-2.0 licensed
Streaming distribution proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] fourierOutcomes

/-- Enumerate exactly one fixed-width word per chronological window. -/
def inputWords : List Nat → List (List (List Bool))
  | [] => [[]]
  | w :: ws => (fourierOutcomes w).flatMap (fun input =>
      (inputWords ws).map (fun rest => input :: rest))

theorem inputWords_mem (ws : List Nat) (inputs : List (List Bool)) :
    inputs ∈ inputWords ws ↔ inputs.map List.length = ws := by
  induction ws generalizing inputs with
  | nil => cases inputs <;> simp [inputWords]
  | cons w ws ih =>
    cases inputs with
    | nil => simp [inputWords, List.mem_flatMap]
    | cons input inputs =>
      simp [inputWords, List.mem_flatMap, List.mem_map, List.cons.injEq,
        fourierOutcomes_mem, ih, and_assoc, and_left_comm, and_comm]

theorem flatten_length_of_widths (inputs : List (List Bool)) :
    inputs.flatten.length = (inputs.map List.length).sum := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih => simp only [List.flatten_cons, List.length_append,
      List.map_cons, List.sum_cons, ih]

theorem outcomes_append (n m : Nat) : fourierOutcomes (n + m) =
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem inputWords_flatten (ws : List Nat) :
    (inputWords ws).map List.flatten = fourierOutcomes ws.sum := by
  induction ws with
  | nil => simp [inputWords, fourierOutcomes]
  | cons w ws ih =>
    rw [List.sum_cons, outcomes_append]
    simp only [inputWords, List.map_flatMap, List.map_map, Function.comp_def, List.flatten_cons]
    apply congrArg (List.flatMap · (fourierOutcomes w))
    funext input
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (input ++ ·)) ih

theorem outcomes_reverse_perm (n : Nat) :
    ((fourierOutcomes n).map List.reverse).Perm (fourierOutcomes n) := by
  apply (List.perm_ext_iff_of_nodup
    ((fourierOutcomes_nodup n).map List.reverse_injective) (fourierOutcomes_nodup n)).mpr
  intro bits
  simp only [List.mem_map, fourierOutcomes_mem]
  constructor
  · rintro ⟨xs, hx, rfl⟩
    simpa only [List.length_reverse] using hx
  · intro hb
    exact ⟨bits.reverse, by simpa using hb, List.reverse_reverse bits⟩

theorem inputWords_reverse_perm (ws : List Nat) :
    ((inputWords ws).map (List.map List.reverse)).Perm (inputWords ws) := by
  induction ws with
  | nil => simp [inputWords]
  | cons w ws ih =>
    simp only [inputWords]
    have he : ((fourierOutcomes w).flatMap (fun input =>
        (inputWords ws).map (fun rest => input :: rest))).map (List.map List.reverse) =
      ((fourierOutcomes w).map List.reverse).flatMap (fun input =>
        ((inputWords ws).map (List.map List.reverse)).map (fun rest => input :: rest)) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, List.map_cons]
    rw [he]
    exact (outcomes_reverse_perm w).flatMap (fun input _ => ih.map (input :: ·))

theorem inputWords_msb_perm (ws : List Nat) :
    ((inputWords ws).map (fun inputs => (inputs.map List.reverse).flatten)).Perm
      (fourierOutcomes ws.sum) := by
  have hp := (inputWords_reverse_perm ws).map List.flatten
  simpa only [List.map_map, Function.comp_def, inputWords_flatten] using hp

/-- Physical banks hold little-endian digits in most-significant-first order. -/
def scalarWord (inputs : List (List Bool)) : List Bool :=
  (inputs.map List.reverse).flatten.reverse

theorem scalarWord_perm (ws : List Nat) :
    ((inputWords ws).map scalarWord).Perm (fourierOutcomes ws.sum) := by
  have hp : ((inputWords ws).map scalarWord).Perm
      ((fourierOutcomes ws.sum).map List.reverse) := by
    simpa only [List.map_map, Function.comp_def, scalarWord] using
      (inputWords_msb_perm ws).map List.reverse
  exact hp.trans (outcomes_reverse_perm ws.sum)

theorem scalarWord_value (inputs : List (List Bool)) :
    boolWordToNat (scalarWord inputs) = fourierWordMSB (inputs.map List.reverse).flatten := by
  simpa only [scalarWord, List.reverse_reverse] using
    (fourierWordMSB_reverse (scalarWord inputs)).symm

theorem scalarWords_sum {A : Type} [AddCommMonoid A] (ws : List Nat)
    (f : List Bool → A) :
    ((inputWords ws).map (fun inputs => f (scalarWord inputs))).sum =
      ((fourierOutcomes ws.sum).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using ((scalarWord_perm ws).map f).sum_eq

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Refinement ====

section
/-! History-dependent physical refinement. Arithmetic records are retained in
execution and erased only by the protected coherent terminal-mass theorem.
Apache-2.0 Streaming proof infrastructure; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option pp.maxSteps 40
attribute [local irreducible] fourierOutcomes

structure WindowModel {n : Nat} (read : ConstantBit n → Bool) where
  physical : Window n
  point : Nat → Secp256k1.Point
  bias : Secp256k1.Point
  ideal : State →ₗ[ℂ] State
  valid : BasisState → Prop
  nodup : physical.wires.Nodup
  coherent : ∀ start history, CoherentlyImplementsOn
    ((physical.program start).instantiate read history) ideal valid

def WindowModel.step {n : Nat} {read : ConstantBit n → Bool} (w : WindowModel read)
    (prior bits : List Bool) : State →ₗ[ℂ] State :=
  (fourierBranch .inverse w.physical.wires prior bits).comp
    (w.ideal.comp (Quantum.run (w.physical.wires.reverse.map Gate.H)))

/-- Newest-first Fourier tags accompany the full physical record and Kraus map. -/
def taggedAxis {n : Nat} {read : ConstantBit n → Bool} :
    List (WindowModel read) → (start : Nat) → (Fin start → Bool) →
      List (Fin start) → List (List Bool × InstrumentBranch)
  | List.nil, _, history, prior => [(prior.map history, ⟨[], LinearMap.id⟩)]
  | w :: ws, start, history, prior =>
      (((prepareOuterBank w.physical.wires.reverse (w.physical.program start)).instantiate read history).run).flatMap
        (fun a =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
            let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
            let f : InstrumentBranch := ⟨bits, fourierBranch .inverse w.physical.wires (prior.map history) bits⟩
            (taggedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior)).map
              (fun b => (b.1, a.seq (f.seq b.2)))))

def selectedAxis {n : Nat} {read : ConstantBit n → Bool} (ws : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) : Instrument :=
  (taggedAxis ws start history prior).flatMap (fun a => (terminal a.1).map a.2.seq)

def idealAxis {n : Nat} {read : ConstantBit n → Bool} :
    List (WindowModel read) → List Bool → (List Bool → Instrument) → Instrument
  | List.nil, prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
        (idealAxis ws (bits.reverse ++ prior) terminal).map
          (fun b => ({history := bits, kraus := w.step prior bits} : InstrumentBranch).seq b))

/-- Reachability states only support facts for the exact ideal prefixes. -/
def Ready {n : Nat} {read : ConstantBit n → Bool} : List (WindowModel read) → State → Prop
  | List.nil, _ => True
  | w :: ws, ψ =>
      SupportedOn w.valid (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ) ∧
        ∀ prior bits, Ready ws (w.step prior bits ψ)

theorem support_smul {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

theorem Ready.smul {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (ψ : State) (hψ : Ready ws ψ) (c : ℂ) : Ready ws (c • ψ) := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · rw [map_smul]
      exact support_smul c hψ.1
    · intro prior bits
      rw [map_smul]
      exact ih _ (hψ.2 prior bits)

theorem flat_mass {A : Type} (xs : List A) (f : A → Instrument) (ψ : State) :
    Instrument.bornMass (xs.flatMap f) ψ = (xs.map (fun x => (f x).bornMass ψ)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, Instrument.bornMass, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] using congrArg (_ + ·) ih

theorem prefixed_mass (b : InstrumentBranch) (I : Instrument) (ψ : State) :
    Instrument.bornMass (I.map b.seq) ψ = I.bornMass (b.kraus ψ) := by
  simp only [Instrument.bornMass, List.map_map, Function.comp_def, InstrumentBranch.seq,
    LinearMap.comp_apply]


theorem seq_mass (I J : Instrument) (ψ : State) :
    (I.seq J).bornMass ψ = (I.map (fun b => J.bornMass (b.kraus ψ))).sum := by
  simp only [Instrument.seq, flat_mass, prefixed_mass]

theorem idealAxis_cons_mass {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (prior : List Bool)
    (terminal : List Bool → Instrument) (ψ : State) :
    (idealAxis (w :: ws) prior terminal).bornMass ψ =
      ((fourierOutcomes w.physical.wires.length).map (fun bits =>
        (idealAxis ws (bits.reverse ++ prior) terminal).bornMass (w.step prior bits ψ))).sum := by
  simp only [idealAxis, flat_mass, prefixed_mass]

theorem axis_run_tagged {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) :
    ((axis (ws.map WindowModel.physical) start prior).instantiate read history).run =
      (taggedAxis ws start history prior).map Prod.snd := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, axis, castFinish_instantiate]
    rw [append_run_history]
    simp only [taggedAxis, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    rw [append_run_history]
    simp only [castFinish_instantiate]
    rw [fourierProgram_run, semiclassicalFourier_run, bankPrior_map]
    simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    simp only [List.map_map, Function.comp_def]

theorem taggedAxis_transcript {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis ws start history prior) :
    ∃ bits, Transcript (ws.map (fun w => (w.physical.count, w.physical.wires.length)))
        tagged.2.history bits ∧ tagged.1 = bits.reverse ++ prior.map history := by
  induction ws generalizing start tagged with
  | nil =>
    simp only [taggedAxis, List.mem_singleton] at ht
    subst tagged
    exact ⟨[], Transcript.nil, rfl⟩
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    obtain ⟨out, htrans, htag⟩ := ih _ _ _ b hbt
    have hla : a.history.length = w.physical.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlb := (fourierOutcomes_mem _ _).mp hb
    refine ⟨bits ++ out, ?_, ?_⟩
    · simpa only [List.map_cons, InstrumentBranch.seq, List.append_assoc] using
        Transcript.cons w.physical.count w.physical.wires.length _ a.history bits b.2.history out hla hlb htrans
    · rw [htag, nextPrior_map _ _ _ _ _ _ hla hlb]
      simp only [List.reverse_append, List.append_assoc]

theorem selectedAxis_cons {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) :
    selectedAxis (w :: ws) start history prior terminal =
      (((prepareOuterBank w.physical.wires.reverse (w.physical.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
          (selectedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior) terminal).map
            (a.seq ({history := bits, kraus := fourierBranch .inverse w.physical.wires (prior.map history) bits} : InstrumentBranch)).seq)) := by
  simp only [selectedAxis, taggedAxis, List.flatMap_assoc, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro bits hb
  apply List.flatMap_congr
  intro b hbt
  apply List.map_congr_left
  intro c hc
  rcases a with ⟨ah, ak⟩
  rcases b with ⟨tag, bh, bk⟩
  rcases c with ⟨ch, ck⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedAxis_cons_mass {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) (ψ : State) :
    (selectedAxis (w :: ws) start history prior terminal).bornMass ψ =
      (((w.physical.program start).instantiate read history).run.map (fun a =>
        ((fourierOutcomes w.physical.wires.length).map (fun bits =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
          (selectedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior) terminal).bornMass
            (fourierBranch .inverse w.physical.wires (prior.map history) bits
              (a.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))))).sum)).sum := by
  rw [selectedAxis_cons, prepare_run]
  simp only [flat_mass, prefixed_mass, List.flatMap_map,
    InstrumentBranch.seq, LinearMap.comp_apply, List.nil_append]


/-- Eliminate internal arithmetic records while preserving every adaptive Fourier phase. -/
theorem selectedAxis_mass {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (terminal : List Bool → Instrument)
    (ψ : State) (hψ : Ready ws ψ) :
    (selectedAxis ws start history prior terminal).bornMass ψ =
      (idealAxis ws (prior.map history) terminal).bornMass ψ := by
  induction ws generalizing start ψ with
  | nil =>
    simp only [selectedAxis, taggedAxis, List.flatMap_cons, List.flatMap_nil, List.append_nil, idealAxis]
    exact prefixed_mass ⟨[], LinearMap.id⟩ _ ψ
  | cons w ws ih =>
    let J : Instrument := (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
      (idealAxis ws (bits.reverse ++ prior.map history) terminal).map
        ({history := bits, kraus := fourierBranch .inverse w.physical.wires (prior.map history) bits} : InstrumentBranch).seq)
    have he :
        (selectedAxis (w :: ws) start history prior terminal).bornMass ψ =
          (((w.physical.program start).instantiate read history).run.seq J).bornMass
            (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ) := by
      rw [selectedAxis_cons_mass, seq_mass]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      unfold J
      simp only [flat_mass, prefixed_mass]
      apply congrArg List.sum
      apply List.map_congr_left
      intro bits hb
      obtain ⟨c, hc⟩ := (w.coherent start history).branch_coefficient a ha
      have hstate := hc.on_supported hψ.1
      have hready : Ready ws (fourierBranch .inverse w.physical.wires (prior.map history) bits
          (a.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))) := by
        rw [hstate, map_smul]
        exact Ready.smul ws _ (hψ.2 (prior.map history) bits) c
      rw [ih _ _ _ _ hready]
      have hla : a.history.length = w.physical.count := by
        have h := straight_history_length _ read history a ha
        omega
      rw [nextPrior_map _ _ _ _ _ _ hla ((fourierOutcomes_mem _ _).mp hb)]
    rw [he, (w.coherent start history).terminalMass hψ.1 J]
    rw [idealAxis_cons_mass]
    simp only [J, flat_mass, prefixed_mass, WindowModel.step, LinearMap.comp_apply]

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/TwoAxes ====

section
/-! Two history-dependent straight axes, resetting Fourier feedback between
axes. Apache-2.0 Streaming proof pattern; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

theorem Ready.append_left {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (ψ : State) (hψ : Ready (left ++ right) ψ) :
    Ready left ψ := by
  induction left generalizing ψ with
  | nil => trivial
  | cons w ws ih => exact ⟨hψ.1, fun prior bits => ih _ (hψ.2 prior bits)⟩

/-- Every physical left-axis branch reaches the right-axis validity domain. -/
theorem taggedAxis_ready_tail {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis left start history prior) (ψ : State)
    (hψ : Ready (left ++ right) ψ) : Ready right (tagged.2.kraus ψ) := by
  induction left generalizing start tagged ψ with
  | nil =>
    simp only [taggedAxis, List.mem_singleton] at ht
    subst tagged
    exact hψ
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    rw [prepare_run] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc⟩ := (w.coherent start history).branch_coefficient a₀ ha₀
    have hs := hc.on_supported hψ.1
    have hready : Ready (ws ++ right)
        (fourierBranch .inverse w.physical.wires (prior.map history) bits
          (a₀.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))) := by
      rw [hs, map_smul]
      exact Ready.smul _ _ (hψ.2 (prior.map history) bits) c
    exact ih _ _ _ b hbt _ hready

theorem taggedAxis_history_length {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis ws start history prior) :
    tagged.2.history.length = axisCount (ws.map WindowModel.physical) := by
  have hb : tagged.2 ∈ ((axis (ws.map WindowModel.physical) start prior).instantiate read history).run := by
    rw [axis_run_tagged]
    exact List.mem_map.mpr ⟨tagged, ht, rfl⟩
  have h := straight_history_length _ read history tagged.2 hb
  omega

def pairAccept (left right : List Nat) (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  ((ShorECDLP.Challenge.readWord history left).bind (fun a =>
    (ShorECDLP.Challenge.readWord history right).map (accept a))).getD false

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/JointMass ====

section
/-! Width-independent point Fourier distribution, using the protected character
expansion (Apache-2.0; see LICENSE and NOTICE). -/
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open Quantum.OrderFinding
open scoped BigOperators
noncomputable section

/-- The coherent Fourier sum, before measuring the point register. -/
def idealPointState (Q : Point) (root : BasisState) (n m : Nat) (x y : List Bool) : State :=
  let c : ℂ := ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m)
  c • ((fourierOutcomes n).map (fun a =>
    ((fourierOutcomes m).map (fun b =>
      (c * dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x) *
        dyadicFourierKernel .inverse m (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root))).sum)).sum

/-- Character expansion applies at any two precisions and any framed root state. -/
theorem idealPointState_mass (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = m)
    (out : Fin (2 ^ n) × Fin (2 ^ m))
    (hox : fourierWordLSB x = out.1.val) (hoy : fourierWordLSB y = out.2.val) :
    normSq (idealPointState Q root n m x y) = asymmetricPairMass order n m d out := by
  unfold idealPointState
  rw [pointDoubleSum_normalize _ _ _ _ _ G Q d hd root, pow_add]
  exact asymmetric_point_character_mass order_prime G generator_order root n m d x y hx hy out hox hoy

/-- An event is selected only after each coherent point sum is complete. -/
def idealEventMass (Q : Point) (root : BasisState) (n m : Nat)
    (accept : Nat → Nat → Bool) : ℝ :=
  ((fourierOutcomes n).map (fun x => ((fourierOutcomes m).map (fun y =>
    if accept (fourierWordLSB x) (fourierWordLSB y) then
      normSq (idealPointState Q root n m x y) else 0)).sum)).sum

theorem outcome_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((fourierOutcomes n).map f).sum = ∑ v : Fin (2 ^ n), f (paperOutcomeBits n v) := by
  rw [← List.sum_toFinset _ (fourierOutcomes_nodup n)]
  symm
  apply Finset.sum_bij (fun v _ => paperOutcomeBits n v)
  · intro v _
    exact List.mem_toFinset.mpr ((fourierOutcomes_mem n _).mpr (paperOutcomeBits_length n v))
  · intro a _ b _ h
    exact paperOutcomeBits_injective n h
  · intro bs hbs
    have hl := (fourierOutcomes_mem n bs).mp (List.mem_toFinset.mp hbs)
    have hv : fourierWordLSB bs < 2 ^ n := by simpa [hl] using fourierWordLSB_lt bs
    refine ⟨⟨fourierWordLSB bs, hv⟩, Finset.mem_univ _, ?_⟩
    apply fourierWordLSB_injective _ _
    · rw [paperOutcomeBits_length, hl]
    · exact paperOutcomeBits_word n _
  · intro _ _; rfl

theorem idealEventMass_distribution (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (accept : Nat → Nat → Bool) :
    idealEventMass Q root n m accept =
      ∑ a : Fin (2 ^ n), ∑ b : Fin (2 ^ m),
        if accept a.val b.val then asymmetricPairMass order n m d (a, b) else 0 := by
  unfold idealEventMass
  simp_rw [outcome_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [paperOutcomeBits_word]
  split_ifs
  · exact idealPointState_mass Q d hd root n m _ _ (paperOutcomeBits_length n a)
      (paperOutcomeBits_length m b) (a, b) (paperOutcomeBits_word n a) (paperOutcomeBits_word m b)
  · rfl


end
end ShorECDLP.Entrant.Single

end

-- ==== part: Single/MixedKernel ====

section
/-! Exact mixed-radix Fourier composition, adapted from the Apache-2.0
Streaming distribution proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
attribute [local irreducible] fourierOutcomes

structure DigitWindow where
  width : Nat
  point : Nat → Point
  bias : Point := 0

def pathWidths (path : List (DigitWindow × List Bool)) : List Nat :=
  path.map (fun w => w.1.width)

def pathEnd : List (DigitWindow × List Bool) → List (List Bool) → Point → Point
  | (w, _) :: windows, input :: inputs, P =>
      pathEnd windows inputs (P + w.point (boolWordToNat input))
  | _, _, P => P

def inputWeight : List (DigitWindow × List Bool) → List Bool → List (List Bool) → ℂ
  | (w, output) :: windows, prior, input :: inputs =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) *
        fourierBitAmplitude .inverse input.reverse prior output *
          inputWeight windows (output.reverse ++ prior) inputs
  | _, _, _ => 1

def pointKernel (root : BasisState) :
    List (DigitWindow × List Bool) → List Bool → Point → State
  | List.nil, _, P => ket (pointWrite P root)
  | (w, output) :: windows, prior, P =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            pointKernel root windows (output.reverse ++ prior)
              (P + w.point (boolWordToNat input)))).sum

theorem flat_sum {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem pointKernel_inputs (root : BasisState)
    (path : List (DigitWindow × List Bool)) (prior : List Bool) (P : Point) :
    pointKernel root path prior P =
      ((inputWords (pathWidths path)).map (fun inputs =>
        inputWeight path prior inputs • ket (pointWrite (pathEnd path inputs P) root))).sum := by
  induction path generalizing prior P with
  | nil => simp [pointKernel, pathWidths, inputWords, inputWeight, pathEnd]
  | cons w path ih =>
    simp only [pointKernel, pathWidths, List.map_cons, inputWords, List.map_flatMap,
      List.map_map, Function.comp_def, inputWeight, pathEnd, flat_sum]
    simp_rw [ih]
    simp only [smul_smul, List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro input hi
    congr 1
    apply List.map_congr_left
    intro inputs his
    rw [mul_assoc]

def inputPairs (path : List (DigitWindow × List Bool)) (inputs : List (List Bool)) :
    List (List Bool × List Bool) :=
  (path.zip inputs).map (fun p => (p.2.reverse, p.1.2))

theorem inputWeight_amplitude (path : List (DigitWindow × List Bool))
    (prior : List Bool) (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    inputWeight path prior inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (pathWidths path).sum) *
        windowFourierAmplitude .inverse (inputPairs path inputs) prior := by
  induction path generalizing prior inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [inputWeight, inputPairs, windowFourierAmplitude, pathWidths]
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = path.length := by simpa using hl
      simp only [inputWeight, inputPairs, List.zip_cons_cons, List.map_cons,
        windowFourierAmplitude, pathWidths, List.sum_cons]
      rw [ih _ inputs ht, pow_add]
      dsimp only [pathWidths, inputPairs]
      ring

theorem inputPairs_fst (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    (inputPairs path inputs).map Prod.fst = inputs.map List.reverse := by
  induction path generalizing inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [inputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

theorem inputPairs_snd (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    (inputPairs path inputs).map Prod.snd = path.map Prod.snd := by
  induction path generalizing inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [inputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

/-- Equal widths are required only for the corresponding input and output bank. -/
theorem inputPairs_lengths (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ path, w.2.length = w.1.width)
    (hi : inputs.map List.length = pathWidths path) :
    ∀ pair ∈ inputPairs path inputs, pair.2.length = pair.1.length := by
  induction path generalizing inputs with
  | nil => simp [inputPairs]
  | cons w path ih =>
    cases inputs with
    | nil => simp [pathWidths] at hi
    | cons input inputs =>
      have hh : input.length = w.1.width ∧ inputs.map List.length = pathWidths path := by
        simpa only [List.map_cons, pathWidths, List.cons.injEq] using hi
      intro pair hp
      simp only [inputPairs, List.zip_cons_cons, List.map_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simpa only [List.length_reverse, hh.1] using ho w (by simp)
      · exact ih inputs (fun v hv => ho v (List.mem_cons_of_mem w hv)) hh.2 pair hp

theorem inputWeight_kernel (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ path, w.2.length = w.1.width)
    (hi : inputs.map List.length = pathWidths path) :
    inputWeight path List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (2 * (pathWidths path).sum)) *
        dyadicFourierKernel .inverse (pathWidths path).sum
          (boolWordToNat (scalarWord inputs)) (fourierWordLSB (path.map Prod.snd).flatten) := by
  have hl : inputs.length = path.length := by
    have h := congrArg List.length hi
    simpa only [List.length_map, pathWidths] using h
  have hlen : (inputs.map List.reverse).flatten.length = (pathWidths path).sum := by
    rw [flatten_length_of_widths, List.map_map]
    simpa only [Function.comp_def, List.length_reverse] using congrArg List.sum hi
  rw [inputWeight_amplitude path List.nil inputs hl,
    windowFourierAmplitude_kernel .inverse _ (inputPairs_lengths path inputs ho hi),
    inputPairs_fst path inputs hl, inputPairs_snd path inputs hl, hlen,
    ← mul_assoc, ← pow_add, show (pathWidths path).sum + (pathWidths path).sum =
      2 * (pathWidths path).sum by omega, ← scalarWord_value]

def twoInputState (root : BasisState) (left right : List (DigitWindow × List Bool))
    (P : Point) : State :=
  ((inputWords (pathWidths left)).map (fun inputsL =>
    ((inputWords (pathWidths right)).map (fun inputsR =>
      (inputWeight left List.nil inputsL * inputWeight right List.nil inputsR) •
        ket (pointWrite (pathEnd right inputsR (pathEnd left inputsL P)) root))).sum)).sum

theorem twoInputState_ideal (Q : Point) (root : BasisState)
    (left right : List (DigitWindow × List Bool)) (P : Point)
    (hol : ∀ w ∈ left, w.2.length = w.1.width)
    (hor : ∀ w ∈ right, w.2.length = w.1.width)
    (hrec : ∀ inputsL ∈ inputWords (pathWidths left),
      ∀ inputsR ∈ inputWords (pathWidths right),
      pathEnd right inputsR (pathEnd left inputsL P) =
        boolWordToNat (scalarWord inputsL) • G + boolWordToNat (scalarWord inputsR) • Q) :
    twoInputState root left right P =
      idealPointState Q root (pathWidths left).sum (pathWidths right).sum
        (left.map Prod.snd).flatten (right.map Prod.snd).flatten := by
  let n := (pathWidths left).sum
  let m := (pathWidths right).sum
  let c : ℂ := (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m))
  let f (a b : List Bool) : State :=
    (c * (c * dyadicFourierKernel .inverse n (boolWordToNat a)
      (fourierWordLSB (left.map Prod.snd).flatten) *
      dyadicFourierKernel .inverse m (boolWordToNat b)
        (fourierWordLSB (right.map Prod.snd).flatten))) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root)
  have he : twoInputState root left right P =
      ((inputWords (pathWidths left)).map (fun inputsL =>
        ((inputWords (pathWidths right)).map (fun inputsR =>
          f (scalarWord inputsL) (scalarWord inputsR))).sum)).sum := by
    unfold twoInputState
    apply congrArg List.sum
    apply List.map_congr_left
    intro inputsL hl
    apply congrArg List.sum
    apply List.map_congr_left
    intro inputsR hr
    rw [hrec inputsL hl inputsR hr, inputWeight_kernel left inputsL hol
      ((inputWords_mem _ _).mp hl), inputWeight_kernel right inputsR hor
        ((inputWords_mem _ _).mp hr)]
    unfold f c
    congr 1
    change _ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m)) * _
    rw [show 2 * (pathWidths left).sum = n + n by dsimp [n, m]; omega,
      show 2 * (pathWidths right).sum = m + m by dsimp [n, m]; omega]
    simp only [pow_add]
    ring
  rw [he]
  have hinner (a : List Bool) :
      ((inputWords (pathWidths right)).map (fun inputs => f a (scalarWord inputs))).sum =
        ((fourierOutcomes (pathWidths right).sum).map (f a)).sum :=
    scalarWords_sum _ (f a)
  simp_rw [hinner]
  rw [scalarWords_sum (pathWidths left)
    (fun a => ((fourierOutcomes (pathWidths right).sum).map (f a)).sum)]
  unfold f idealPointState
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  rfl

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/Reconstruction ====

section
/-! Mixed-radix scalar reconstruction. Offset cancellation is a group identity,
independent of the arithmetic implementation and of the Fourier outputs. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

theorem scalarWord_cons (input : List Bool) (inputs : List (List Bool)) :
    boolWordToNat (scalarWord (input :: inputs)) =
      boolWordToNat input * 2 ^ inputs.flatten.length + boolWordToNat (scalarWord inputs) := by
  rw [scalarWord_value, List.map_cons, List.flatten_cons, fourierWordMSB_append,
    fourierWordMSB_reverse, ← scalarWord_value]
  have he : (inputs.map List.reverse).flatten.length = inputs.flatten.length := by
    simp only [flatten_length_of_widths, List.map_map, Function.comp_def, List.length_reverse]
  rw [he]

def biasSum (bias : DigitWindow → Point) (path : List (DigitWindow × List Bool)) : Point :=
  (path.map (fun w => bias w.1)).sum

/-- Suffix widths determine significance; each centered digit has a fixed bias. -/
def DescendingWeights (P : Point) (bias : DigitWindow → Point) :
    List (DigitWindow × List Bool) → Prop
  | [] => True
  | (w, _) :: rest =>
      (∀ v, w.point v + bias w = (v * 2 ^ (pathWidths rest).sum) • P) ∧
        DescendingWeights P bias rest

/-- Centered digit biases cancel before any character expansion is used. -/
theorem pathEnd_reconstruct (P : Point) (bias : DigitWindow → Point)
    (path : List (DigitWindow × List Bool)) (hw : DescendingWeights P bias path)
    (inputs : List (List Bool)) (hi : inputs.map List.length = pathWidths path) (A : Point) :
    pathEnd path inputs A + biasSum bias path =
      A + boolWordToNat (scalarWord inputs) • P := by
  induction path generalizing inputs A with
  | nil =>
    have hn : inputs = [] := by simpa only [pathWidths, List.map_nil, List.map_eq_nil_iff] using hi
    subst inputs
    simp [pathEnd, biasSum, scalarWord]
  | cons w path ih =>
    cases inputs with
    | nil => simp [pathWidths] at hi
    | cons input inputs =>
      have hh : input.length = w.1.width ∧ inputs.map List.length = pathWidths path := by
        simpa only [List.map_cons, pathWidths, List.cons.injEq] using hi
      have hsuf : inputs.flatten.length = (pathWidths path).sum := by
        rw [flatten_length_of_widths, hh.2]
      have ht := ih hw.2 inputs hh.2 (A + w.1.point (boolWordToNat input))
      change pathEnd path inputs (A + w.1.point (boolWordToNat input)) +
        (bias w.1 + biasSum bias path) = A + boolWordToNat (scalarWord (input :: inputs)) • P
      rw [scalarWord_cons, hsuf, add_nsmul]
      calc
        _ = (pathEnd path inputs (A + w.1.point (boolWordToNat input)) +
            biasSum bias path) + bias w.1 := by abel
        _ = (A + w.1.point (boolWordToNat input) + boolWordToNat (scalarWord inputs) • P) +
            bias w.1 := by rw [ht]
        _ = A + (w.1.point (boolWordToNat input) + bias w.1) +
            boolWordToNat (scalarWord inputs) • P := by abel
        _ = _ := by rw [hw.1]; abel

theorem two_axes_reconstruct (Q : Point)
    (biasL biasR : DigitWindow → Point) (left right : List (DigitWindow × List Bool))
    (hwL : DescendingWeights G biasL left) (hwR : DescendingWeights Q biasR right)
    (A : Point) (hA : A = biasSum biasL left + biasSum biasR right)
    (inputsL : List (List Bool)) (inputsR : List (List Bool))
    (hiL : inputsL.map List.length = pathWidths left)
    (hiR : inputsR.map List.length = pathWidths right) :
    pathEnd right inputsR (pathEnd left inputsL A) =
      boolWordToNat (scalarWord inputsL) • G + boolWordToNat (scalarWord inputsR) • Q := by
  have hl := pathEnd_reconstruct G biasL left hwL inputsL hiL A
  have hr := pathEnd_reconstruct Q biasR right hwR inputsR hiR (pathEnd left inputsL A)
  rw [eq_sub_iff_add_eq.mpr hr, eq_sub_iff_add_eq.mpr hl, hA]
  abel

/-- A compositional version of the full-state identity, with only per-digit
weights and fixed offset cancellation as arithmetic premises. -/
theorem twoInputState_ideal_of_weights (Q : Point) (root : BasisState)
    (left right : List (DigitWindow × List Bool)) (A : Point)
    (hol : ∀ w ∈ left, w.2.length = w.1.width)
    (hor : ∀ w ∈ right, w.2.length = w.1.width)
    (biasL biasR : DigitWindow → Point)
    (hwL : DescendingWeights G biasL left) (hwR : DescendingWeights Q biasR right)
    (hA : A = biasSum biasL left + biasSum biasR right) :
    twoInputState root left right A =
      idealPointState Q root (pathWidths left).sum (pathWidths right).sum
        (left.map Prod.snd).flatten (right.map Prod.snd).flatten := by
  apply twoInputState_ideal Q root left right A hol hor
  intro inputsL hl inputsR hr
  exact two_axes_reconstruct Q biasL biasR left right hwL hwR A hA inputsL inputsR
    ((inputWords_mem _ _).mp hl) ((inputWords_mem _ _).mp hr)

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/Paths ====

section
/-! Output-path expansion for arbitrary window banks, preserving the complete
linear branch before taking its Born mass. Apache-2.0 Streaming proof pattern;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] fourierOutcomes

def outputPaths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool} :
    List (WindowModel read) → List (List (WindowModel read × List Bool))
  | List.nil => [[]]
  | w :: ws => (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
      (outputPaths ws).map (fun path => (w, bits) :: path))

def modelBranch {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool} :
    List (WindowModel read × List Bool) → List Bool → State →ₗ[ℂ] State
  | List.nil, _ => LinearMap.id
  | (w, bits) :: ws, prior =>
      (modelBranch ws (bits.reverse ++ prior)).comp (w.step prior bits)

theorem idealAxis_paths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (prior : List Bool) (terminal : List Bool → Instrument) :
    idealAxis ws prior terminal =
      (outputPaths ws).flatMap (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).map (fun b =>
          ({history := (path.map Prod.snd).flatten, kraus := modelBranch path prior} : InstrumentBranch).seq b)) := by
  induction ws generalizing prior with
  | nil =>
    simp only [idealAxis, outputPaths, List.flatMap_cons, List.flatMap_nil, List.map_nil,
      List.flatten_nil, List.reverse_nil, List.nil_append, List.append_nil, modelBranch]
    exact (List.map_id' _).symm
  | cons w ws ih =>
    simp only [idealAxis, outputPaths, ih, List.map_flatMap, List.flatMap_map,
      List.flatMap_assoc, List.map_map, Function.comp_def, List.map_cons,
      List.flatten_cons, List.reverse_append, List.append_assoc, modelBranch]
    apply List.flatMap_congr
    intro bits hb
    apply List.flatMap_congr
    intro path hp
    apply List.map_congr_left
    intro b hbt
    cases b
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem idealAxis_paths_mass {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (prior : List Bool) (terminal : List Bool → Instrument)
    (ψ : State) :
    (idealAxis ws prior terminal).bornMass ψ =
      ((outputPaths ws).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (modelBranch path prior ψ))).sum := by
  rw [idealAxis_paths]
  simp only [flat_mass, prefixed_mass]

theorem outputPaths_zip {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) :
    outputPaths ws = (inputWords (ws.map (fun w => w.physical.wires.length))).map (ws.zip ·) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [outputPaths, List.map_cons, inputWords, List.map_flatMap,
      List.map_map, Function.comp_def, List.zip_cons_cons, ih]

def logicalPath {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (logical : WindowModel read → DigitWindow) (path : List (WindowModel read × List Bool)) :
    List (DigitWindow × List Bool) := path.map (fun w => (logical w.1, w.2))

theorem modelBranch_point {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (logical : WindowModel read → DigitWindow) (root : BasisState)
    (path : List (WindowModel read × List Bool))
    (hrule : ∀ w ∈ path, ∀ prior P,
      w.1.step prior w.2 (ket (pointWrite P root)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (logical w.1).width) •
          ((fourierOutcomes (logical w.1).width).map (fun input =>
            fourierBitAmplitude .inverse input.reverse prior w.2 •
              ket (pointWrite (P + (logical w.1).point (boolWordToNat input)) root))).sum)
    (prior : List Bool) (P : Point) :
    modelBranch path prior (ket (pointWrite P root)) =
      pointKernel root (logicalPath logical path) prior P := by
  induction path generalizing prior P with
  | nil => rfl
  | cons w path ih =>
    simp only [modelBranch, LinearMap.comp_apply]
    rw [hrule w (by simp)]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def]
    simp_rw [ih (fun v hv => hrule v (List.mem_cons_of_mem w hv))]
    rfl

def modelDigit {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (w : WindowModel read) : DigitWindow := ⟨w.physical.wires.length, w.point, w.bias⟩

def PointRule {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (root : BasisState) (w : WindowModel read) : Prop :=
  ∀ prior bits P, w.step prior bits (ket (pointWrite P root)) =
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.physical.wires.length) •
      ((fourierOutcomes w.physical.wires.length).map (fun input =>
        fourierBitAmplitude .inverse input.reverse prior bits •
          ket (pointWrite (P + w.point (boolWordToNat input)) root))).sum

theorem outputPath_models {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) : path.map Prod.fst = ws := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := List.mem_singleton.mp hp
    subst path
    rfl
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    simp only [List.map_cons, ih rest hr]

theorem outputPath_lengths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    ∀ w ∈ logicalPath modelDigit path, w.2.length = w.1.width := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := by simpa only [outputPaths, List.mem_singleton] using hp
    subst path
    simp [logicalPath]
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    intro v hv
    simp only [logicalPath, List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (fourierOutcomes_mem _ _).mp hb
    · exact ih rest hr v hv

def ModelWeights {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (P : Point) : List (WindowModel read) → Prop
  | List.nil => True
  | w :: ws =>
      (∀ v, w.point v + w.bias =
        (v * 2 ^ (ws.map (fun w => w.physical.wires.length)).sum) • P) ∧ ModelWeights P ws

theorem outputPath_widths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    pathWidths (logicalPath modelDigit path) = ws.map (fun w => w.physical.wires.length) := by
  have he := congrArg (List.map (fun w : WindowModel read => w.physical.wires.length))
    (outputPath_models ws path hp)
  simpa only [pathWidths, logicalPath, modelDigit, List.map_map, Function.comp_def] using he

theorem outputPath_bias {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    biasSum DigitWindow.bias (logicalPath modelDigit path) = (ws.map WindowModel.bias).sum := by
  have he := congrArg (fun ms : List (WindowModel read) => (ms.map WindowModel.bias).sum)
    (outputPath_models ws path hp)
  simpa only [biasSum, logicalPath, modelDigit, List.map_map, Function.comp_def] using he

theorem outputPath_weights {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (P : Point) (ws : List (WindowModel read)) (hw : ModelWeights P ws)
    (path : List (WindowModel read × List Bool)) (hp : path ∈ outputPaths ws) :
    DescendingWeights P DigitWindow.bias (logicalPath modelDigit path) := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := List.mem_singleton.mp hp
    subst path
    trivial
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    constructor
    · change ∀ v, w.point v + w.bias =
        (v * 2 ^ (pathWidths (logicalPath modelDigit rest)).sum) • P
      rw [outputPath_widths ws rest hr]
      exact hw.1
    · exact ih hw.2 rest hr

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/EventMass ====

section
/-! Selected-event distribution for arbitrary window banks and a terminal reset
that preserves Born mass. Apache-2.0 Streaming proof pattern; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section

def precision {n : Nat} {read : ConstantBit n → Bool} (ws : List (WindowModel read)) : Nat :=
  (ws.map (fun w => w.physical.wires.length)).sum

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/WindowKernel ====

section
/-! Coherent mixed-width window sums. Adapted from the Apache-2.0 Streaming
window proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
attribute [local irreducible] fourierOutcomes

end
end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Support ====

section
/-! Finite-support facts adapted from the Apache-2.0 Streaming validity proofs;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Support
open Quantum
noncomputable section

theorem add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ + φ) := by
  intro s hs
  by_cases h : ψ s = 0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h

theorem smul {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

theorem list_sum {A : Type} {V : BasisState → Prop} (xs : List A) (f : A → State)
    (hf : ∀ a ∈ xs, SupportedOn V (f a)) : SupportedOn V (xs.map f).sum := by
  induction xs with
  | nil => exact supportedOn_zero V
  | cons a xs ih =>
    exact add (hf a (by simp)) (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

theorem linear (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s = 0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz, hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u = s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [map_add, he, map_smul]
    exact add (smul c (hL s hvs)) (ih hvψ)

end
end ShorECDLP.Entrant.Single.Support

end

-- ==== part: Single/WindowModels ====

section
/-! Instantiate history-aware refinement using only the mixed-window contract.
Concrete bodies may later discharge that contract without changing this proof. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

/-- Coherent superpositions of valid point encodings with a fixed clean frame. -/
def pointFamily (root : BasisState) (s : BasisState) : Prop :=
  ∃ P : Point, s = pointWrite P root

end
end ShorECDLP.Entrant.Single.Distribution

end


/-! EDITABLE. Single-trial entrant: concrete single-trial success.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Distribution ====

section
/-! Distribution proof entry point for the mixed-width single-trial construction. -/

end

-- ==== part: Single/Scalar ====

section
namespace ShorECDLP.Entrant.Single
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Setup ====

section
/-! The complete distribution theorem is parameterized by coherent physical
windows. Counts and Fourier order are explicit interface obligations. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option pp.maxSteps 60

structure Setup {n : Nat} (coeffs : Fin n → PointCoeff) where
  first : Window n
  signed : SignedWindow → Window n
  firstLaw : WindowLaw coeffs first firstUpdate FirstWindowInput
  signedLaw : SignedWindowLaw coeffs signed
  firstWires : first.wires = (bank 16).reverse
  signedWires : ∀ w, (signed w).wires = (bank w.width).reverse
  firstCount : first.count = 65535
  signedCount : ∀ w, (signed w).count = b.records

def initialRoot : BasisState := zeroBasisState[836 ↦ true]

theorem initialRoot_input : FirstWindowInput initialRoot := firstWindowInput_start

theorem initialRoot_clean : Clean streamAddress initialRoot := by
  intro v hv
  have he := (show ∀ v ∈ streamAddress, v ≠ 836 by decide +kernel) v hv
  simp only [initialRoot, upd, if_neg he, zeroBasisState]

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/ConcreteDistribution ====

section
/-! Connect the distribution theorem to the real coherent bodies. Fourier
metadata is most-significant-first; lookup addresses remain little-endian. -/
namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option pp.maxSteps 60

def terminalInstrument : Instrument :=
  (AdaptiveCircuit.unitary [.X 836]
    (measureResetWithCorrection b.reset (fun _ => List.nil))).run

theorem terminalInstrument_mass (ψ : State) : terminalInstrument.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection b.reset (fun _ => List.nil)).run.bornMass
        (Quantum.run [.X 836] ψ) := by
      simp only [terminalInstrument, AdaptiveCircuit.run, Instrument.bornMass,
        List.map_map, Function.comp_def]
      rfl
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ


theorem prefix_filter_mass (I : Instrument) (gs : Circuit) (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((I.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b)).filter
        (fun b => accept b.history)) ψ =
      Instrument.bornMass (I.filter (fun b => accept b.history)) (Quantum.run gs ψ) := by
  rw [List.filter_map]
  simp only [Function.comp_def, InstrumentBranch.seq, List.nil_append, Instrument.bornMass,
    List.map_map, LinearMap.comp_apply]

theorem append_run_fixed_right {n start a b finish : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ h, (r.instantiate read h).run = target.run) :
    ((p.append (q.append r)).instantiate read history).run =
      ((p.append q).instantiate read history).run.seq target.run := by
  rw [append_run_history]
  simp_rw [append_run_fixed q r read _ target hr, AdaptiveCircuit.run_seq]
  rw [append_run_history]
  simp only [Instrument.seq, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro x hx
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro z hz
  rcases x with ⟨xh, xk⟩
  rcases y with ⟨yh, yk⟩
  rcases z with ⟨zh, zk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem straight_gate_run {n start finish : Nat} (g : TemplateGate n) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((Straight.gate g p).instantiate read history).run =
      ((p.instantiate read history).run).map (fun b =>
        ({history := List.nil, kraus := Quantum.run (g.instantiate read)} : InstrumentBranch).seq b) := rfl

attribute [local irreducible] axis resetProgram

theorem unitary_run_map (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b) := rfl

theorem framed_reset_run {n start a b finish out : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish) (h : finish = out)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ history, (r.instantiate read history).run = target.run) :
    ((framed p q r h).instantiate read history).run =
      (((p.append q).instantiate read history).run.seq (AdaptiveCircuit.unitary [.X 836] target).run).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  have ht : ∀ history, ((Straight.gate (.literal (.X 836)) r).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836] target).run := by
    intro history
    rw [straight_gate_run, hr history, unitary_run_map]
    rfl
  rw [framed_run, unitary_run_map, append_run_fixed_right _ _ _ _ _ _ ht]

end
end ShorECDLP.Entrant.Single.Distribution

end

namespace ShorECDLP.Entrant.Single.Distribution
variable [b : WindowBody] [ledger : ProducerResources b]
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section

end
end ShorECDLP.Entrant.Single.Distribution

-- ==== bundle: Single/Readout ====

set_option linter.unusedSectionVars false

/-! EDITABLE. Single-trial entrant: protected certificate assembly.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Certificate ====

section
/-! Single-trial certificate for the 263/263-bit protected nearest-pair decoder.
The fixed-table packaging follows the Apache-2.0 VerifiedQC Streaming certificate
(PR #551), for the construction of arXiv:2607.13816v2. See LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
variable [body : WindowBody] [ledger : ProducerResources body]
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

theorem positiveWords_support (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((positiveWords n steps start width c).instantiate read history).wires⊆[0,1]
  | 0,_,_,_,_,_=>by simp [positiveWords,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.wires]
  | steps+1,start,width,c,read,history=>by
    rw [positiveWords,castFinish_instantiate]
    exact outer_append_support _ _ read history ([0,1] : List Wire) (incrementStep_support _ _ _ _)
      (fun h=>positiveWords_support n steps _ _ _ read h)

theorem negativeStep_support (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((negativeStep n c).instantiate read history).wires⊆[0,1] := by
  rw [negativeStep,castFinish_instantiate]
  exact outer_append_support _ _ read history ([0,1] : List Wire) (incrementStep_support _ _ _ _)
    (fun h=>complementStep_support n c.next read h)

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

/--55 candidate words from one sample: center,27 positive shifts,27 negative shifts.
The arithmetic is carried out by explicit permitted record-controlled Clifford gates. -/
def neighborSuffix (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start+2+164*width) :=
  let c:=initialCursor bits
  let q:=c.lift (27*(2*width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 27 (start+2) width c).append
        ((complementStep n q).append
          (negativeWords n 27 (start+2+27*(2*width)+2*width) width q.next))))

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

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
    (i+b)%2^208=(((b : ℤ)+(i : ℤ))%(2^208 : Nat)).toNat := by
  simp only [←Int.natCast_add,←Int.natCast_mod,Int.toNat_natCast,Nat.add_comm]

theorem negative_word_mod (b i : Nat) (hb : b<2^208) :
    2^208-1-((i+(2^208-1-b))%2^208)=(((b : ℤ)-(i : ℤ))%(2^208 : Nat)).toNat := by
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

end
end ShorECDLP.Entrant.NeighborReadout

-- ==== bundle: Single/Producer ====

set_option linter.unusedSectionVars false

namespace ShorECDLP.Entrant.Rounded
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open RoundedReadout
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def finePositions : List (Fin (65535 + 29 * body.records + 474 + body.reset.length)) :=
  Single.trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(Single.right_position_bound i.val i.property).2.trans_le (by omega)⟩
theorem finePositions_length : finePositions.length=208 := by
  simp [finePositions,Single.params]
def fineBits : Vector (Fin (65535 + 29 * body.records + 474 + body.reset.length)) 208 := Vector.ofFn fun i=>
  finePositions[i.val]'(by rw [finePositions_length];exact i.isLt)

def readout : Straight 917504 (65535 + 29 * body.records + 474 + body.reset.length) (65535 + 29 * body.records + 474 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 917504 (65535 + 29 * body.records + 474 + body.reset.length) 208 fineBits)

attribute [local irreducible] readout Straight.instantiate Straight.WellFormed Straight.gateSlots
  AdaptiveCircuit.tCount AdaptiveCircuit.wires AdaptiveCircuit.measurementCount AdaptiveCircuit.run

def program : Straight 917504 0 (65535 + 29 * body.records + 474 + body.reset.length + 34114) := Single.program.append readout

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

def entry : StraightEntry := Single.fixedEntry Single.mixedCoefficientAt program

end
end ShorECDLP.Entrant.Rounded

namespace ShorECDLP.Entrant.Single
open ShorECDLP.Challenge
variable [body : WindowBody] [ledger : ProducerResources body]

end ShorECDLP.Entrant.Single

-- ==== bundle: Single/EEA ====

section


/-! Exact cancellation of reversible gates across commuting classical operations.
The rewrite preserves the full quantum operator, including on nonzero workspace. -/
namespace ShorECDLP.Entrant.Cancellation
open Quantum
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

end ShorECDLP.Entrant.Cancellation

namespace ShorECDLP.Entrant.Cancellation
open Paper2607_13816

private instance gateWellFormedDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

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

/-- A program together with the exact proof needed to replace a fixed source context. -/
structure Patch {n s e : Nat} (source : Straight n s e) (saving : Nat) where
  program : Straight n s e
  drops : Drops source program saving
  rewrites : Rewrites source program

namespace Patch
noncomputable section

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
  measuredInverseStepProgram measuredEEAReverseProgram measuredReverseWrapperProgram
  hInverseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplicationProgram
  multiplicationAfterResetProgram multiplicationCorrectionProgram multiplicationCleanupProgram
  multiplyDataProgram unmultiplyDataProgram divisionCorrectionProgram collectProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram


set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

end
end ShorECDLP.Entrant.Optimization
namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  Single.axis Rounded.entry

end
end ShorECDLP.Entrant.Optimization
end

namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration


end ShorECDLP.Entrant.Single

end

-- Assembly bundle: committed WEX body 776a74c
section
/-! Consolidated module: WEX. -/

/-! Consolidated development: ECDSALib. -/
-- Adapted from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; proofs follow its finite-addend frontier modules at c3f340a. Changes: recovery stage, table template, names.

/-! # ECDSALib: the ecdsa.fail finite-addend circuit as a table template

One module (the kernel replay loads every Entrant module's whole import closure in its own task,
so the Entrant keeps few modules). Sections, in order:

1. `recoveryStageS`, `genericS`, `finiteS`: B's frontier finite-addend program with the recovery
   constant `cx` added as `cx` then the literal `1`, and `-cy` read from a table field.
2. `finiteS_spec`, `finiteS_full_spec`, `finiteS_counts`, `finiteS_physical`,
   `finiteS_gateSlots_le`, `finiteS_supportQ`.
3. `TInstr`/`Tmpl`, the field-reading leaves, `finiteT L row rowD`, `finiteT_inst`.
4. Structural enables for multiples of `G`; `finiteT_spec`, `finiteT_counts`, `finiteT_supportQ`,
   `finiteT_physical`, `finiteT_gateSlots_le`, `finiteT_clifford`, `finiteT_encodes`,
   `finiteT_qubits_le`.
-/

/-! ---------------------------------------------------------------------------
(formerly `ECDSALib/Program.lean`) -/

/-! # The ecdsa.fail finite-addend program with a field-readable recovery constant

Adapted from `ECDSAAdd/Submission/Entrant/Program.lean`, `QProgram.lean` and
`ECDSAAdd/Arithmetic/{PointRecoveryStage,CompressedPointDialogSteps,
CompressedPointDialogResources,SkywalkPointPhysical}.lean` and `Baselines/SkywalkSlots.lean`
(ECDSAAdd, Apache-2.0).

The only change to the frontier program is in the recovery stage: the controlled canonical
addition of the constant `cx + 1` (not a protected table field) becomes an addition of `cx`
followed by an addition of the literal `1`. Every other block is unchanged, so every constant
the program reads is a bit of `x`, `y`, `negX`, `negY`, `tripleX` (or a doubling field) of
the addend. Cost: one extra controlled constant adder, +1023 Toffoli and +1023 measurements. -/
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.ShorPort
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed Entrant

/-! ## Programs -/

/-- Reflection, add `cx`, add `1`, add `-cy` (the frontier adds `cx+1` in one step). -/
def recoveryStageS (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointRecoveryReflection L ++ pointDialogConstantAdd L L.point.x cx ++
    pointDialogConstantAdd L L.point.x 1 ++ pointDialogConstantAdd L L.point.y (-cy)

/-- `pointCompressedDialogGeneric` with `recoveryStageS`. -/
def genericS (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  pointCompressedArithmetic L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  pointCompressedArithmetic L true ++
  recoveryStageS L cx cy

/-- The frontier `finiteProgram` with `genericS` in place of `pointCompressedDialogGeneric`. -/
def finiteS (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  shortEqual L L.core.equalX L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ genericS L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  shortEqual L L.core.double L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

/-! ## Recovery stage -/

theorem recoveryStageS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (recoveryStageS L cx cy)
      (PointDialogValues L (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have a := pointRecoveryReflection_step L hw hn X Y G base
  have b := dialogStep_addX L hw hn (if G then -1-X else X) Y G base cx
  have c := dialogStep_addX L hw hn ((if G then -1-X else X)+(if G then cx else 0)) Y G base 1
  have d := dialogStep_addY L hw hn
    ((if G then -1-X else X)+(if G then cx else 0)+(if G then 1 else 0)) Y G base (-cy)
  have all := ((a.seq b).seq c).seq d
  have x : (if G then -1-X else X)+(if G then cx else 0)+(if G then 1 else 0)=
      (if G then cx-X else X) := by
    cases G
    · simp
    · rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl]; ring
  have y : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by
    cases G <;> simp [sub_eq_add_neg]
  rw [x,y] at all
  exact all

theorem recoveryStageS_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (recoveryStageS L cx cy)=3324 ∧ measurementCount (recoveryStageS L cx cy)=3324 := by
  have neg := pointRecoveryReflection_counts L hw
  have x := pointRecoveryConstantAdd_counts L hw L.point.x (Or.inl rfl) cx
  have x1 := pointRecoveryConstantAdd_counts L hw L.point.x (Or.inl rfl) 1
  have y := pointRecoveryConstantAdd_counts L hw L.point.y (Or.inr rfl) (-cy)
  simp only [recoveryStageS,pointDialogConstantAdd,toffoliCount_append,
    measurementCount_append,neg.1,neg.2,x.1,x.2,x1.1,x1.2,y.1,y.2]
  decide

theorem recoveryStageS_support (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (recoveryStageS L cx cy)⊆L.recoveryStageSites.toFinset := by
  have neg := pointRecoveryReflection_support L hw
  have x := pointRecoveryConstantAdd_support L hw L.point.x cx
  have x1 := pointRecoveryConstantAdd_support L hw L.point.x 1
  have y := pointRecoveryConstantAdd_support L hw L.point.y (-cy)
  have small : L.dialogPool.take 258⊆L.dialogPool.take 515 := by
    intro q hq
    have eq : (L.dialogPool.take 515).take 258=L.dialogPool.take 258 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←eq] at hq
    exact List.mem_of_mem_take hq
  have en : (L.core.generic::L.point.x++L.dialogPool.take 258).toFinset⊆
      L.recoveryStageSites.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    have ht : q∈L.dialogPool.take 258 → q∈L.dialogPool.take 515 := fun h => small h
    tauto
  have ex : (L.core.generic::L.point.x++L.dialogPool.take 515).toFinset⊆
      L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  have ey : (L.core.generic::L.point.y++L.dialogPool.take 515).toFinset⊆
      L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  simpa only [recoveryStageS,pointDialogConstantAdd,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (neg.trans en) (x.trans ex)) (x1.trans ex)) (y.trans ey)

theorem recoveryStageS_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (recoveryStageS L cx cy) := by
  simp only [recoveryStageS,gatePhysical_append]
  exact ⟨⟨⟨CompactRecoveryNegateLayout.reflection_physical _ _ _ (L.recoveryNegate_nodup hw hn),
    pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _⟩,
    pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _⟩,
    pointDialogConstantAdd_physical L hw hn _ (Or.inr rfl) _⟩

theorem recoveryStageS_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Challenge.gateSlots (recoveryStageS L cx cy) ≤ 58608 := by
  have hr := Baselines.recoveryReflection_gateSlots_le L hw
  have hx := Baselines.recoveryConstant_gateSlots_le L hw L.point.x hw.inputX cx
  have hx1 := Baselines.recoveryConstant_gateSlots_le L hw L.point.x hw.inputX 1
  have hy := Baselines.recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  simp only [recoveryStageS, Challenge.gateSlots_append]; omega

/-! ## Generic branch -/

section Generic
open CompressedPointDialog
attribute [local irreducible] run pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointMeasuredSquareCandidate

end Generic

section GenericResources
open CompressedPointDialog
attribute [local irreducible] wires pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointRecoveryConstantAdd pointRecoveryReflection compactRecoveryConstant
  CompactRecoveryNegateLayout.reflection

theorem genericS_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (genericS L cx cy)⊆(sites L).toFinset := by
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
  have recover := recoveryStageS_support L hw cx cy
  have recovery : wires (recoveryStageS L cx cy)⊆(sites L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (recover hq)
    have p := prefix_small L hw 515 (Nat.le_refl 515)
    simp only [recoveryStageSites,List.mem_append] at h
    simp only [sites,CompressedPointSquare.residents,List.mem_toFinset,List.mem_append]
    tauto
  simpa only [genericS,wires_append,Finset.union_subset_iff,sites] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recovery

theorem genericS_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    toffoliCount (genericS L cx cy)=2214305 ∧ measurementCount (genericS L cx cy)=1554847 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have arith := pointCompressedArithmetic_counts L
  have square := CompressedPointSquare.counts L hw
  have recovery := recoveryStageS_counts L hw cx cy
  simp only [genericS,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2,recovery.1,recovery.2]
  norm_num

end GenericResources

theorem genericS_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (genericS L cx cy) := by
  have ax (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.x (Or.inl rfl) k
  have ay (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.y (Or.inr rfl) k
  have di := pointCompressedArithmetic_physical L hw hn false
  have mu := pointCompressedArithmetic_physical L hw hn true
  have sq := CompressedPointSquare.computableProgram_physical L hw hn
  have recovery := recoveryStageS_physical L hw hn cx cy
  simp only [genericS,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,ax _⟩,mu⟩,recovery⟩

end ECDSAAdd.ShorPort

end

/-! ---------------------------------------------------------------------------
(formerly `ECDSALib/Finite.lean`) -/

/-! # Specification and resources of `finiteS`

Adapted from `ECDSAAdd/Submission/Entrant/{Program,QProgram,Main}.lean` (ECDSAAdd, Apache-2.0):
the same proofs with `genericS` in place of the frontier generic branch. -/
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.ShorPort
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog MappedCompressed Entrant

section Spec
attribute [local irreducible] run wires shortEqual pairEqual genericS
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

end Spec

section Support
attribute [local irreducible] wires pointCompressedDialogGeneric genericS

theorem finiteS_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) :
    wires (finiteS L C cx cy) ⊆ (CompressedPointDialog.sites L).toFinset := by
  have h := CompressedPointDialog.finite_support L hw hn C cx cy
  simp only [pointCompressedDialogFinite, wires_append, Finset.union_subset_iff] at h
  have hG := genericS_support L hw hn cx cy
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
  simp only [finiteS, wires_append, Finset.union_subset_iff]
  have r (A B : Program) (hAB : wires A ⊆ wires B) :
      wires B ⊆ (CompressedPointDialog.sites L).toFinset →
        wires A ⊆ (CompressedPointDialog.sites L).toFinset := fun h' => hAB.trans h'
  have r3 := r _ _ q3
  have r5 := r _ _ q5
  clear r q3 q5
  tauto

theorem finiteS_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : wires (finiteS L C cx cy) ⊆ L.dialogUsedWires.toFinset :=
  (finiteS_support L hw hn C cx cy).trans (sites_used L hw)

end Support

section Frame
attribute [local irreducible] run wires

end Frame

section Counts

theorem pairEqual_toffoli (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (e₁ e₂ : Bool) (C D : Point) :
    toffoliCount (pairEqual L t₁ t₂ e₁ e₂ C D) = 257 + e₁.toNat + e₂.toNat := by
  have h := zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (e₁.toNat + e₂.toNat)
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)
  rw [pairPorts_length L hw] at h
  have x := xorConstant_counts (pairSrc L) (pairCode C)
  simp only [pairEqual, toffoliCount_append, x.1, h.1]
  omega

/-- Exact counts when both pair enables hold (they do for every finite `C` in the prime-order
group, see `Structural.lean`). -/
theorem finiteS_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) (h₁ : decide (cy≠-cy) = true) (h₂ : exceptionBit C = true) :
    toffoliCount (finiteS L C cx cy)=2215341 ∧ measurementCount (finiteS L C cx cy)=1555877 := by
  have hg := genericS_counts L hw hn cx cy
  have s5 := shortEqual_counts L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
  have s7 := shortEqual_counts L hw L.core.double L.doubleSelect (C+C)
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have t1 : toffoliCount
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)) = 259 := by
    simp only [pairEqual_toffoli L hw, h₁, Bool.toNat_true]
  have t2 : toffoliCount
      (pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)) = 259 := by
    simp only [pairEqual_toffoli L hw, h₂, Bool.toNat_true]
  have z1 := zeroFlag_counts L.point.finite L.control L.infinitySelect
  have z2 := zeroFlag_counts L.point.finite L.control L.genericSelect
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  have hf : toffoliCount (pointDialogGenericFlag L)=0 ∧
      measurementCount (pointDialogGenericFlag L)=0 := by
    simp [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]
  have hc : toffoliCount (pointDialogCorners L C)=0 ∧ measurementCount (pointDialogCorners L C)=0 := by
    simp only [pointDialogCorners,pointInPlaceCorners,toffoliCount_append,measurementCount_append,
      (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2]
    simp
  simp only [finiteS, toffoliCount_append, measurementCount_append]
  omega

end Counts

section Physical
open MappedCompressed

theorem finiteS_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (finiteS L C cx cy) := by
  have orig := skywalkFinite_physical L hw hn C cx cy
  simp only [pointCompressedDialogFinite, gatePhysical_append] at orig
  have ge := genericS_physical L hw hn cx cy
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
  simp only [finiteS, gatePhysical_append]
  tauto

end Physical

section Slots
open Challenge MappedCompressed Baselines

end Slots

/-! ## Support inside the 1898-site inventory `sitesQ` (pool site 1801 unused) -/

section SupportQ
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
  pointCompressedDialogGeneric genericS shortEqual pairEqual

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

end SupportQ

end ECDSAAdd.ShorPort

end

/-! ---------------------------------------------------------------------------
(formerly `ECDSALib/Template.lean`) -/

/-! # The C-dependent template of `finiteS`

In the ShorECDLP challenge the classical addend `C` (a coefficient-table point) may enter the
circuit only as gates switched by one bit of one protected field of a table row. This module
gives a template instruction type over the ECDSAAdd instruction set,

* `TInstr.lit i`: the fixed instruction `i`;
* `TInstr.gated ref v i`: `i`, present exactly when bit `ref` of the table equals `v`,

and the template `finiteT L row rowD` whose instantiation with any reader that returns the
protected fields of `C` on row `row` and of `C + C` on row `rowD` is exactly
`finiteS L C cx cy` (for a finite `C = (cx, cy)` with the two structural enables, which hold
for every finite multiple of the generator, see `Structural.lean`).

Field use (row `row` holds `C`, row `rowD` holds `C + C`):
`infinity`, `x`, `y`, `negX`, `negY`, `tripleX`, `doubleInfinity`, `doubleX`, `doubleY` of
`row`, and `negY` of `rowD` (the ordinate of `-(C+C)`, which is not a field of `row`).
Only `X` and `CX` gates are ever gated. -/
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace ECDSAAdd.ShorPort
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed Entrant

abbrev CBit (n : Nat) := ShorECDLP.Challenge.ConstantBit n
abbrev Field := ShorECDLP.Challenge.PointField

/-! ## Template instructions -/

/-- A fixed instruction, or one present exactly when one table bit equals `value`. -/
inductive TInstr (n : Nat) where
  | lit (i : Instr)
  | gated (ref : CBit n) (value : Bool) (i : Instr)

namespace TInstr
variable {n : Nat}

def instantiate (read : CBit n → Bool) : TInstr n → Program
  | .lit i => [i]
  | .gated r v i => if read r = v then [i] else []

def map (f : Instr → Instr) : TInstr n → TInstr n
  | .lit i => .lit (f i)
  | .gated r v i => .gated r v (f i)

end TInstr

abbrev Tmpl (n : Nat) := List (TInstr n)

namespace Tmpl
variable {n : Nat}

def instantiate (read : CBit n → Bool) (t : Tmpl n) : Program :=
  t.flatMap (TInstr.instantiate read)

/-- A fixed program as a template. -/
def lit (p : Program) : Tmpl n := p.map TInstr.lit

def map (f : Instr → Instr) (t : Tmpl n) : Tmpl n := List.map (TInstr.map f) t

@[simp] theorem instantiate_nil (read : CBit n → Bool) : instantiate read ([] : Tmpl n) = [] := rfl

@[simp] theorem instantiate_cons (read : CBit n → Bool) (g : TInstr n) (t : Tmpl n) :
    instantiate read (g :: t) = g.instantiate read ++ instantiate read t := rfl

@[simp] theorem instantiate_append (read : CBit n → Bool) (s t : Tmpl n) :
    instantiate read (s ++ t) = instantiate read s ++ instantiate read t := by
  simp [instantiate, List.flatMap_append]

@[simp] theorem instantiate_lit (read : CBit n → Bool) (p : Program) :
    instantiate read (lit p : Tmpl n) = p := by
  induction p with
  | nil => rfl
  | cons i p ih => exact congrArg (List.cons i) ih

theorem _root_.ECDSAAdd.ShorPort.TInstr.instantiate_map (read : CBit n → Bool)
    (f : Instr → Instr) (g : TInstr n) :
    (TInstr.map f g).instantiate read = (g.instantiate read).map f := by
  cases g with
  | lit i => rfl
  | gated r v i =>
    by_cases h : read r = v <;> simp [TInstr.map, TInstr.instantiate, h]

theorem instantiate_map (read : CBit n → Bool) (f : Instr → Instr) (t : Tmpl n) :
    instantiate read (map f t) = (instantiate read t).map f := by
  induction t with
  | nil => rfl
  | cons g t ih =>
    show (TInstr.map f g).instantiate read ++ instantiate read (map f t) =
      ((g.instantiate read) ++ instantiate read t).map f
    rw [List.map_append, ih, TInstr.instantiate_map]

/-- Normalization (`CCX a a t ↦ CX a t`, `CZ a a ↦ Z a`) commutes with instantiation. -/
theorem instantiate_normalize (read : CBit n → Bool) (t : Tmpl n) :
    instantiate read (map Baselines.normalizeInstr t) =
      Baselines.normalizeProgram (instantiate read t) :=
  instantiate_map read _ t

end Tmpl

/-! ## Reading table fields -/

/-- A finite point of the vendored curve as a point of the ShorECDLP curve (the two curve
definitions are identical, so this is the identity up to unfolding). -/
def toA (P : Point) : ShorECDLP.Secp256k1.Point := P

/-- Bit `i` (taken mod 256) of field `f` of table row `row`. -/
def bitRef {n : Nat} (row : Fin n) (f : Field) (i : Nat) : CBit n :=
  ⟨row, f, ⟨i % 256, Nat.mod_lt _ (by decide)⟩⟩

/-- `read` returns the protected fields of `P` on table row `row`. -/
def RowReads {n : Nat} (read : CBit n → Bool) (row : Fin n) (P : Point) : Prop :=
  ∀ (f : Field) (b : Fin 256),
    read ⟨row, f, b⟩ = (ShorECDLP.Challenge.fieldValue (toA P) f).testBit b.val

theorem bitRef_eq {n : Nat} (row : Fin n) (f : Field) (i : Nat) (hi : i < 256) :
    bitRef row f i = ⟨row, f, ⟨i, hi⟩⟩ := by
  unfold bitRef
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hi)

theorem RowReads.bit {n : Nat} {read : CBit n → Bool} {row : Fin n} {P : Point}
    (h : RowReads read row P) (f : Field) (i : Nat) (hi : i < 256) :
    read (bitRef row f i) = (ShorECDLP.Challenge.fieldValue (toA P) f).testBit i := by
  rw [bitRef_eq row f i hi]
  exact h f ⟨i, hi⟩

/-- The protected reader of the ShorECDLP challenge satisfies `RowReads` on every row. -/
theorem readConstant_rowReads {n : Nat} (coeffs : Fin n → ShorECDLP.Challenge.PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (row : Fin n) (P : Point)
    (hP : ShorECDLP.Challenge.constantPoint Q (coeffs row) = toA P) :
    RowReads (ShorECDLP.Challenge.readConstant coeffs Q) row P := by
  intro f b
  show (ShorECDLP.Challenge.fieldValue (ShorECDLP.Challenge.constantPoint Q (coeffs row)) f).testBit
    b.val = _
  rw [hP]

section Coordinates
open ShorECDLP.Challenge (pointCoordinates fieldValue doubledCoordinates)

theorem coords_finite (P : Point) : (pointCoordinates (toA P)).1 = !pointFinite P := by
  cases P <;> rfl

theorem coords_x (P : Point) : (pointCoordinates (toA P)).2.1.val = pointX P := by
  cases P <;> rfl

theorem coords_y (P : Point) : (pointCoordinates (toA P)).2.2.val = pointY P := by
  cases P <;> rfl

theorem toA_add (P R : Point) : toA P + toA R = toA (P + R) := rfl

theorem negY_eq (x y : Fp) : curve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, curve]

theorem pointFinite_neg (P : Point) : pointFinite (-P) = pointFinite P := by
  cases P with
  | zero => rfl
  | some h => rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

theorem pointX_neg (P : Point) : pointX (-P) = pointX P := by
  cases P with
  | zero => rfl
  | some h => rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

theorem pointY_neg (P : Point) : pointY (-P) = (-(pointCoordinates (toA P)).2.2).val := by
  cases P with
  | zero =>
    show pointY 0 = (-(0 : ShorECDLP.Fp)).val
    rw [neg_zero]; rfl
  | @some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    show (curve.toAffine.negY x y).val = (-y).val
    rw [negY_eq]

theorem infinity_bit (P : Point) :
    (fieldValue (toA P) .infinity).testBit 0 = !pointFinite P := by
  show (if (pointCoordinates (toA P)).1 then 1 else 0).testBit 0 = _
  rw [coords_finite]
  cases pointFinite P <;> rfl

theorem doubleInfinity_bit (P : Point) :
    (fieldValue (toA P) .doubleInfinity).testBit 0 = !pointFinite (P + P) := by
  show (if (pointCoordinates (toA P + toA P)).1 then 1 else 0).testBit 0 = _
  rw [toA_add, coords_finite]
  cases pointFinite (P + P) <;> rfl

theorem field_x (P : Point) : fieldValue (toA P) .x = pointX P := coords_x P
theorem field_y (P : Point) : fieldValue (toA P) .y = pointY P := coords_y P
theorem field_negY (P : Point) : fieldValue (toA P) .negY = pointY (-P) := (pointY_neg P).symm

theorem field_doubleX (P : Point) : fieldValue (toA P) .doubleX = pointX (P + P) := by
  show (pointCoordinates (toA P + toA P)).2.1.val = _
  rw [toA_add, coords_x]

theorem field_doubleY (P : Point) : fieldValue (toA P) .doubleY = pointY (P + P) := by
  show (pointCoordinates (toA P + toA P)).2.2.val = _
  rw [toA_add, coords_y]

theorem field_some_negX {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    fieldValue (toA (.some hc)) .negX = (-cx).val := rfl
theorem field_some_negY {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    fieldValue (toA (.some hc)) .negY = (-cy).val := rfl
theorem field_some_x {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    fieldValue (toA (.some hc)) .x = cx.val := rfl
theorem field_some_tripleX {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    fieldValue (toA (.some hc)) .tripleX = (3*cx).val := rfl

end Coordinates

/-! ## Constant-bit leaves -/

section Leaves
variable {n : Nat}

theorem testBit_zero' (k : Nat) : k.testBit 0 = decide (k % 2 = 1) := Nat.testBit_zero k

theorem testBit_succ' (k i : Nat) : k.testBit (i+1) = (k/2).testBit i := Nat.testBit_succ k i

/-- `maskedConstant c ws k`, the bits of `k` read from `ref 0, ref 1, …`. -/
def maskedT (c : Wire) : List Wire → (Nat → CBit n) → Tmpl n
  | [], _ => []
  | w :: ws, ref => .gated (ref 0) true (.CX c w) :: maskedT c ws (fun i => ref (i+1))

/-- `xorConstant ws k`, the bits of `k` read from `ref 0, ref 1, …`. -/
def xorT : List Wire → (Nat → CBit n) → Tmpl n
  | [], _ => []
  | w :: ws, ref => .gated (ref 0) true (.X w) :: xorT ws (fun i => ref (i+1))

theorem maskedT_inst (read : CBit n → Bool) (c : Wire) (ws : List Wire) (ref : Nat → CBit n)
    (k : Nat) (h : ∀ i < ws.length, read (ref i) = k.testBit i) :
    (maskedT c ws ref).instantiate read = maskedConstant c ws k := by
  induction ws generalizing ref k with
  | nil => rfl
  | cons w ws ih =>
    have h0 : read (ref 0) = decide (k % 2 = 1) := by
      rw [h 0 (by simp), testBit_zero']
    have ht : ∀ i < ws.length, read (ref (i+1)) = (k/2).testBit i := by
      intro i hi
      rw [h (i+1) (by simp; omega), testBit_succ']
    rw [maskedT, Tmpl.instantiate_cons, ih _ (k/2) ht]
    by_cases hk : k % 2 = 1 <;> simp [maskedConstant, TInstr.instantiate, h0, hk]

theorem xorT_inst (read : CBit n → Bool) (ws : List Wire) (ref : Nat → CBit n)
    (k : Nat) (h : ∀ i < ws.length, read (ref i) = k.testBit i) :
    (xorT ws ref).instantiate read = xorConstant ws k := by
  induction ws generalizing ref k with
  | nil => rfl
  | cons w ws ih =>
    have h0 : read (ref 0) = decide (k % 2 = 1) := by
      rw [h 0 (by simp), testBit_zero']
    have ht : ∀ i < ws.length, read (ref (i+1)) = (k/2).testBit i := by
      intro i hi
      rw [h (i+1) (by simp; omega), testBit_succ']
    rw [xorT, Tmpl.instantiate_cons, ih _ (k/2) ht]
    by_cases hk : k % 2 = 1 <;> simp [xorConstant, TInstr.instantiate, h0, hk]

theorem xorConstant_append : ∀ (ws ws' : List Wire) (k : Nat),
    xorConstant (ws ++ ws') k = xorConstant ws k ++ xorConstant ws' (k / 2^ws.length)
  | [], ws', k => by simp [xorConstant]
  | w :: ws, ws', k => by
    simp only [List.cons_append, xorConstant, List.length_cons]
    rw [xorConstant_append ws ws' (k/2), List.append_assoc, Nat.div_div_eq_div_mul, pow_succ']

theorem xorConstant_congr : ∀ (ws : List Wire) (a b : Nat),
    a % 2^ws.length = b % 2^ws.length → xorConstant ws a = xorConstant ws b
  | [], _, _, _ => rfl
  | w :: ws, a, b, h => by
    have h' : a % (2 * 2^ws.length) = b % (2 * 2^ws.length) := by
      rw [← pow_succ']; simpa using h
    have hdvd : 2 ∣ 2 * 2^ws.length := Dvd.intro _ rfl
    have h2 : a % 2 = b % 2 := by
      rw [← Nat.mod_mod_of_dvd a hdvd, h', Nat.mod_mod_of_dvd b hdvd]
    have hd : a / 2 % 2^ws.length = b / 2 % 2^ws.length := by
      rw [← Nat.mod_mul_right_div_self a 2 (2^ws.length),
        ← Nat.mod_mul_right_div_self b 2 (2^ws.length), h']
    simp only [xorConstant, h2, xorConstant_congr ws (a/2) (b/2) hd]

/-- `maskedPointConstant c r P`: finite flag from an `infinity`-type bit (gate when it is
clear), coordinates from two field bit sequences. -/
def maskedPointT (c : Wire) (r : PointReg) (fin : CBit n) (xr yr : Nat → CBit n) : Tmpl n :=
  [.gated fin false (.CX c r.finite)] ++ maskedT c r.x xr ++ maskedT c r.y yr

theorem maskedPointT_inst (read : CBit n → Bool) (c : Wire) (r : PointReg) (fin : CBit n)
    (xr yr : Nat → CBit n) (P : Point) (hf : read fin = !pointFinite P)
    (hx : ∀ i < r.x.length, read (xr i) = (pointX P).testBit i)
    (hy : ∀ i < r.y.length, read (yr i) = (pointY P).testBit i) :
    (maskedPointT c r fin xr yr).instantiate read = maskedPointConstant c r P := by
  simp only [maskedPointT, maskedPointConstant, Tmpl.instantiate_append,
    maskedT_inst read c r.x xr _ hx, maskedT_inst read c r.y yr _ hy]
  congr 2
  simp only [Tmpl.instantiate_cons, Tmpl.instantiate_nil, TInstr.instantiate, hf,
    maskedConstant, List.append_nil]
  cases pointFinite P <;> rfl

/-- `xorConstant (finite :: x) (pairCode P)`. -/
def pairXorT (L : ControlledPointLayout) (fin : CBit n) (xr : Nat → CBit n) : Tmpl n :=
  [.gated fin false (.X L.point.finite)] ++ xorT L.point.x xr

theorem pairXorT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (fin : CBit n)
    (xr : Nat → CBit n) (P : Point) (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i) :
    (pairXorT L fin xr).instantiate read = xorConstant (pairSrc L) (pairCode P) := by
  have hb : (pointFinite P).toNat ≤ 1 := by cases pointFinite P <;> decide
  have hm : pairCode P % 2 = (pointFinite P).toNat := by unfold pairCode; omega
  have hd : pairCode P / 2 = pointX P := by unfold pairCode; omega
  simp only [pairXorT, pairSrc, xorConstant, Tmpl.instantiate_append, hd, hm,
    xorT_inst read L.point.x xr _ hx]
  congr 1
  simp only [Tmpl.instantiate_cons, Tmpl.instantiate_nil, TInstr.instantiate, hf, List.append_nil]
  cases pointFinite P <;> rfl

/-- `xorConstant (shortSrc L) (shortCode P)`; `y0` is bit 0 of the ordinate. -/
def shortXorT (L : ControlledPointLayout) (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n) :
    Tmpl n :=
  [.gated fin false (.X L.point.finite)] ++ xorT L.point.x xr ++
    xorT (L.point.y.take 1) (fun _ => y0)

theorem shortXorT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (hw : L.Widths)
    (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n) (P : Point)
    (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i)
    (hy : read y0 = (pointY P).testBit 0) :
    (shortXorT L fin xr y0).instantiate read = xorConstant (shortSrc L) (shortCode P) := by
  have hxl : L.point.x.length = 256 := hw.inputX
  have hb : (pointFinite P).toNat ≤ 1 := by cases pointFinite P <;> decide
  have hX : pointX P < 2^256 := (point_coordinates_lt P).1.trans (by norm_num [p])
  generalize hm : pointX P + 2^256 * (pointY P % 2) = m
  have hcode : shortCode P = (pointFinite P).toNat + 2 * m := by rw [← hm]; rfl
  have hmod : shortCode P % 2 = (pointFinite P).toNat := by rw [hcode]; omega
  have hdiv : shortCode P / 2 = m := by rw [hcode]; omega
  have hlow : m % 2^256 = pointX P % 2^256 := by
    rw [← hm, Nat.add_mul_mod_self_left]
  have hhigh : m / 2^256 = pointY P % 2 := by
    rw [← hm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt hX, Nat.zero_add]
  have hsrc : shortSrc L = L.point.finite :: (L.point.x ++ L.point.y.take 1) := rfl
  rw [hsrc, xorConstant, hmod, hdiv, xorConstant_append, hxl, hhigh,
    xorConstant_congr L.point.x m (pointX P) (by rw [hxl]; exact hlow)]
  simp only [shortXorT, Tmpl.instantiate_append, xorT_inst read L.point.x xr _ hx,
    List.append_assoc]
  rw [xorT_inst read (L.point.y.take 1) (fun _ => y0) (pointY P % 2) (by
    intro i hi
    have hl := List.length_take_le 1 L.point.y
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hy, testBit_zero', testBit_zero', Nat.mod_mod])]
  congr 1
  simp only [Tmpl.instantiate_cons, Tmpl.instantiate_nil, TInstr.instantiate, hf, List.append_nil]
  cases pointFinite P <;> rfl

/-- `bitTest w y t a` with `a` read from `r`. -/
def bitTestT (w y t : Wire) (r : CBit n) : Tmpl n :=
  [.gated r false (.X y), .lit (.CCX w y t), .gated r false (.X y)]

theorem bitTestT_inst (read : CBit n → Bool) (w y t : Wire) (r : CBit n) (a : Bool)
    (h : read r = a) : (bitTestT w y t r).instantiate read = bitTest w y t a := by
  subst h
  cases hr : read r <;>
    simp [bitTestT, bitTest, zeroFlag, Tmpl.instantiate, TInstr.instantiate, hr]

def pairTailT (y t₁ t₂ : Wire) (r₁ r₂ : CBit n) (w : Wire) : Tmpl n :=
  bitTestT w y t₁ r₁ ++ bitTestT w y t₂ r₂

theorem pairTailT_inst (read : CBit n → Bool) (y t₁ t₂ : Wire) (r₁ r₂ : CBit n) (a₁ a₂ : Bool)
    (h₁ : read r₁ = a₁) (h₂ : read r₂ = a₂) (w : Wire) :
    (pairTailT y t₁ t₂ r₁ r₂ w).instantiate read = pairTail y t₁ t₂ true a₁ true a₂ w := by
  simp [pairTailT, pairTail, bitTestT_inst read _ _ _ _ _ h₁, bitTestT_inst read _ _ _ _ _ h₂]

def zeroWithT (T : Wire → Tmpl n) (c : Wire) : List ZeroBit → Tmpl n
  | [] => T c
  | b :: bs => Tmpl.lit (chainAnd c b.input b.work) ++ zeroWithT T b.work bs ++
      Tmpl.lit (chainErase c b.input b.work)

theorem zeroWithT_inst (read : CBit n → Bool) (T : Wire → Tmpl n) (T' : Wire → Program)
    (hT : ∀ w, (T w).instantiate read = T' w) (c : Wire) (bs : List ZeroBit) :
    (zeroWithT T c bs).instantiate read = zeroWith T' c bs := by
  induction bs generalizing c with
  | nil => exact hT c
  | cons b bs ih =>
    simp only [zeroWithT, zeroWith, Tmpl.instantiate_append, Tmpl.instantiate_lit, ih]

/-- `pairEqual L t₁ t₂ true true P D` (both enables literal). -/
def pairEqualT (L : ControlledPointLayout) (t₁ t₂ : Wire) (fin : CBit n) (xr : Nat → CBit n)
    (r₁ r₂ : CBit n) : Tmpl n :=
  pairXorT L fin xr ++ zeroWithT (pairTailT (yLow L) t₁ t₂ r₁ r₂) L.control (pairPorts L) ++
    pairXorT L fin xr

theorem pairEqualT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : CBit n) (xr : Nat → CBit n) (r₁ r₂ : CBit n) (P D : Point)
    (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i)
    (h₁ : read r₁ = yBit P) (h₂ : read r₂ = yBit D) :
    (pairEqualT L t₁ t₂ fin xr r₁ r₂).instantiate read = pairEqual L t₁ t₂ true true P D := by
  simp only [pairEqualT, pairEqual, Tmpl.instantiate_append, pairXorT_inst read L fin xr P hf hx,
    zeroWithT_inst read _ _ (pairTailT_inst read (yLow L) t₁ t₂ r₁ r₂ _ _ h₁ h₂)]

/-- `shortEqual L c t P`. -/
def shortEqualT (L : ControlledPointLayout) (c t : Wire) (fin : CBit n) (xr : Nat → CBit n)
    (y0 : CBit n) : Tmpl n :=
  shortXorT L fin xr y0 ++ Tmpl.lit (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
    shortXorT L fin xr y0

theorem shortEqualT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (hw : L.Widths)
    (c t : Wire) (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n) (P : Point)
    (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i)
    (hy : read y0 = (pointY P).testBit 0) :
    (shortEqualT L c t fin xr y0).instantiate read = shortEqual L c t P := by
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  have hsrc := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 258) hsl).1
  simp only [shortEqualT, shortEqual, equalConstant, hsrc, Tmpl.instantiate_append,
    Tmpl.instantiate_lit, shortXorT_inst read L hw fin xr y0 P hf hx hy]

/-- `pointDialogConstantAdd L r k`, the bits of `k.val` read from `ref`. -/
def constAddT (L : ControlledPointLayout) (r : List Wire) (ref : Nat → CBit n) : Tmpl n :=
  maskedT L.core.generic (L.recoveryConstant r).src ref ++
    Tmpl.lit ((L.recoveryConstant r).program SquareReduction.c p) ++
    maskedT L.core.generic (L.recoveryConstant r).src ref

theorem constAddT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (r : List Wire)
    (ref : Nat → CBit n) (k : Fp) (h : ∀ i < 256, read (ref i) = k.val.testBit i) :
    (constAddT L r ref).instantiate read = pointDialogConstantAdd L r k := by
  have hs : ∀ i < (L.recoveryConstant r).src.length, read (ref i) = k.val.testBit i := by
    intro i hi
    have : (L.recoveryConstant r).src.length ≤ 256 := by
      simp only [recoveryConstant]; exact List.length_take_le _ _
    exact h i (by omega)
  simp only [constAddT, pointDialogConstantAdd, pointRecoveryConstantAdd, compactRecoveryConstant,
    Tmpl.instantiate_append, Tmpl.instantiate_lit, maskedT_inst read _ _ ref _ hs]

end Leaves

/-! ## The template -/

section Template
variable {n : Nat}

/-- Bits `0, 1, …` of field `f` of row `row`. -/
def fieldBits (row : Fin n) (f : Field) : Nat → CBit n := bitRef row f

/-- Recovery stage: reflection, add `x`, add the literal `1`, add `negY`. -/
def recoveryT (L : ControlledPointLayout) (row : Fin n) : Tmpl n :=
  Tmpl.lit (pointRecoveryReflection L) ++ constAddT L L.point.x (fieldBits row .x) ++
    Tmpl.lit (pointDialogConstantAdd L L.point.x 1) ++ constAddT L L.point.y (fieldBits row .negY)

def genericT (L : ControlledPointLayout) (row : Fin n) : Tmpl n :=
  constAddT L L.point.x (fieldBits row .negX) ++
  constAddT L L.point.y (fieldBits row .negY) ++
  Tmpl.lit (pointCompressedArithmetic L false) ++
  Tmpl.lit (CompressedPointSquare.computableProgram L) ++
  constAddT L L.point.x (fieldBits row .tripleX) ++
  Tmpl.lit (pointCompressedArithmetic L true) ++
  recoveryT L row

/-- Corners: `C`, `C`, `C+C`, `-C`, `-(C+C)`, `-C` written under the respective flags. -/
def cornersT (L : ControlledPointLayout) (row rowD : Fin n) : Tmpl n :=
  maskedPointT L.infinitySelect L.point (bitRef row .infinity 0) (fieldBits row .x)
    (fieldBits row .y) ++
  maskedPointT L.doubleSelect L.point (bitRef row .infinity 0) (fieldBits row .x)
    (fieldBits row .y) ++
  maskedPointT L.doubleSelect L.point (bitRef row .doubleInfinity 0) (fieldBits row .doubleX)
    (fieldBits row .doubleY) ++
  maskedPointT L.genericSelect L.point (bitRef row .infinity 0) (fieldBits row .x)
    (fieldBits row .negY) ++
  maskedPointT L.core.equalNegY L.point (bitRef row .doubleInfinity 0) (fieldBits row .doubleX)
    (fieldBits rowD .negY) ++
  maskedPointT L.core.equalNegY L.point (bitRef row .infinity 0) (fieldBits row .x)
    (fieldBits row .negY)

/-- The template of `finiteS L C cx cy` for `C` on row `row` and `C + C` on row `rowD`. -/
def finiteT (L : ControlledPointLayout) (row rowD : Fin n) : Tmpl n :=
  Tmpl.lit [.CX L.control L.core.double] ++ Tmpl.lit [.CX L.control L.core.equalX] ++
  Tmpl.lit (zeroFlag L.point.finite L.control L.infinitySelect) ++
  pairEqualT L L.doubleSelect L.genericSelect (bitRef row .infinity 0) (fieldBits row .x)
    (bitRef row .y 0) (bitRef row .negY 0) ++
  shortEqualT L L.core.equalX L.core.equalNegY (bitRef row .doubleInfinity 0)
    (fieldBits row .doubleX) (bitRef rowD .negY 0) ++
  Tmpl.lit (pointDialogGenericFlag L) ++ genericT L row ++ cornersT L row rowD ++
  Tmpl.lit (pointDialogGenericFlag L) ++
  pairEqualT L L.infinitySelect L.core.equalNegY (bitRef row .infinity 0) (fieldBits row .x)
    (bitRef row .y 0) (bitRef row .negY 0) ++
  shortEqualT L L.core.double L.doubleSelect (bitRef row .doubleInfinity 0)
    (fieldBits row .doubleX) (bitRef row .doubleY 0) ++
  Tmpl.lit (zeroFlag L.point.finite L.control L.genericSelect) ++
  Tmpl.lit [.CX L.control L.core.equalX] ++ Tmpl.lit [.CX L.control L.core.double]

variable {read : CBit n → Bool} {row rowD : Fin n}

theorem yBit_eq (P : Point) : yBit P = (pointY P).testBit 0 := by
  rw [yBit, testBit_zero']

end Template

end ECDSAAdd.ShorPort

end

/-! ---------------------------------------------------------------------------
(formerly `ECDSALib/Structural.lean`) -/

/-! # Structural enables are true for every finite table point

The frontier program contains two enables that are compile-time booleans of `C`:
`cy ≠ -cy` (the doubling comparison) and `exceptionBit C` (`-(C+C) ∉ {0, C, -C}`). The template
`finiteT` emits both gates unconditionally. This is exact for every non-zero multiple of the
generator: the generator has prime order `order > 3`, so `C + C ≠ 0` and `C + C + C ≠ 0`. -/
noncomputable section
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.ShorPort
open Arithmetic Secp256k1 Entrant

/-- In the prime-order subgroup generated by `G`, `m • C ≠ 0` for `C ≠ 0` and `0 < m < order`. -/
theorem nsmul_ne_zero_of_multiple (C : ShorECDLP.Secp256k1.Point) (k m : ℕ)
    (hk : C = k • ShorECDLP.Secp256k1.G) (hC : C ≠ 0) (hm0 : 0 < m)
    (hm : m < ShorECDLP.order) : m • C ≠ 0 := by
  intro h
  rw [hk, smul_smul] at h
  have hd : ShorECDLP.order ∣ m * k := by
    rw [← ShorECDLP.Secp256k1.generator_order]
    exact addOrderOf_dvd_of_nsmul_eq_zero h
  rcases (Nat.Prime.dvd_mul ShorECDLP.Secp256k1.order_prime).mp hd with h1 | h1
  · exact absurd (Nat.le_of_dvd hm0 h1) (by omega)
  · apply hC
    rw [hk]
    rw [← ShorECDLP.Secp256k1.generator_order] at h1
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h1

/-- `C + C ≠ 0` and `C + C + C ≠ 0` for a non-zero multiple of the generator. -/
theorem double_triple_ne_zero (C : Point) (k : ℕ)
    (hk : toA C = k • ShorECDLP.Secp256k1.G) (hC : C ≠ 0) :
    C + C ≠ 0 ∧ C + C + C ≠ 0 := by
  have hord : 3 < ShorECDLP.order := by norm_num [ShorECDLP.order]
  have h2 := nsmul_ne_zero_of_multiple (toA C) k 2 hk hC (by decide) (by omega)
  have h3 := nsmul_ne_zero_of_multiple (toA C) k 3 hk hC (by decide) hord
  rw [two_nsmul] at h2
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul] at h3
  exact ⟨h2, h3⟩

/-- Both structural enables hold for a finite `C` with `C + C ≠ 0` and `C + C + C ≠ 0`. -/
theorem enables_true {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h2 : (.some hc : Point) + .some hc ≠ 0) (h3 : (.some hc : Point) + .some hc + .some hc ≠ 0) :
    cy ≠ -cy ∧ exceptionBit (.some hc) = true := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  refine ⟨(doubling_enabled_iff hc).mpr (fun h => h2 (eq_neg_iff_add_eq_zero.mp h)), ?_⟩
  have n1 : -(C + C) ≠ 0 := fun h => h2 (neg_eq_zero.mp h)
  have n2 : -(C + C) ≠ C := by
    intro h
    apply h3
    rw [← add_neg_cancel (C + C), h]
  have n3 : -(C + C) ≠ -C := by
    intro h
    apply hC
    have h' : C + C = C := neg_inj.mp h
    calc C = C + C - C := by abel
      _ = C - C := by rw [h']
      _ = 0 := sub_self C
  have f1 : pointEqual (dialogExceptionPoint C) 0 = false :=
    Bool.eq_false_iff.mpr fun h => n1 ((pointEqual_true_iff _ _).mp h)
  have f2 : pointEqual (dialogExceptionPoint C) C = false :=
    Bool.eq_false_iff.mpr fun h => n2 ((pointEqual_true_iff _ _).mp h)
  have f3 : pointEqual (dialogExceptionPoint C) (-C) = false :=
    Bool.eq_false_iff.mpr fun h => n3 ((pointEqual_true_iff _ _).mp h)
  simp only [exceptionBit, f1, f2, f3, Bool.not_false, Bool.and_self]

/-- Structural enables for a finite table point that is a multiple of the generator. -/
theorem enables_of_multiple {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (k : ℕ)
    (hk : toA (.some hc) = k • ShorECDLP.Secp256k1.G) :
    cy ≠ -cy ∧ exceptionBit (.some hc) = true :=
  have h := double_triple_ne_zero (.some hc) k hk (WeierstrassCurve.Affine.Point.some_ne_zero hc)
  enables_true hc h.1 h.2

/-! ## The instantiated template

Uniform over the table reader `read`, the rows and the curve point read: if `row` holds a finite
multiple `C = k • G` and `rowD` holds `C + C`, the instantiated template is exactly `finiteS`, so it
inherits the full specification and the resource bounds. -/

section Instantiated
open Challenge MappedCompressed Baselines CompressedPointDialog ControlledPointLayout
variable {n : Nat} {read : CBit n → Bool} {row rowD : Fin n}

end Instantiated

/-! ## Only `X` and `CX` gates are gated

The template's table-dependent instructions are single `X`/`CX` gates: no gated Toffoli and no
gated measurement, so the measurement sequence is the same for every table point. -/

section Clifford
variable {n : Nat}

end Clifford

section CountsAny
open Challenge MappedCompressed Baselines CompressedPointDialog ControlledPointLayout
variable {n : Nat}

end CountsAny

/-! ## B's contract on its fixed layout

`Challenge.encodes b R` (control wire, point register, every other wire clean) on B's `layout`:
the instantiated template meets B's per-addition contract, its wires lie in the 1,898-site
inventory `sitesQ layout` (`sitesQ_length`), and `qubits` counts at most those sites. -/

section Contract
open Challenge Baselines Entrant
variable {n : Nat} {read : CBit n → Bool} {row rowD : Fin n}

end Contract

end ECDSAAdd.ShorPort

end

/-! Consolidated development: Bridge. -/

/-! EDITABLE. The ShorECDLP side of the ecdsa.fail port, as one module.

The Entrant keeps few modules (the kernel replay loads each module's whole import closure in its
own task). Sections, in order:

1. `WindowMassSharp`, `Success`: phase-estimation window mass and the single-trial success bound.
2. `Chain`, `Coherent`: chaining 526 straight-line blocks and the per-block coherent contract
   `AddsCoherently`, composed into the Naive `ecdlpOracle` on an untouched ideal workspace.
3. `Translate`, `PointCode`, `Sound`, `Resources`: ECDSAAdd templates as challenge straight-line
   programs (`translate`), the point-register identification, soundness (`block_adds`) and the
   static resource counts.
4. `AdaptiveTrial`, `Assembly`: the observed trial and the generic `AddProvider` assembly
   (`AddProvider.certificate`).
-/

/-! ---------------------------------------------------------------------------
(formerly `WindowMassSharp.lean`) -/

/-! Sharp window mass for quantum phase estimation.

With `N = 2 ^ t ≥ 128 r` outcomes, the QPE outcome distribution for the phase `n / r`
puts mass at least `200 / 201` on the outcomes `a` whose rounding `round (r a / N)`
equals `n`.  Compared with `WindowMass.lean`, the pointwise estimate uses
`sin z ≥ z - z ^ 3 / 6` and `sin z = cos (π / 2 - z) ≥ 1 - (π / 2 - z) ^ 2 / 2`, giving
`1 / sin² z ≤ (3 / 2) (1 / z² + 1 / (π - z)²)` on `(0, π)`, so that
`|amplitude a|² ≤ 3 / (2 π²) (1 / u² + 1 / (N - u)²)`.  The two families of terms are
regrouped by the wrapped distances `phiR`, `phiL` (each injective with values `≥ L`), and a
telescoping estimate bounds the tail by `3 / (π² (L - 1)) < 1 / 201` for `L ≥ 64`. -/

-- The common sharp-window proof is supplied by the producer.

/-! ---------------------------------------------------------------------------
(formerly `Success.lean`) -/

/-! EDITABLE. Single-trial success from rounding-window mass.

For every nonzero character `k`, the joint distribution of the two phase
registers is a product of two phase-estimation distributions.  If each
distribution puts mass at least `c` on the samples that round to the correct
numerator, the canonical postprocessing recovers the secret with probability
at least `((r - 1) / r) * c ^ 2`. -/

namespace ShorECDLP.Entrant
open ShorECDLP.Quantum ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

end
end ShorECDLP.Entrant

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Chain.lean`) -/

/-! EDITABLE. Chaining closed straight-line blocks.

A block is a straight-line program `Straight n 0 M` that reads only its own measurement records.
`shiftStraight` (adapted from the protected `2607_13816/Challenge/CursorShift.lean`, Apache-2.0)
moves such a block to an arbitrary starting cursor without letting it read earlier records, so a
list of blocks concatenates to one straight-line program whose instantiation is the sequential
composition of the instantiated blocks, independently of the records produced before it. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Challenge NaiveChallenge

/-! ## Chains of closed blocks -/

theorem straightWires_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    ShorECDLP.NaiveChallenge.straightWires (p.append q) = ShorECDLP.NaiveChallenge.straightWires p ++ ShorECDLP.NaiveChallenge.straightWires q := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, ShorECDLP.NaiveChallenge.straightWires, ih, List.append_assoc]
  | recordGate i v g p ih => simp only [Straight.append, ShorECDLP.NaiveChallenge.straightWires, ih, List.append_assoc]
  | measure w p ih => simp only [Straight.append, ShorECDLP.NaiveChallenge.straightWires, ih, List.cons_append]

theorem straightWires_castFinish {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    ShorECDLP.NaiveChallenge.straightWires (castFinish h p) = ShorECDLP.NaiveChallenge.straightWires p := by
  subst f; rfl

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Coherent.lean`) -/

/-! EDITABLE. Adaptive controlled point additions refine the protected Naive oracle.

`AddsCoherently a ctrl pointReg work C` is the per-block contract of an adaptive controlled point
addition: on every computational-basis input whose point register holds a canonical point code
and whose workspace is clean, each Kraus branch equals one fixed coefficient times the basis state
in which the point register has been replaced by the (controlled) sum, and the coefficients have
total squared magnitude one.  Nothing else changes, for every value of every other wire.

Such a block coherently implements the protected Naive circuit `controlledPointAdd` placed on an
ideal workspace that the block never touches; a chain of blocks implements the Naive
`scalarMulCore`, hence the Naive `ecdlpOracle`, whose `ECDLPOracleSpec` is already proved. The
ideal workspace is purely mathematical: it is not part of the submitted program. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Secp256k1 Challenge NaiveChallenge

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-! ## Register lemmas -/

/-! ## One block -/

/-! ## Chains of blocks -/

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Translate.lean`) -/

/-! EDITABLE. Translating vendored ECDSAAdd programs into challenge straight-line programs.

An ECDSAAdd instruction is `X`, `CX`, `CCX`, or an X-basis measurement with reset followed by an
immediate list of `Z`/`CZ` corrections selected by the outcome.  A template instruction is such
an instruction, optionally switched by one table bit (`TInstr`).  The translation keeps the gates,
turns each measurement into the challenge's `measure` followed by record-controlled corrections on
that very record (`Z = H·X·H`, `CZ = H·CX·H`, all Clifford), and never switches a measurement.

`translate_branch` is the soundness theorem: on every signed basis state, every Kraus branch of
the instantiated translation equals `(1/√2)^M` times the signed basis state produced by the
ECDSAAdd semantics on that branch's measurement record. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Challenge NaiveChallenge

/-- An ECDSAAdd instruction, optionally enabled by one constant bit of the table. -/
inductive TInstr (n : Nat) where
  | lit (i : ECDSAAdd.Instr)
  | when (ref : ConstantBit n) (value : Bool) (i : ECDSAAdd.Instr)

namespace TInstr

def instantiate {n : Nat} (read : ConstantBit n → Bool) : TInstr n → ECDSAAdd.Program
  | .lit i => [i]
  | .when ref v i => if read ref = v then [i] else []

/-- The underlying instruction. -/
def instr {n : Nat} : TInstr n → ECDSAAdd.Instr
  | .lit i => i
  | .when _ _ i => i

/-- Records written by the translation (switched measurements are not allowed). -/
def meas {n : Nat} : TInstr n → Nat
  | .lit (.measureX _ _ _) => 1
  | _ => 0

/-- No measurement is switched by a table bit. -/
def Static {n : Nat} : TInstr n → Prop
  | .when _ _ (.measureX _ _ _) => False
  | _ => True

end TInstr

/-- The ECDSAAdd program selected by the table bits. -/
def instB {n : Nat} (read : ConstantBit n → Bool) (t : List (TInstr n)) : ECDSAAdd.Program :=
  t.flatMap (TInstr.instantiate read)

def tmplMeas {n : Nat} : List (TInstr n) → Nat
  | [] => 0
  | i :: t => i.meas + tmplMeas t

/-- Clifford circuit of one phase correction. -/
def corrCircuit : ECDSAAdd.Correction → Circuit
  | .Z t => pauliZ t
  | .CZ a b => if a = b then pauliZ a else controlledZ a b

def corrsCircuit (cs : List ECDSAAdd.Correction) : Circuit := cs.flatMap corrCircuit

/-- Gates controlled by one record bit. -/
def recordGates {n k e : Nat} (r : Fin k) (v : Bool) : Circuit → Straight n k e → Straight n k e
  | [], next => next
  | g :: gs, next => .recordGate r v g (recordGates r v gs next)

/-- One template instruction in front of the translation of the rest. -/
def TInstr.step {n e : Nat} : (i : TInstr n) → (k : Nat) → Straight n (k + i.meas) e →
    Straight n k e
  | .lit (.X a), _, next => .gate (.literal (.X a)) next
  | .lit (.CX a b), _, next => .gate (.literal (.CX a b)) next
  | .lit (.CCX a b c), _, next => .gate (.literal (.CCX a b c)) next
  | .lit (.measureX w c0 c1), k, next => .measure w
      (recordGates (Fin.last k) false (corrsCircuit c0)
        (recordGates (Fin.last k) true (corrsCircuit c1) next))
  | .when r v (.X a), _, next => .gate (.whenBit r v (.X a)) next
  | .when r v (.CX a b), _, next => .gate (.whenBit r v (.CX a b)) next
  | .when r v (.CCX a b c), _, next => .gate (.whenBit r v (.CCX a b c)) next
  | .when _ _ (.measureX _ _ _), _, next => next

theorem translate_end {n : Nat} (i : TInstr n) (t : List (TInstr n)) (k : Nat) :
    k + i.meas + tmplMeas t = k + tmplMeas (i :: t) := by
  rw [tmplMeas, Nat.add_assoc]

/-- The straight-line translation of a template, starting at record cursor `k`. -/
def translate {n : Nat} : (t : List (TInstr n)) → (k : Nat) → Straight n k (k + tmplMeas t)
  | [], k => castFinish (by rfl) (.done : Straight n k k)
  | i :: t, k => i.step k (castFinish (translate_end i t k) (translate t (k + i.meas)))

/-! ## Signed basis states -/

/-- The ECDSAAdd signed basis state as a challenge state vector. -/
noncomputable def signedKet (st : ECDSAAdd.State) : State :=
  (if st.phase then (-1 : ℂ) else 1) • ket st.basis

/-- The magnitude of one X-basis measurement branch. -/
noncomputable def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem upd_eq_update (s : BasisState) (t : Wire) (b : Bool) :
    s[t ↦ b] = ECDSAAdd.writeBit s t b := by
  funext j
  simp only [upd, ECDSAAdd.writeBit, Function.update_apply]

theorem run_gate_signed (g : Gate) (f : BasisState → BasisState)
    (hg : ∀ s, applyGate g (ket s) = ket (f s)) (st : ECDSAAdd.State) :
    Quantum.run [g] (signedKet st) = signedKet ⟨st.phase, f st.basis⟩ := by
  simp only [signedKet, run_cons, run_nil, map_smul, hg]

theorem run_X_signed (a : Wire) (st : ECDSAAdd.State) :
    Quantum.run [.X a] (signedKet st) =
      signedKet ⟨st.phase, ECDSAAdd.writeBit st.basis a (!st.basis a)⟩ := by
  rw [run_gate_signed (.X a) (fun s => ECDSAAdd.writeBit s a (!s a))]
  intro s
  rw [applyGate_X_ket, upd_eq_update]

theorem run_CX_signed (a b : Wire) (st : ECDSAAdd.State) :
    Quantum.run [.CX a b] (signedKet st) =
      signedKet ⟨st.phase, ECDSAAdd.writeBit st.basis b (st.basis b ^^ st.basis a)⟩ := by
  rw [run_gate_signed (.CX a b) (fun s => ECDSAAdd.writeBit s b (s b ^^ s a))]
  intro s
  rw [applyGate_ket]
  simp only [onKet, upd_eq_update]

theorem run_CCX_signed (a b c : Wire) (st : ECDSAAdd.State) :
    Quantum.run [.CCX a b c] (signedKet st) =
      signedKet ⟨st.phase, ECDSAAdd.writeBit st.basis c (st.basis c ^^ (st.basis a && st.basis b))⟩ := by
  rw [run_gate_signed (.CCX a b c) (fun s => ECDSAAdd.writeBit s c (s c ^^ (s a && s b)))]
  intro s
  rw [applyGate_ket]
  simp only [onKet, upd_eq_update]

theorem sign_mul (x y : Bool) :
    ((if x then (-1 : ℂ) else 1) * if y then (-1 : ℂ) else 1) = if (x ^^ y) then -1 else 1 := by
  cases x <;> cases y <;> norm_num

theorem run_corr_signed (c : ECDSAAdd.Correction) (st : ECDSAAdd.State) :
    Quantum.run (corrCircuit c) (signedKet st) = signedKet (ECDSAAdd.correct [c] st) := by
  obtain ⟨ph, s⟩ := st
  cases c with
  | Z t =>
    simp only [corrCircuit, signedKet, map_smul, run_pauliZ_ket, ECDSAAdd.correct]
    by_cases hb : s t <;> cases ph <;> simp [hb]
  | CZ a b =>
    by_cases h : a = b
    · subst h
      rw [corrCircuit, if_pos rfl]
      simp only [signedKet, map_smul, run_pauliZ_ket, ECDSAAdd.correct, Bool.and_self]
      by_cases hb : s a <;> cases ph <;> simp [hb]
    · rw [corrCircuit, if_neg h]
      simp only [signedKet, map_smul, run_controlledZ_ket a b _ h, ECDSAAdd.correct]
      by_cases ha : s a <;> by_cases hb : s b <;> cases ph <;> simp [ha, hb]

theorem correct_append (c : ECDSAAdd.Correction) (cs : List ECDSAAdd.Correction)
    (st : ECDSAAdd.State) : ECDSAAdd.correct (c :: cs) st =
      ECDSAAdd.correct cs (ECDSAAdd.correct [c] st) := by
  cases c <;> rfl

theorem run_corrs_signed (cs : List ECDSAAdd.Correction) (st : ECDSAAdd.State) :
    Quantum.run (corrsCircuit cs) (signedKet st) = signedKet (ECDSAAdd.correct cs st) := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    rw [corrsCircuit, List.flatMap_cons, Quantum.run_append, run_corr_signed,
      correct_append c cs st]
    exact ih _

theorem xReset_signed (w : Wire) (v : Bool) (st : ECDSAAdd.State) :
    xResetKraus w v (signedKet st) =
      invSqrtTwo • signedKet ⟨st.phase ^^ (v && st.basis w), ECDSAAdd.writeBit st.basis w false⟩ := by
  simp only [signedKet, map_smul, xResetKraus_ket, xResetCoeff, smul_smul, invSqrtTwo,
    upd_eq_update]
  congr 1
  rw [mul_left_comm, sign_mul]

/-! ## Branch structure -/

theorem recordGates_branch {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) (read : ConstantBit n → Bool) (h : Fin k → Bool)
    (b : InstrumentBranch) (hb : b ∈ ((recordGates r v gs next).instantiate read h).run) :
    ∃ c ∈ (next.instantiate read h).run, b.history = c.history ∧
      ∀ ψ, b.kraus ψ = c.kraus (Quantum.run (if h r = v then gs else []) ψ) := by
  induction gs generalizing b with
  | nil =>
    refine ⟨b, hb, rfl, fun ψ => ?_⟩
    split <;> rfl
  | cons g gs ih =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨c, hc, hh, hk⟩ := ih d hd
    refine ⟨c, hc, hh, fun ψ => ?_⟩
    change d.kraus (Quantum.run (if h r = v then [g] else []) ψ) = _
    rw [hk]
    split <;> rfl

/-- Soundness of the translation on signed basis states. -/
theorem translate_branch {n : Nat} (read : ConstantBit n → Bool) :
    ∀ (t : List (TInstr n)), (∀ i ∈ t, i.Static) →
    ∀ (k : Nat) (h : Fin k → Bool) (b : InstrumentBranch),
      b ∈ ((translate t k).instantiate read h).run →
      ∀ st : ECDSAAdd.State, b.kraus (signedKet st) =
        invSqrtTwo ^ tmplMeas t • signedKet (ECDSAAdd.run (instB read t) b.history st)
  | [], _, k, h, b, hb, st => by
    simp only [translate, instantiate_castFinish, Straight.instantiate, AdaptiveCircuit.run,
      List.mem_singleton] at hb
    subst b
    simp [tmplMeas, instB, ECDSAAdd.run]
  | i :: t, hs, k, h, b, hb, st => by
    have hst : ∀ j ∈ t, j.Static := fun j hj => hs j (List.mem_cons_of_mem _ hj)
    have hi : i.Static := hs i List.mem_cons_self
    have ih := translate_branch read t hst
    cases i with
    | lit i =>
      cases i with
      | X a =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run [.X a] (signedKet st)) = _
        rw [run_X_signed, ih k h c hc]
        simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
          TInstr.instantiate, List.singleton_append, ECDSAAdd.run]
        rfl
      | CX a b' =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run [.CX a b'] (signedKet st)) = _
        rw [run_CX_signed, ih k h c hc]
        simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
          TInstr.instantiate, List.singleton_append, ECDSAAdd.run]
        rfl
      | CCX a b' c' =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run [.CCX a b' c'] (signedKet st)) = _
        rw [run_CCX_signed, ih k h c hc]
        simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
          TInstr.instantiate, List.singleton_append, ECDSAAdd.run]
        rfl
      | measureX w c0 c1 =>
        simp only [translate, TInstr.step, Straight.instantiate, AdaptiveCircuit.run] at hb
        rcases List.mem_append.mp hb with hb | hb
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
          obtain ⟨d₁, hd₁, hh₁, hk₁⟩ := recordGates_branch _ _ _ _ read _ d hd
          obtain ⟨d₂, hd₂, hh₂, hk₂⟩ := recordGates_branch _ _ _ _ read _ d₁ hd₁
          rw [instantiate_castFinish] at hd₂
          change d.kraus (xResetKraus w false (signedKet st)) = _
          rw [hk₁, hk₂]
          simp only [Fin.lastCases_last, if_true, if_false, Bool.false_eq_true, run_nil]
          rw [xReset_signed, map_smul, map_smul, run_corrs_signed, ih _ _ d₂ hd₂, smul_smul]
          change _ = _ • signedKet (ECDSAAdd.run (instB read (TInstr.lit (.measureX w c0 c1) :: t))
            (false :: d.history) st)
          rw [hh₁, hh₂]
          simp only [tmplMeas, TInstr.meas, instB, List.flatMap_cons, TInstr.instantiate,
            List.singleton_append, ECDSAAdd.run, ECDSAAdd.measureAndCorrect, List.headD_cons,
            List.tail_cons, Bool.false_and, Bool.xor_false, if_false, Bool.false_eq_true]
          congr 1
          ring
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
          obtain ⟨d₁, hd₁, hh₁, hk₁⟩ := recordGates_branch _ _ _ _ read _ d hd
          obtain ⟨d₂, hd₂, hh₂, hk₂⟩ := recordGates_branch _ _ _ _ read _ d₁ hd₁
          rw [instantiate_castFinish] at hd₂
          change d.kraus (xResetKraus w true (signedKet st)) = _
          rw [hk₁, hk₂]
          simp only [Fin.lastCases_last, if_true, Bool.true_eq_false, if_false, run_nil]
          rw [xReset_signed, map_smul, map_smul, run_corrs_signed, ih _ _ d₂ hd₂, smul_smul]
          change _ = _ • signedKet (ECDSAAdd.run (instB read (TInstr.lit (.measureX w c0 c1) :: t))
            (true :: d.history) st)
          rw [hh₁, hh₂]
          simp only [tmplMeas, TInstr.meas, instB, List.flatMap_cons, TInstr.instantiate,
            List.singleton_append, ECDSAAdd.run, ECDSAAdd.measureAndCorrect, List.headD_cons,
            List.tail_cons, Bool.true_and, if_true]
          congr 1
          ring
    | when r v i =>
      cases i with
      | X a =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run (TemplateGate.instantiate read (.whenBit r v (.X a)))
          (signedKet st)) = _
        simp only [TemplateGate.instantiate]
        by_cases hr : read r = v
        · rw [if_pos hr, run_X_signed, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_pos hr, List.singleton_append, ECDSAAdd.run]
          rfl
        · rw [if_neg hr, run_nil, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_neg hr, List.nil_append]
          rfl
      | CX a b' =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run (TemplateGate.instantiate read (.whenBit r v (.CX a b')))
          (signedKet st)) = _
        simp only [TemplateGate.instantiate]
        by_cases hr : read r = v
        · rw [if_pos hr, run_CX_signed, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_pos hr, List.singleton_append, ECDSAAdd.run]
          rfl
        · rw [if_neg hr, run_nil, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_neg hr, List.nil_append]
          rfl
      | CCX a b' c' =>
        simp only [translate, TInstr.step, Straight.instantiate] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        rw [instantiate_castFinish] at hc
        change c.kraus (Quantum.run (TemplateGate.instantiate read (.whenBit r v (.CCX a b' c')))
          (signedKet st)) = _
        simp only [TemplateGate.instantiate]
        by_cases hr : read r = v
        · rw [if_pos hr, run_CCX_signed, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_pos hr, List.singleton_append, ECDSAAdd.run]
          rfl
        · rw [if_neg hr, run_nil, ih k h c hc]
          simp only [tmplMeas, TInstr.meas, Nat.zero_add, instB, List.flatMap_cons,
            TInstr.instantiate, if_neg hr, List.nil_append]
          rfl
      | measureX w c0 c1 => exact hi.elim

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/PointCode.lean`) -/

/-! EDITABLE. The vendored ECDSAAdd curve and point register are the challenge's.

The vendored `ECDSAAdd.Math.BitcoinCurve` defines the same prime, curve, generator and point type
as the protected `ShorECDLP.Math.BitcoinCurve`, so the two point types are definitionally equal,
with the same group law.  The ECDSAAdd point register (finite tag on wire 1, `x` on wires
2..257, `y` on wires 258..513) holds a point exactly when the challenge's little-endian register
`List.range' 1 513` holds its canonical 513-bit code. -/

namespace ShorECDLP.Entrant.Bridge

/-- View a challenge point as a vendored ECDSAAdd point (the identity map). -/
def toB (P : ShorECDLP.Secp256k1.Point) : ECDSAAdd.Secp256k1.Point := P

section
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem toB_neg (P : ShorECDLP.Secp256k1.Point) : toB (-P) = -toB P := rfl

end

/-! ## Registers -/

theorem regValueB_eq (r : List Nat) (st : Nat → Bool) :
    ECDSAAdd.regValue r st = ShorECDLP.regValue r st := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    simp only [ECDSAAdd.regValue, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

theorem map_add_range (s n : Nat) : (List.range n).map (· + s) = List.range' s n := by
  rw [List.range'_eq_map_range]
  apply List.map_congr_left
  intro a _
  exact Nat.add_comm a s

/-- The challenge point register in the ECDSAAdd layout. -/
def pointWires : List Nat := List.range' 1 513

theorem pointWires_split :
    pointWires = 1 :: (List.range' 2 256 ++ List.range' 258 256) := by
  rw [pointWires, List.range'_append]
  rfl

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Sound.lean`) -/

/-! EDITABLE. From ECDSAAdd specifications to coherent challenge blocks.

`translate_adds` turns an exact record-independent ECDSAAdd run into the challenge contract
`AddsCoherently`: every one of the `2^M` Kraus branches carries the same coefficient
`(1/√2)^M`.  `run_of_triple` derives that exact run from an ECDSAAdd `Triple` (phase restored,
point updated, workspace clean) plus a support bound, and `run_rename` (vendored) moves the control
wire from 0 to the phase qubit of the addition. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Challenge NaiveChallenge Secp256k1

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-! ## Branch count and coefficients -/

theorem straight_run_length {n s e : Nat} (p : Straight n s e) (read : ConstantBit n → Bool)
    (h : Fin s → Bool) : (p.instantiate read h).run.length = 2 ^ (e - s) := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.run]
  | gate g p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.run, List.length_map]
    exact ih h
  | recordGate i v g p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.run, List.length_map]
    exact ih h
  | measure w p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.run, List.length_append, List.length_map,
      ih]
    have hm := p.cursor_mono
    rw [← two_mul, ← Nat.pow_succ']
    congr 1
    omega

theorem normSq_invSqrtTwo : Complex.normSq invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem signedKet_false (s : BasisState) : signedKet ⟨false, s⟩ = ket s := by
  simp [signedKet]

/-! ## Exact runs from ECDSAAdd triples -/

theorem regValue_bits (r : List Wire) (s t : BasisState) (h : regValue r s = regValue r t) :
    ∀ w ∈ r, s w = t w := by
  induction r with
  | nil => simp
  | cons x xs ih =>
    rw [regValue_cons, regValue_cons] at h
    have hx : s x = t x := by
      cases hs : s x <;> cases ht : t x <;> simp [hs, ht] at h ⊢ <;> omega
    have hxs : regValue xs s = regValue xs t := by
      rw [hx] at h
      omega
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hx
    · exact ih hxs w hw

/-- The vendored ECDSAAdd control wire. -/
def bControl : Wire := 0

/-- The ECDSAAdd contract of a controlled addition of `C`, on workspace `work`. -/
def BSpec (prog : ECDSAAdd.Program) (C : Point) (work : List Wire) : Prop :=
  ∀ (b : Bool) (R : Point), ECDSAAdd.Triple
    (fun st => st bControl = b ∧ ECDSAAdd.Holds.holds st ECDSAAdd.Challenge.point (toB R) ∧
      ∀ w ∈ work, st w = false) prog
    (fun st => st bControl = b ∧
      ECDSAAdd.Holds.holds st ECDSAAdd.Challenge.point (toB (controlledPointResult b R C)) ∧
      ∀ w ∈ work, st w = false)

/-! ## Moving the control wire -/

/-! ## Renamed templates -/

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Resources.lean`) -/

/-! EDITABLE. Static resources of translated templates.

Every count is a template-level (slot) count, independent of the table: switched-off
instructions still occupy their slots, as in the challenge's static T bound.

* T model: `straightT (translate t k) = 7 * tmplToffoli t` (corrections are Clifford);
* records: `tmplMeas t`, the number of unswitched measurements;
* gate slots: `tmplSlots t` (one per gate, three per correction);
* wires: contained in `tmplWires t`;
* well-formedness: from the vendored ECDSAAdd `instructionValid` of every template instruction. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Challenge NaiveChallenge

def TInstr.toffoli {n : Nat} : TInstr n → Nat
  | .lit (.CCX _ _ _) => 1
  | .when _ _ (.CCX _ _ _) => 1
  | _ => 0

def tmplToffoli {n : Nat} (t : List (TInstr n)) : Nat := (t.map TInstr.toffoli).sum

def corrsSlots (cs : List ECDSAAdd.Correction) : Nat := 3 * cs.length

def TInstr.slots {n : Nat} : TInstr n → Nat
  | .lit (.measureX _ c0 c1) => corrsSlots c0 + corrsSlots c1
  | .when _ _ (.measureX _ _ _) => 0
  | _ => 1

def tmplSlots {n : Nat} (t : List (TInstr n)) : Nat := (t.map TInstr.slots).sum

def corrWires : ECDSAAdd.Correction → List Wire
  | .Z a => [a]
  | .CZ a b => [a, b]

def instrWires : ECDSAAdd.Instr → List Wire
  | .X a => [a]
  | .CX a b => [a, b]
  | .CCX a b c => [a, b, c]
  | .measureX w c0 c1 => w :: (c0.flatMap corrWires ++ c1.flatMap corrWires)

def tmplWires {n : Nat} (t : List (TInstr n)) : List Wire := t.flatMap fun i => instrWires i.instr

/-! ## Append and literal lemmas -/

theorem instB_lit {n : Nat} (read : ConstantBit n → Bool) (p : ECDSAAdd.Program) :
    instB read (p.map (TInstr.lit (n := n))) = p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [instB, List.map_cons, List.flatMap_cons, TInstr.instantiate] at ih ⊢
    rw [ih]
    rfl

theorem static_lit {n : Nat} (p : ECDSAAdd.Program) : ∀ i ∈ p.map (TInstr.lit (n := n)), i.Static := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  cases j <;> trivial

/-! ## Translation counts -/

theorem tCount_corrs (cs : List ECDSAAdd.Correction) : tCount (corrsCircuit cs) = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [corrsCircuit, List.flatMap_cons, tCount_append]
    rw [corrsCircuit] at ih
    rw [ih]
    cases c with
    | Z a => rfl
    | CZ a b => simp only [corrCircuit]; split <;> rfl

theorem gateSlots_recordGates {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) :
    (recordGates r v gs next).gateSlots = gs.length + next.gateSlots := by
  induction gs with
  | nil => simp [recordGates]
  | cons g gs ih => simp only [recordGates, Straight.gateSlots, ih, List.length_cons]; omega

theorem corrsCircuit_length (cs : List ECDSAAdd.Correction) :
    (corrsCircuit cs).length = corrsSlots cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [corrsCircuit, List.flatMap_cons, List.length_append]
    rw [corrsCircuit] at ih
    rw [ih, corrsSlots, corrsSlots, List.length_cons]
    cases c with
    | Z a => simp [corrCircuit, pauliZ]; omega
    | CZ a b =>
      simp only [corrCircuit]
      split <;> simp [pauliZ, controlledZ] <;> omega

theorem translate_gateSlots {n : Nat} :
    ∀ (t : List (TInstr n)) (k : Nat), (translate t k).gateSlots = tmplSlots t
  | [], k => by simp [translate, tmplSlots, Straight.gateSlots]
  | i :: t, k => by
    have ih := translate_gateSlots t (k + i.meas)
    simp only [tmplSlots, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    cases i with
    | lit i =>
      cases i <;> simp [translate, TInstr.step, Straight.gateSlots, gateSlots_recordGates,
        corrsCircuit_length, TInstr.slots]
      all_goals omega
    | when r v i =>
      cases i <;> simp [translate, TInstr.step, Straight.gateSlots, TInstr.slots]

/-! ## Wires -/

theorem straightWires_recordGates {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) :
    ShorECDLP.NaiveChallenge.straightWires (recordGates r v gs next) = circuitWires gs ++ ShorECDLP.NaiveChallenge.straightWires next := by
  induction gs with
  | nil => simp [recordGates, circuitWires]
  | cons g gs ih =>
    simp only [recordGates, ShorECDLP.NaiveChallenge.straightWires, ih, circuitWires, List.flatMap_cons, List.append_assoc]

theorem corrsCircuit_wires (cs : List ECDSAAdd.Correction) :
    ∀ w ∈ circuitWires (corrsCircuit cs), w ∈ cs.flatMap corrWires := by
  intro w hw
  simp only [circuitWires, corrsCircuit, List.mem_flatMap] at hw ⊢
  obtain ⟨g, ⟨c, hc, hg⟩, hw⟩ := hw
  refine ⟨c, hc, ?_⟩
  cases c with
  | Z a =>
    simp only [corrCircuit, pauliZ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simpa [gateWires, corrWires] using hw
  | CZ a b =>
    simp only [corrCircuit] at hg
    split at hg
    · simp only [pauliZ, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp_all [gateWires, corrWires]
    · simp only [controlledZ, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp_all [gateWires, corrWires]

theorem translate_wires {n : Nat} :
    ∀ (t : List (TInstr n)) (k : Nat), ∀ w ∈ ShorECDLP.NaiveChallenge.straightWires (translate t k), w ∈ tmplWires t
  | [], k => by simp [translate, straightWires_castFinish, ShorECDLP.NaiveChallenge.straightWires]
  | i :: t, k => by
    have ih := translate_wires t (k + i.meas)
    intro w hw
    simp only [tmplWires, List.flatMap_cons, List.mem_append] at ih ⊢
    cases i with
    | lit i =>
      cases i with
      | measureX x c0 c1 =>
        simp only [translate, TInstr.step, ShorECDLP.NaiveChallenge.straightWires, straightWires_recordGates,
          straightWires_castFinish, List.mem_cons, List.mem_append] at hw
        rcases hw with rfl | hw | hw | hw
        · left; simp [TInstr.instr, instrWires]
        · left; simp only [TInstr.instr, instrWires, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl (corrsCircuit_wires c0 w hw))
        · left; simp only [TInstr.instr, instrWires, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (corrsCircuit_wires c1 w hw))
        · exact Or.inr (ih w hw)
      | _ =>
        simp only [translate, TInstr.step, ShorECDLP.NaiveChallenge.straightWires, straightWires_castFinish, slotGate,
          gateWires, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with hw | hw
        all_goals first
          | exact Or.inr (ih w hw)
          | (left; simp only [TInstr.instr, instrWires, List.mem_cons, List.not_mem_nil]; tauto)
    | when r v i =>
      cases i with
      | measureX x c0 c1 =>
        simp only [translate, TInstr.step, straightWires_castFinish] at hw
        exact Or.inr (ih w hw)
      | _ =>
        simp only [translate, TInstr.step, ShorECDLP.NaiveChallenge.straightWires, straightWires_castFinish, slotGate,
          gateWires, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with hw | hw
        all_goals first
          | exact Or.inr (ih w hw)
          | (left; simp only [TInstr.instr, instrWires, List.mem_cons, List.not_mem_nil]; tauto)

/-! ## Well-formedness -/

theorem recordGates_wellFormed {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) (hg : CircuitWellFormed gs) (hn : next.WellFormed) :
    (recordGates r v gs next).WellFormed := by
  induction gs with
  | nil => exact hn
  | cons g gs ih =>
    exact ⟨hg g List.mem_cons_self, ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))⟩

theorem corrsCircuit_wellFormed (cs : List ECDSAAdd.Correction) :
    CircuitWellFormed (corrsCircuit cs) := by
  intro g hg
  simp only [corrsCircuit, List.mem_flatMap] at hg
  obtain ⟨c, _, hg⟩ := hg
  cases c with
  | Z a => exact pauliZ_wellFormed a g hg
  | CZ a b =>
    simp only [corrCircuit] at hg
    split at hg
    · exact pauliZ_wellFormed a g hg
    · exact controlledZ_wellFormed a b (by assumption) g hg

theorem translate_wellFormed {n : Nat} :
    ∀ (t : List (TInstr n)) (k : Nat),
      (∀ i ∈ t, ECDSAAdd.Challenge.instructionValid i.instr) → (translate t k).WellFormed
  | [], k, _ => by simp [translate, Straight.WellFormed]
  | i :: t, k, hv => by
    have ih := translate_wellFormed t (k + i.meas) (fun j hj => hv j (List.mem_cons_of_mem _ hj))
    have hi := hv i List.mem_cons_self
    cases i with
    | lit i =>
      cases i with
      | measureX x c0 c1 =>
        simp only [translate, TInstr.step, Straight.WellFormed]
        exact recordGates_wellFormed _ _ _ _ (corrsCircuit_wellFormed c0)
          (recordGates_wellFormed _ _ _ _ (corrsCircuit_wellFormed c1)
            (by rw [wellFormed_castFinish]; exact ih))
      | _ =>
        simp only [translate, TInstr.step, Straight.WellFormed, wellFormed_castFinish]
        exact ⟨hi, ih⟩
    | when r v i =>
      cases i with
      | measureX x c0 c1 =>
        simp only [translate, TInstr.step, wellFormed_castFinish]
        exact ih
      | _ =>
        simp only [translate, TInstr.step, Straight.WellFormed, wellFormed_castFinish]
        exact ⟨hi, ih⟩

end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/AdaptiveTrial.lean`) -/

/-! EDITABLE. One observed trial whose oracle is a chain of adaptive point additions.

The straight-line program is

```text
hadamards(A ++ B) ; block₀ ; … ; block₅₂₅ ; iqft A ; iqft B ; observe(A ++ B)
```

where every block is a closed straight-line program (it reads only its own measurement records)
satisfying `AddsCoherently` for its control wire and table point.  The internal records of the
blocks come first in every history; the 526 phase bits follow them.  Coherent refinement
(`CoherentlyImplementsOn.terminalMass`) replaces the chain of blocks by the protected Naive
`ecdlpOracle` on an ideal workspace that the program never touches, and the single-trial window
bound of the unitary pipeline (`success_of_window_mass`, `window_mass_sharp`) then applies
unchanged, read through the protected `nearestPair` decoder at shifted record positions. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Secp256k1 Challenge NaiveChallenge
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
noncomputable section

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-! ## Instruments -/

/-! ## The straight-line trial -/

/-! ## Layout -/

/-! ## The ideal oracle -/

/-! ## Decoder at shifted positions -/

/-! ## Probability of the ideal trial -/

/-! ## The adaptive trial -/

end
end ShorECDLP.Entrant.Bridge

/-! ---------------------------------------------------------------------------
(formerly `Bridge/Assembly.lean`) -/

/-! EDITABLE. Generic assembly of the certified entry from controlled-addition templates.

An `AddProvider` supplies, for each of the 526 controlled additions, an ECDSAAdd template whose
control is wire 0, whose point register is wires 1..513 and whose workspace is `work`, with its
ECDSAAdd specification and its static template counts.  The assembly

* renames wire 0 of block `j` to the phase qubit `206624 + j` (registers `A = 206624..206886`,
  `B = 206887..207149`, QFT ancilla `207150`),
* chains the 526 translated blocks between the Hadamards and the two inverse QFTs,
* places the protected Naive ideal workspace at its original position `1026..206623`; the
  submitted program never touches it, so it costs no qubit, and
* proves the `Certificate` for any declared bounds above the static counts. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Secp256k1 Challenge NaiveChallenge
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
noncomputable section

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-! ## Wire layout -/

/-! ## Table points -/

/-- The table point added by block `j`: `2^j • G` for the first register, `2^(j-263) • Q`. -/
def tablePoint (Q : Point) (j : Fin 526) : Point :=
  if j.val < 263 then (2 ^ j.val) • G else (2 ^ (j.val - 263)) • Q

/-! ## Static helpers -/

/-! ## Providers -/

/-- Everything the controlled-addition library provides. -/
structure AddProvider where
  n : Nat
  coeffs : Fin n → PointCoeff
  work : List Wire
  M : Nat
  T : Nat
  S : Nat
  tmpl : Fin 526 → List (TInstr n)
  static : ∀ j, ∀ i ∈ tmpl j, i.Static
  valid : ∀ j, ∀ i ∈ tmpl j, ECDSAAdd.Challenge.instructionValid i.instr
  supp : List Wire
  wires : ∀ j, ∀ w ∈ tmplWires (tmpl j), w ∈ supp
  supp_range : ∀ w : Nat, w ∈ supp → w < 206624
  supp_cover : ∀ w : Nat, w ∈ supp → w = bControl ∨ w ∈ pointWires ∨ w ∈ work
  work_range : ∀ w : Nat, w ∈ work → 514 ≤ w ∧ w < 206624
  meas : ∀ j, tmplMeas (tmpl j) = M
  toffoli : ∀ j, tmplToffoli (tmpl j) ≤ T
  slots : ∀ j, tmplSlots (tmpl j) ≤ S
  spec : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G → ∀ j : Fin 526,
    BSpec (instB (readConstant coeffs Q) (tmpl j)) (tablePoint Q j) work

namespace AddProvider

variable (P : AddProvider)

/-! ## Success -/

/-! ## Static resources -/

end AddProvider
end
end ShorECDLP.Entrant.Bridge

/-! Consolidated development: WEX. -/

/-!
Copyright 2026 ShorECDLP contributors. Apache-2.0.

One window-addressed constant-addition experiment. The protected measured lookup
replaces both constant masks around the vendored measured canonical adder.
This module proves a component, not a new end-to-end challenge entry.
-/
namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-! The bridge's record controls are local to the translated program. -/

def literalT {n : Nat} (p : ECDSAAdd.Program) : List (Bridge.TInstr n) :=
  p.map Bridge.TInstr.lit

def literalSource : ECDSAAdd.Program → AdaptiveCircuit
  | [] => .done
  | .X a :: p => .unitary [.X a] (literalSource p)
  | .CX a b :: p => .unitary [.CX a b] (literalSource p)
  | .CCX a b c :: p => .unitary [.CCX a b c] (literalSource p)
  | .measureX w c0 c1 :: p => .xMeasureReset w
      (.unitary (Bridge.corrsCircuit c0) (literalSource p))
      (.unitary (Bridge.corrsCircuit c1) (literalSource p))

theorem recordGates_run {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) (read : ConstantBit n → Bool) (h : Fin k → Bool) :
    ((Bridge.recordGates r v gs next).instantiate read h).run =
      (.unitary (if h r = v then gs else []) (next.instantiate read h) : AdaptiveCircuit).run := by
  induction gs with
  | nil =>
    simp only [Bridge.recordGates, ite_self, AdaptiveCircuit.run]
    symm
    apply List.map_id'
  | cons g gs ih =>
    simp only [Bridge.recordGates, Straight.instantiate, AdaptiveCircuit.run, ih]
    by_cases hv : h r = v <;> simp [hv, List.map_map]
    all_goals intro a ha; cases a; rfl

theorem literal_run {n : Nat} (p : ECDSAAdd.Program) (start : Nat)
    (read : ConstantBit n → Bool) (h : Fin start → Bool) :
    ((Bridge.translate (literalT p) start).instantiate read h).run = (literalSource p).run := by
  induction p generalizing start with
  | nil => simp [literalT, Bridge.translate, NaiveChallenge.instantiate_castFinish, literalSource, Straight.instantiate]
  | cons i p ih =>
    simp only [literalT] at ih
    cases i <;>
      simp only [literalT, List.map_cons, Bridge.translate, Bridge.TInstr.step, Bridge.TInstr.meas, Nat.add_zero,
        Straight.instantiate, NaiveChallenge.instantiate_castFinish, literalSource, AdaptiveCircuit.run,
        recordGates_run, Fin.lastCases_last, if_true, Bool.false_eq_true, if_false, ih]
    all_goals try simp only [AdaptiveCircuit.run, List.map_map, ih]
    all_goals rfl

theorem literal_meas {n : Nat} (p : ECDSAAdd.Program) :
    Bridge.tmplMeas (literalT (n := n) p) = ECDSAAdd.measurementCount p := by
  induction p with
  | nil => rfl
  | cons i p ih => cases i <;> simp [literalT, Bridge.tmplMeas, Bridge.TInstr.meas,
      ECDSAAdd.measurementCount, literalT] at ih ⊢ <;> omega

theorem recordGates_tCount {n k e : Nat} (r : Fin k) (v : Bool) (gs : Circuit)
    (next : Straight n k e) (read : ConstantBit n → Bool) (h : Fin k → Bool) :
    ((Bridge.recordGates r v gs next).instantiate read h).tCount =
      tCount (if h r = v then gs else []) + (next.instantiate read h).tCount := by
  induction gs with
  | nil => simp [Bridge.recordGates, tCount]
  | cons g gs ih =>
    simp only [Bridge.recordGates, Straight.instantiate, AdaptiveCircuit.tCount, ih]
    by_cases hv : h r = v <;> simp [hv, tCount, Nat.add_assoc]

theorem literal_program_tCount {n : Nat} (p : ECDSAAdd.Program) (start : Nat)
    (read : ConstantBit n → Bool) (h : Fin start → Bool) :
    ((Bridge.translate (literalT p) start).instantiate read h).tCount =
      7 * ECDSAAdd.toffoliCount p := by
  induction p generalizing start with
  | nil => simp [literalT, Bridge.translate, NaiveChallenge.instantiate_castFinish,
      Straight.instantiate, AdaptiveCircuit.tCount, ECDSAAdd.toffoliCount]
  | cons i p ih =>
    simp only [literalT] at ih
    cases i <;> simp only [literalT, List.map_cons, Bridge.translate, Bridge.TInstr.step, Bridge.TInstr.meas, Nat.add_zero,
      Straight.instantiate, NaiveChallenge.instantiate_castFinish, AdaptiveCircuit.tCount,
      recordGates_tCount, Fin.lastCases_last, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      Bridge.tCount_corrs, ih]
    all_goals simp [TemplateGate.instantiate, tCount, tCost, ECDSAAdd.toffoliCount, Nat.mul_add, ih]

theorem literal_coherent (p : ECDSAAdd.Program) (Valid : BasisState → Prop)
    (result : BasisState → BasisState)
    (hrun : ∀ s, Valid s → ∀ m, ECDSAAdd.run p m ⟨false, s⟩ = ⟨false, result s⟩) :
    CoherentlyImplementsOn (literalSource p) (Finsupp.lmapDomain ℂ ℂ result) Valid := by
  let program := Bridge.translate (literalT (n := 1) p) 0
  let read : ConstantBit 1 → Bool := fun _ => false
  let history : Fin 0 → Bool := Fin.elim0
  have hr := literal_run p 0 read history
  change (program.instantiate read history).run = _ at hr
  refine ⟨(literalSource p).run.map (fun _ => Bridge.invSqrtTwo ^ ECDSAAdd.measurementCount p),
    ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro b hb s hs
    rw [← hr] at hb
    have h := Bridge.translate_branch read (literalT p) (Bridge.static_lit p) 0 history b hb
      ⟨false, s⟩
    have hib : Bridge.instB read (literalT (n := 1) p) = p := Bridge.instB_lit read p
    rw [Bridge.signedKet_false, hib, literal_meas, hrun s hs b.history,
      Bridge.signedKet_false] at h
    simpa [ket] using h
  · rw [List.map_map]
    have hcf : (Complex.normSq ∘ fun _ : InstrumentBranch =>
        Bridge.invSqrtTwo ^ ECDSAAdd.measurementCount p) =
        fun _ => ((1 : ℝ) / 2) ^ ECDSAAdd.measurementCount p := by
      funext b
      rw [Function.comp_apply, map_pow, Bridge.normSq_invSqrtTwo]
    rw [hcf, List.map_const', List.sum_replicate, ← hr, Bridge.straight_run_length]
    simp only [literal_meas, Nat.sub_zero, Nat.zero_add, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num

abbrev ModLayout := ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout

def CoreValid (K : ModLayout) (p : Nat) (s : BasisState) : Prop :=
  regValue K.src s < p ∧ regValue K.out s < p ∧
    Clean (K.carry ++ [K.high, K.cin, K.flag]) s

theorem regValue_wireValues (ws : List Wire) (s : BasisState) :
    regValue ws s = boolWordToNat (wireValues ws s) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => cases hs : s w <;> simp [regValue, wireValues, boolWordToNat, hs, ih]

theorem tableAddressValue_congr (bits : List Wire) (s t : BasisState)
    (h : ∀ w ∈ bits, s w = t w) : tableAddressValue bits s = tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    rw [tableAddressValue, tableAddressValue, h w (by simp),
      ih (by intro v hv; exact h v (by simp [hv]))]

/-! Concrete 15-bit experiment on the exact recovery-constant layout. -/

def probeRows (label : Nat) : Fin 32768 := ⟨label % 32768, Nat.mod_lt _ (by decide)⟩

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

/-- A table-bit-controlled target in a combined lookup leaf. -/
structure LookupPort (n : Nat) where
  ref : Nat → ConstantBit n
  value : Bool
  target : Wire

def portTargets {n : Nat} (ports : List (LookupPort n)) : List Wire :=
  ports.map LookupPort.target

def portMask {n : Nat} (read : ConstantBit n → Bool) (ports : List (LookupPort n))
    (address : Nat) : List Wire :=
  tableBitsMask (portTargets ports) (ports.map fun p => decide (read (p.ref address) = p.value))

def portLeaf {n : Nat} (ports : List (LookupPort n)) (address : Nat) (root : Wire) :
    List (TemplateGate n) :=
  ports.map fun p => .whenBit (p.ref address) p.value (.CX root p.target)

theorem portLeaf_source {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (address : Nat) (root : Wire) :
    (portLeaf ports address root).flatMap (TemplateGate.instantiate read) =
      tableXorGates root (portMask read ports address) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    simp only [portLeaf, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    by_cases h : read (p.ref address) = p.value <;>
      simp [TemplateGate.instantiate, portMask, portTargets, tableBitsMask, tableXorGates, h]

def portOps {n : Nat} (ports : List (LookupPort n)) (bits paths : List Wire)
    (root : Wire) : List (LookupOp n) :=
  unaryLookupOps (portLeaf ports) (tableAddressTree bits 0 1) root paths

theorem portOps_circuit {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (bits paths : List Wire) (root : Wire) :
    lookupCircuit read (portOps ports bits paths root) =
      tableLookupProgram (portMask read ports) bits root paths := by
  rw [portOps, unaryLookupOps_circuit]
  simp only [portLeaf_source]
  rfl

theorem portOps_measurements {n : Nat} (ports : List (LookupPort n))
    (bits paths : List Wire) (root : Wire) (hl : bits.length ≤ paths.length)
    (hn : (root :: bits ++ paths).Nodup) :
    lookupMeasurements (portOps ports bits paths root) = 2 ^ bits.length - 1 := by
  rw [portOps, unaryLookupOps_measurements _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ hl hn)]
  have h := tableAddressTree_nodes bits 0 1
  omega

theorem portProgram_run {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (bits paths : List Wire) (root start : Nat)
    (history : Fin start → Bool) :
    ((lookupProgram n (portOps ports bits paths root) start).instantiate read history).run =
      (tableLookupProgram (portMask read ports) bits root paths).run := by
  rw [lookupProgram_run, portOps_circuit]

theorem portProgram_tCount {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (bits paths : List Wire) (root start : Nat)
    (history : Fin start → Bool) (hl : bits.length ≤ paths.length)
    (hn : (root :: bits ++ paths).Nodup) :
    ((lookupProgram n (portOps ports bits paths root) start).instantiate read history).tCount =
      7 * (2 ^ bits.length - 1) := by
  rw [lookupProgram_tCount, portOps_circuit]
  exact tableLookupProgram_tCount _ _ _ _ hl hn

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

/-- Literal measured segments alternate with address-controlled XOR masks. -/
inductive WInstr (n : Nat) where
  | literal (program : ECDSAAdd.Program)
  | lookup (control : Option Wire) (ports : List (LookupPort n))

abbrev WCode (n : Nat) := List (WInstr n)

def indexedPorts {n : Nat} : List Wire → (Nat → Nat → ConstantBit n) → Bool →
    List (LookupPort n)
  | [], _, _ => []
  | w :: ws, refs, value => ⟨fun a => refs a 0, value, w⟩ ::
      indexedPorts ws (fun a i => refs a (i+1)) value

def portTemplate {n : Nat} (control : Option Wire) (ports : List (LookupPort n))
    (address : Nat) : ECDSAAdd.ShorPort.Tmpl n :=
  ports.map fun p => .gated (p.ref address) p.value
    (match control with | some c => .CX c p.target | none => .X p.target)

@[simp] theorem portTemplate_nil {n : Nat} (control : Option Wire) (address : Nat) :
    portTemplate control ([] : List (LookupPort n)) address = [] := rfl

@[simp] theorem portTemplate_cons {n : Nat} (control : Option Wire) (p : LookupPort n)
    (ports : List (LookupPort n)) (address : Nat) :
    portTemplate control (p :: ports) address =
      .gated (p.ref address) p.value
        (match control with | some c => .CX c p.target | none => .X p.target) ::
      portTemplate control ports address := rfl

def WInstr.specialize {n : Nat} (address : Nat) : WInstr n → ECDSAAdd.ShorPort.Tmpl n
  | .literal p => ECDSAAdd.ShorPort.Tmpl.lit p
  | .lookup control ports => portTemplate control ports address

def specialize {n : Nat} (code : WCode n) (address : Nat) : ECDSAAdd.ShorPort.Tmpl n :=
  code.flatMap (WInstr.specialize address)

def wLiteral {n : Nat} (p : ECDSAAdd.Program) : WCode n := [.literal p]

def wMask {n : Nat} (control : Option Wire) (targets : List Wire)
    (refs : Nat → Nat → ConstantBit n) (value : Bool := true) : WCode n :=
  [.lookup control (indexedPorts targets refs value)]

@[simp] theorem specialize_append {n : Nat} (xs ys : WCode n) (address : Nat) :
    specialize (xs ++ ys) address = specialize xs address ++ specialize ys address := by
  simp [specialize, List.flatMap_append]

@[simp] theorem specialize_literal {n : Nat} (p : ECDSAAdd.Program) (address : Nat) :
    specialize (wLiteral (n := n) p) address = ECDSAAdd.ShorPort.Tmpl.lit p := by
  simp [specialize, wLiteral, WInstr.specialize]

@[simp] theorem portTemplate_append {n : Nat} (control : Option Wire)
    (xs ys : List (LookupPort n)) (address : Nat) :
    portTemplate control (xs ++ ys) address =
      portTemplate control xs address ++ portTemplate control ys address := by
  simp [portTemplate]

theorem portTemplate_indexed_some {n : Nat} (c : Wire) (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (address : Nat) :
    portTemplate (some c) (indexedPorts ws refs true) address =
      ECDSAAdd.ShorPort.maskedT c ws (refs address) := by
  induction ws generalizing refs with
  | nil => rfl
  | cons w ws ih =>
    simp only [indexedPorts, portTemplate, List.map_cons, ECDSAAdd.ShorPort.maskedT]
    exact congrArg (List.cons _) (ih (fun a i => refs a (i+1)))

theorem portTemplate_indexed_none {n : Nat} (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (address : Nat) :
    portTemplate none (indexedPorts ws refs true) address =
      ECDSAAdd.ShorPort.xorT ws (refs address) := by
  induction ws generalizing refs with
  | nil => rfl
  | cons w ws ih =>
    simp only [indexedPorts, portTemplate, List.map_cons, ECDSAAdd.ShorPort.xorT]
    exact congrArg (List.cons _) (ih (fun a i => refs a (i+1)))

@[simp] theorem specialize_mask_some {n : Nat} (c : Wire) (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (address : Nat) :
    specialize (wMask (some c) ws refs) address =
      ECDSAAdd.ShorPort.maskedT c ws (refs address) := by
  simpa [specialize, wMask, WInstr.specialize] using portTemplate_indexed_some c ws refs address

open ECDSAAdd (Wire PointReg)
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout

def wPoint {n : Nat} (c : Wire) (r : PointReg) (fin : Nat → ConstantBit n)
    (xr yr : Nat → Nat → ConstantBit n) : WCode n :=
  [.lookup (some c) (⟨fin, false, r.finite⟩ ::
    indexedPorts r.x xr true ++ indexedPorts r.y yr true)]

@[simp] theorem specialize_point {n : Nat} (c : Wire) (r : PointReg)
    (fin : Nat → ConstantBit n) (xr yr : Nat → Nat → ConstantBit n) (address : Nat) :
    specialize (wPoint c r fin xr yr) address =
      ECDSAAdd.ShorPort.maskedPointT c r (fin address) (xr address) (yr address) := by
  simp [specialize, wPoint, WInstr.specialize, ECDSAAdd.ShorPort.maskedPointT,
    portTemplate_append, portTemplate_indexed_some]

def wPairXor {n : Nat} (L : ControlledPointLayout) (fin : Nat → ConstantBit n)
    (xr : Nat → Nat → ConstantBit n) : WCode n :=
  [.lookup none (⟨fin, false, L.point.finite⟩ :: indexedPorts L.point.x xr true)]

@[simp] theorem specialize_pairXor {n : Nat} (L : ControlledPointLayout)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n) (address : Nat) :
    specialize (wPairXor L fin xr) address =
      ECDSAAdd.ShorPort.pairXorT L (fin address) (xr address) := by
  simp [specialize, wPairXor, WInstr.specialize, ECDSAAdd.ShorPort.pairXorT, portTemplate_indexed_none]

def wShortXor {n : Nat} (L : ControlledPointLayout) (fin : Nat → ConstantBit n)
    (xr : Nat → Nat → ConstantBit n) (y0 : Nat → ConstantBit n) : WCode n :=
  [.lookup none (⟨fin, false, L.point.finite⟩ :: indexedPorts L.point.x xr true ++
    indexedPorts (L.point.y.take 1) (fun a _ => y0 a) true)]

@[simp] theorem specialize_shortXor {n : Nat} (L : ControlledPointLayout)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (y0 : Nat → ConstantBit n) (address : Nat) :
    specialize (wShortXor L fin xr y0) address =
      ECDSAAdd.ShorPort.shortXorT L (fin address) (xr address) (y0 address) := by
  simp [specialize, wShortXor, WInstr.specialize, ECDSAAdd.ShorPort.shortXorT, portTemplate_append, portTemplate_indexed_none]

def wBitTest {n : Nat} (w y t : Wire) (ref : Nat → ConstantBit n) : WCode n :=
  [.lookup none ([⟨ref, false, y⟩]), .literal ([.CCX w y t]), .lookup none ([⟨ref, false, y⟩])]

@[simp] theorem specialize_bitTest {n : Nat} (w y t : Wire)
    (ref : Nat → ConstantBit n) (address : Nat) :
    specialize (wBitTest w y t ref) address =
      ECDSAAdd.ShorPort.bitTestT w y t (ref address) := by
  rfl

def wPairTail {n : Nat} (y t₁ t₂ : Wire) (r₁ r₂ : Nat → ConstantBit n)
    (w : Wire) : WCode n := wBitTest w y t₁ r₁ ++ wBitTest w y t₂ r₂

@[simp] theorem specialize_pairTail {n : Nat} (y t₁ t₂ : Wire)
    (r₁ r₂ : Nat → ConstantBit n) (w : Wire) (address : Nat) :
    specialize (wPairTail y t₁ t₂ r₁ r₂ w) address =
      ECDSAAdd.ShorPort.pairTailT y t₁ t₂ (r₁ address) (r₂ address) w := by
  simp [wPairTail, ECDSAAdd.ShorPort.pairTailT]

def wZeroWith {n : Nat} (tail : Wire → WCode n) (c : Wire) : List ZeroBit → WCode n
  | [] => tail c
  | b :: bs => wLiteral (chainAnd c b.input b.work) ++ wZeroWith tail b.work bs ++
      wLiteral (chainErase c b.input b.work)

theorem specialize_zeroWith {n : Nat} (tail : Wire → WCode n)
    (tailT : Wire → ECDSAAdd.ShorPort.Tmpl n) (address : Nat)
    (h : ∀ w, specialize (tail w) address = tailT w) (c : Wire) (bs : List ZeroBit) :
    specialize (wZeroWith tail c bs) address = ECDSAAdd.ShorPort.zeroWithT tailT c bs := by
  induction bs generalizing c with
  | nil => exact h c
  | cons b bs ih => simp [wZeroWith, ECDSAAdd.ShorPort.zeroWithT, ih]

def wPairEqual {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (r₁ r₂ : Nat → ConstantBit n) : WCode n :=
  wPairXor L fin xr ++ wZeroWith (wPairTail (yLow L) t₁ t₂ r₁ r₂) L.control (pairPorts L) ++
    wPairXor L fin xr

@[simp] theorem specialize_pairEqual {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (r₁ r₂ : Nat → ConstantBit n) (address : Nat) :
    specialize (wPairEqual L t₁ t₂ fin xr r₁ r₂) address =
      ECDSAAdd.ShorPort.pairEqualT L t₁ t₂ (fin address) (xr address) (r₁ address) (r₂ address) := by
  simp [wPairEqual, ECDSAAdd.ShorPort.pairEqualT,
    specialize_zeroWith _ _ address (fun w => specialize_pairTail _ _ _ _ _ w address)]

def wShortEqual {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (y0 : Nat → ConstantBit n) : WCode n :=
  wShortXor L fin xr y0 ++
    wLiteral (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
    wShortXor L fin xr y0

@[simp] theorem specialize_shortEqual {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (y0 : Nat → ConstantBit n) (address : Nat) :
    specialize (wShortEqual L c t fin xr y0) address =
      ECDSAAdd.ShorPort.shortEqualT L c t (fin address) (xr address) (y0 address) := by
  simp [wShortEqual, ECDSAAdd.ShorPort.shortEqualT]

def wConstAdd {n : Nat} (L : ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) : WCode n :=
  wMask (some L.core.generic) (L.recoveryConstant r).src refs ++
    wLiteral ((L.recoveryConstant r).program SquareReduction.c ECDSAAdd.p) ++
    wMask (some L.core.generic) (L.recoveryConstant r).src refs

@[simp] theorem specialize_constAdd {n : Nat} (L : ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) (address : Nat) :
    specialize (wConstAdd L r refs) address =
      ECDSAAdd.ShorPort.constAddT L r (refs address) := by
  simp [wConstAdd, ECDSAAdd.ShorPort.constAddT]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 3000000

def wFields {n : Nat} (rows : Nat → Fin n) (f : PointField) :
    Nat → Nat → ConstantBit n := fun a => ECDSAAdd.ShorPort.fieldBits (rows a) f

def wBit {n : Nat} (rows : Nat → Fin n) (f : PointField) (i : Nat := 0) :
    Nat → ConstantBit n := fun a => ECDSAAdd.ShorPort.bitRef (rows a) f i

def wRecovery {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral (pointRecoveryReflection L) ++ wConstAdd L L.point.x (wFields rows .x) ++
    wLiteral (pointDialogConstantAdd L L.point.x 1) ++
    wConstAdd L L.point.y (wFields rows .negY)

/-! Arithmetic adapter for the public ecdsa.fail Lean lineage at a2af67c,
submission 41de28b3-7fbc-41b2-874a-9d2ac1b899ca, ercumentyildirim and contributors,
Apache-2.0. Selector-free arithmetic and square are combined with protected-field
constant loading and literal infinity repair. The clean-reset helper supports
record-schedule compatibility without extra T or wires. -/


namespace Arith
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run Frontier.arithS Frontier.SquareOB5.program
  pointDialogConstantAdd pointRecoveryReflection recoveryStageS
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Tmpl.lit Frontier.SelGeneric5.program Frontier.fastConstAdd Frontier.fastConstNeg Frontier.pfix

/-- Public selector-free arithmetic and square, with protected-field constant runs. -/
def core (L : ControlledPointLayout) (cx cy : ECDSAAdd.Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  Frontier.arithS L false ++ Frontier.SquareOB5.program L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++ Frontier.arithS L true ++
  recoveryStageS L cx cy

/-- The literal five repair keeps the divisor nonzero on infinity. -/
def genericS (L : ControlledPointLayout) (cx cy : ECDSAAdd.Fp) : Program :=
  Frontier.zrep L ++ core L cx cy ++ Frontier.zrep L

theorem core_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : ECDSAAdd.Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (core L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := Frontier.arith3F_step L hw hn (X-cx) (Y-cy) true base false (sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [Bool.false_eq_true,if_false,ha] at h3
  have h4 := Frontier.GenericOB5.square_step L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := Frontier.arith3F_step L hw hn d a true base true hd
  simp only [if_true] at h6
  have recovery := recoveryStageS_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [core,List.append_assoc] using h

theorem core_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : ECDSAAdd.Fp) (base : BasisState) (hX0 : X≠0) :
    Triple (PointDialogValues L X Y false base) (core L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := Frontier.arith3F_step L hw hn X Y false base false hX0
  have h4 := Frontier.GenericOB5.square_step L hw hn X (Y/X) false base
  have h5 := dialogStep_addX L hw hn X (Y/X) false base (3*cx)
  have h6 := Frontier.arith3F_step L hw hn X (Y/X) false base true hX0
  have recovery := recoveryStageS_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  rw [div_mul_cancel₀ Y hX0] at h6
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [core,List.append_assoc] using h

theorem boundary_genericS (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (genericS L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := Frontier.finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := Frontier.zrep_step L hw hn 0 5 0 false s.basis
      (by rw [hfin,Frontier.finFive_val]; rfl)
    have mid := core_false L hw hn 5 0 cx cy s.basis Frontier.finFive_ne_zero
    have z2 := Frontier.zrep_step L hw hn 5 0 0 false s.basis
      (by rw [hfin,Frontier.finFive_val]; rfl)
    have all : Triple (PointDialogValues L 0 0 false s.basis) (genericS L cx cy)
        (PointDialogValues L 0 0 false s.basis) := by
      simpa only [genericS,List.append_assoc] using (z1.seq mid).seq z2
    obtain ⟨phase,hv⟩ := all s m values
    refine ⟨phase,?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr
      ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _ => rfl⟩
      have z1 := Frontier.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := core_false L hw hn x y cx cy s.basis (Frontier.curve_x_ne_zero hr)
      have z2 := Frontier.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have all : Triple (PointDialogValues L x y false s.basis) (genericS L cx cy)
          (PointDialogValues L x y false s.basis) := by
        simpa only [genericS,List.append_assoc] using (z1.seq mid).seq z2
      obtain ⟨phase,hv⟩ := all s m values
      refine ⟨phase,?_⟩
      simp only [hG,Bool.false_eq_true,if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr
        ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _ => rfl⟩
      have z1 := Frontier.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := core_true L hw hn x y cx cy s.basis den.1 den.2
      have z2 := Frontier.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy)
        (genericY x y cx cy) true s.basis (by rw [hfin]; simp)
      have all : Triple (PointDialogValues L x y true s.basis) (genericS L cx cy)
          (PointDialogValues L (genericX x y cx cy) (genericY x y cx cy) true s.basis) := by
        simpa only [genericS,List.append_assoc] using (z1.seq mid).seq z2
      obtain ⟨phase,hv⟩ := all s m values
      refine ⟨phase,?_⟩
      simp only [hG,if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr
        ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

theorem genericS_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : ECDSAAdd.Fp) : ECDSAAdd.toffoliCount (genericS L cx cy) = 2154570 ∧
      ECDSAAdd.measurementCount (genericS L cx cy) = 1503131 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have ar := Frontier.arithS_counts L
  have sq := Frontier.SquareOB5.counts L hw
  have recov := recoveryStageS_counts L hw cx cy
  have z := Frontier.zrep_counts L
  simp only [genericS,core,toffoliCount_append,measurementCount_append,(a _).1,(a _).2,
    (b _).1,(b _).2,ar.1,ar.2.1,ar.2.2.1,ar.2.2.2,sq.1,sq.2,recov.1,recov.2,z.1,z.2]
  norm_num


def genericT {n : Nat} (L : ControlledPointLayout) (row : Fin n) : Tmpl n :=
  Tmpl.lit (Frontier.zrep L) ++
  constAddT L L.point.x (fieldBits row .negX) ++
  constAddT L L.point.y (fieldBits row .negY) ++
  Tmpl.lit (Frontier.arithS L false) ++ Tmpl.lit (Frontier.SquareOB5.program L) ++
  constAddT L L.point.x (fieldBits row .tripleX) ++
  Tmpl.lit (Frontier.arithS L true) ++ recoveryT L row ++ Tmpl.lit (Frontier.zrep L)

theorem bits_of {n : Nat} {read : CBit n → Bool} {row : Fin n} {P : Point}
    (h : RowReads read row P) (f : Field) (k : Nat)
    (hk : ShorECDLP.Challenge.fieldValue (toA P) f = k) :
    ∀ i < 256, read (fieldBits row f i) = k.testBit i := by
  intro i hi
  rw [fieldBits,h.bit f i hi,hk]

theorem genericT_inst {n : Nat} {read : CBit n → Bool} {row : Fin n}
    (L : ControlledPointLayout) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h : RowReads read row (.some hc)) :
    (genericT L row).instantiate read = genericS L cx cy := by
  have ax := constAddT_inst read L L.point.x _ (-cx) (bits_of h .negX _ (field_some_negX hc))
  have ay := constAddT_inst read L L.point.y _ (-cy) (bits_of h .negY _ (field_some_negY hc))
  have a3 := constAddT_inst read L L.point.x _ (3*cx) (bits_of h .tripleX _ (field_some_tripleX hc))
  have ac := constAddT_inst read L L.point.x _ cx (bits_of h .x _ (field_some_x hc))
  simp only [genericT,recoveryT,genericS,core,recoveryStageS,Tmpl.instantiate_append,
    Tmpl.instantiate_lit,ax,ay,a3,ac,List.append_assoc]

theorem arith_in_selected (L : ControlledPointLayout) (multiply : Bool)
    (i : Instr) (hi : i ∈ Frontier.arithS L multiply) :
    i ∈ Frontier.SelGeneric5.program L 0 0 := by
  cases multiply <;>
    simp only [Frontier.SelGeneric5.program,Frontier.SelGeneric5.farithS,List.mem_append] <;> tauto

theorem square_in_selected (L : ControlledPointLayout) (i : Instr)
    (hi : i ∈ Frontier.SquareOB5.program L) : i ∈ Frontier.SelGeneric5.program L 0 0 := by
  simp only [Frontier.SelGeneric5.program,List.mem_append]
  tauto

theorem genericS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : ECDSAAdd.Fp) : GatePhysical (genericS L cx cy) := by
  have hp := Frontier.SelGeneric5.program_physical L hw hn 0 0
  have ar (multiply : Bool) : GatePhysical (Frontier.arithS L multiply) :=
    fun i hi => hp i (arith_in_selected L multiply i hi)
  have sq : GatePhysical (Frontier.SquareOB5.program L) :=
    fun i hi => hp i (square_in_selected L i hi)
  have a k := pointDialogConstantAdd_physical L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_physical L hw hn L.point.y (Or.inr rfl) k
  have re := recoveryStageS_physical L hw hn cx cy
  have z := Frontier.zrep_physical L hn
  simp only [genericS,core,gatePhysical_append]
  exact ⟨⟨z,⟨⟨⟨⟨⟨a _,b _⟩,ar false⟩,sq⟩,a _⟩,ar true⟩,re⟩,z⟩

theorem genericS_slots (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : ECDSAAdd.Fp) : ECDSAAdd.Challenge.gateSlots (genericS L cx cy) ≤ 49500000 := by
  have g := Frontier.SelGeneric5.program_gateSlots_le L hw hn cx cy
  simp only [Frontier.SelGeneric5.program,Frontier.SelGeneric5.farithS,ECDSAAdd.Challenge.gateSlots_append] at g
  have a := Baselines.recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (-cx)
  have b := Baselines.recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  have c := Baselines.recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (3*cx)
  have r := recoveryStageS_gateSlots_le L hw cx cy
  have z := Frontier.zrep_gateSlots_le L hw
  simp only [genericS,core,ECDSAAdd.Challenge.gateSlots_append]
  omega

theorem inventory_used (L : ControlledPointLayout) (hw : L.Widths) :
    (Frontier.OB5Support.genericSites L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  simp only [Frontier.OB5Support.genericSites,List.mem_toFinset,List.mem_append,List.mem_singleton] at hq
  rcases hq with (hq | hq) | hq
  · exact List.mem_toFinset.mpr (by simp [dialogUsedWires,hq])
  · subst q
    exact List.mem_toFinset.mpr (by simp [dialogUsedWires,inPlaceFlags])
  · obtain ⟨i,hi,rfl⟩ := Frontier.OB5Support.pool_index L q hq
    have hl : i < 2613 := by rcases hi with h | h | h | h <;> omega
    have hm := Frontier.Square5Placement.pool_member L hw i hl
    exact List.mem_toFinset.mpr (by simp [dialogUsedWires,hm])

theorem arith_wires_selected (L : ControlledPointLayout) (multiply : Bool) :
    ECDSAAdd.wires (Frontier.arithS L multiply) ⊆
      ECDSAAdd.wires (Frontier.SelGeneric5.program L 0 0) := by
  cases multiply <;> intro q hq <;>
    simp only [Frontier.SelGeneric5.program,Frontier.SelGeneric5.farithS,ECDSAAdd.wires_append,
      Finset.mem_union] <;> tauto

theorem square_wires_selected (L : ControlledPointLayout) :
    ECDSAAdd.wires (Frontier.SquareOB5.program L) ⊆
      ECDSAAdd.wires (Frontier.SelGeneric5.program L 0 0) := by
  intro q hq
  simp only [Frontier.SelGeneric5.program,ECDSAAdd.wires_append,Finset.mem_union]
  tauto

theorem genericS_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : ECDSAAdd.Fp) : ECDSAAdd.wires (genericS L cx cy) ⊆ L.dialogUsedWires.toFinset := by
  have old := ECDSAAdd.ShorPort.finiteS_used L hw hn (0 : Point) cx cy
  have selected := (Frontier.SelGeneric5.program_support L hw hn 0 0).trans (inventory_used L hw)
  have ar (multiply : Bool) := (arith_wires_selected L multiply).trans selected
  have sq := (square_wires_selected L).trans selected
  have z : ECDSAAdd.wires (Frontier.zrep L) ⊆ L.dialogUsedWires.toFinset := by
    intro q hq
    rcases Frontier.zrep_wires L q hq with rfl | hq
    · exact List.mem_toFinset.mpr (by simp [dialogUsedWires,PointAddLayout.pointWires])
    · exact List.mem_toFinset.mpr (by simp [dialogUsedWires,PointAddLayout.pointWires,hq])
  simp only [ECDSAAdd.ShorPort.finiteS,ECDSAAdd.ShorPort.genericS,ECDSAAdd.wires_append,
    Finset.union_subset_iff] at old
  simp only [genericS,core,ECDSAAdd.wires_append,Finset.union_subset_iff]
  have a := ar false
  have b := ar true
  tauto

open ECDSAAdd.RecordedQuantum

def padding (q : Wire) (n : Nat) : Program := List.replicate n (.measureX q ([]) ([]))

theorem zero_reset (q : Wire) (b : Bool) (s : ECDSAAdd.State) (h : s.basis q = false) :
    measureAndCorrect q ([]) ([]) b s = s := by
  have he : writeBit s.basis q false = s.basis := by
    funext w
    by_cases hw : w = q
    · subst w; simp [writeBit,h]
    · simp [writeBit,hw]
  simp only [measureAndCorrect,h,Bool.and_false,Bool.xor_false,ite_self,correct,he]

theorem padding_run (q : Wire) (n : Nat) (s : ECDSAAdd.State) (m : List Bool) (h : s.basis q = false) :
    ECDSAAdd.run (padding q n) m s = s := by
  induction n generalizing m with
  | zero => simp only [padding,List.replicate_zero,ECDSAAdd.run]
  | succ n ih =>
    rw [padding,List.replicate_succ,ECDSAAdd.run,zero_reset q (m.headD false) s h]
    exact ih m.tail

theorem padding_counts (q : Wire) (n : Nat) :
    ECDSAAdd.toffoliCount (padding q n) = 0 ∧ ECDSAAdd.measurementCount (padding q n) = n := by
  induction n with
  | zero => simp [padding,ECDSAAdd.toffoliCount,ECDSAAdd.measurementCount]
  | succ n ih =>
    simp only [padding,List.replicate_succ,ECDSAAdd.toffoliCount,ECDSAAdd.measurementCount] at ih ⊢
    constructor <;> omega

theorem padding_slots (q : Wire) (n : Nat) : ECDSAAdd.Challenge.gateSlots (padding q n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [padding,List.replicate_succ,ECDSAAdd.Challenge.gateSlots,ECDSAAdd.Challenge.instructionSlots,
      List.length_nil,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem padding_physical (q : Wire) (n : Nat) : GatePhysical (padding q n) := by
  intro i hi
  have he := List.eq_of_mem_replicate hi
  subst i
  simp [PhysicalInstr]

theorem padding_support (q : Wire) (n : Nat) : ECDSAAdd.wires (padding q n) ⊆ {q} := by
  induction n with
  | zero => simpa only [padding,List.replicate_zero,ECDSAAdd.wires] using Finset.empty_subset ({q} : Finset Wire)
  | succ n ih =>
    simp only [padding,List.replicate_succ,ECDSAAdd.wires,Instr.wires,correctionWires,Finset.union_empty]
    exact Finset.union_subset (Finset.Subset.refl _) ih

theorem padding_boundary (L : ControlledPointLayout) (hw : L.Widths)
    (R : Point) (b : Bool) (n : Nat) :
    Triple (PointDialogBoundary L R b (fun _ => false)) (padding (L.core.poolWire 0) n)
      (PointDialogBoundary L R b (fun _ => false)) := by
  intro s m hs
  have hz : s.basis (L.core.poolWire 0) = false :=
    (regValue_zero _ _).mp hs.clean _ (Frontier.Square5Placement.pool_member L hw 0 (by decide))
  rw [padding_run _ _ _ _ hz]
  exact ⟨rfl,hs⟩

end
end Arith

def wGenericLegacy {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wConstAdd L L.point.x (wFields rows .negX) ++
  wConstAdd L L.point.y (wFields rows .negY) ++
  wLiteral (MappedCompressed.pointCompressedArithmetic L false) ++
  wLiteral (CompressedPointSquare.computableProgram L) ++
  wConstAdd L L.point.x (wFields rows .tripleX) ++
  wLiteral (MappedCompressed.pointCompressedArithmetic L true) ++ wRecovery L rows

def wGeneric {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral (ECDSAAdd.Frontier.zrep L) ++
  wConstAdd L L.point.x (wFields rows .negX) ++
  wConstAdd L L.point.y (wFields rows .negY) ++
  wLiteral (ECDSAAdd.Frontier.arithS L false) ++
  wLiteral (ECDSAAdd.Frontier.SquareOB5.program L) ++
  wConstAdd L L.point.x (wFields rows .tripleX) ++
  wLiteral (ECDSAAdd.Frontier.arithS L true) ++ wRecovery L rows ++
  wLiteral (ECDSAAdd.Frontier.zrep L)

@[simp] theorem specialize_recovery {n : Nat} (L : ControlledPointLayout)
    (rows : Nat → Fin n) (address : Nat) :
    specialize (wRecovery L rows) address = ECDSAAdd.ShorPort.recoveryT L (rows address) := by
  simp [wRecovery, ECDSAAdd.ShorPort.recoveryT, wFields]

@[simp] theorem specialize_generic {n : Nat} (L : ControlledPointLayout)
    (rows : Nat → Fin n) (address : Nat) :
    specialize (wGeneric L rows) address = Arith.genericT L (rows address) := by
  simp [wGeneric,Arith.genericT,wFields,List.append_assoc]

def traversals {n : Nat} : WCode n → Nat
  | [] => 0
  | .literal _ :: code => traversals code
  | .lookup _ _ :: code => 1 + traversals code

@[simp] theorem traversals_append {n : Nat} (xs ys : WCode n) :
    traversals (xs ++ ys) = traversals xs + traversals ys := by
  induction xs with
  | nil => simp [traversals]
  | cons i xs ih => cases i <;> simp [traversals, ih, Nat.add_assoc]

@[simp] theorem traversals_literal {n : Nat} (p : ECDSAAdd.Program) :
    traversals (wLiteral (n := n) p) = 0 := rfl

@[simp] theorem traversals_mask {n : Nat} (c : Option Wire) (targets : List Wire)
    (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    traversals (wMask c targets refs v) = 1 := rfl

@[simp] theorem traversals_point {n : Nat} (c : Wire) (r : ECDSAAdd.PointReg)
    (fin : Nat → ConstantBit n) (xr yr : Nat → Nat → ConstantBit n) :
    traversals (wPoint c r fin xr yr) = 1 := rfl

@[simp] theorem traversals_pairXor {n : Nat} (L : ControlledPointLayout)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n) :
    traversals (wPairXor L fin xr) = 1 := rfl

@[simp] theorem traversals_shortXor {n : Nat} (L : ControlledPointLayout)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (y0 : Nat → ConstantBit n) : traversals (wShortXor L fin xr y0) = 1 := rfl

@[simp] theorem traversals_bitTest {n : Nat} (w y t : Wire)
    (ref : Nat → ConstantBit n) : traversals (wBitTest w y t ref) = 2 := rfl

@[simp] theorem traversals_pairTail {n : Nat} (y t₁ t₂ : Wire)
    (r₁ r₂ : Nat → ConstantBit n) (w : Wire) :
    traversals (wPairTail y t₁ t₂ r₁ r₂ w) = 4 := rfl

theorem traversals_zeroWith {n : Nat} (tail : Wire → WCode n) (k : Nat)
    (h : ∀ w, traversals (tail w) = k) (c : Wire) (bs : List ZeroBit) :
    traversals (wZeroWith tail c bs) = k := by
  induction bs generalizing c with
  | nil => exact h c
  | cons b bs ih => simp [wZeroWith, ih]

@[simp] theorem traversals_shortEqual {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (y0 : Nat → ConstantBit n) : traversals (wShortEqual L c t fin xr y0) = 2 := by
  simp [wShortEqual]

@[simp] theorem traversals_constAdd {n : Nat} (L : ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) : traversals (wConstAdd L r refs) = 2 := by
  simp [wConstAdd]

@[simp] theorem traversals_recovery {n : Nat} (L : ControlledPointLayout)
    (rows : Nat → Fin n) : traversals (wRecovery L rows) = 4 := by simp [wRecovery]

@[simp] theorem traversals_generic {n : Nat} (L : ControlledPointLayout)
    (rows : Nat → Fin n) : traversals (wGeneric L rows) = 10 := by simp [wGeneric]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

def lookupRoot (root : Wire) (control : Option Wire) : Wire := control.getD root

def codeRecords {n : Nat} (bits paths : List Wire) (root : Wire) : WCode n → Nat
  | [] => 0
  | .literal p :: code => ECDSAAdd.measurementCount p + codeRecords bits paths root code
  | .lookup control ports :: code =>
      lookupMeasurements (portOps ports bits paths (lookupRoot root control)) +
        codeRecords bits paths root code

/-- Real straight-line compilation with the record cursor advanced at every lookup. -/
def compile {n : Nat} (bits paths : List Wire) (root : Wire) :
    (code : WCode n) → (start : Nat) → Straight n start (start + codeRecords bits paths root code)
  | [], start => .done
  | .literal p :: code, start => NaiveChallenge.castFinish (by
      simp [codeRecords, literal_meas]; omega)
      ((Bridge.translate (literalT p) start).append
        (compile bits paths root code (start + Bridge.tmplMeas (literalT p))))
  | .lookup control ports :: code, start => NaiveChallenge.castFinish (by
      simp [codeRecords]; omega)
      ((lookupProgram n (portOps ports bits paths (lookupRoot root control)) start).append
        (compile bits paths root code
          (start + lookupMeasurements (portOps ports bits paths (lookupRoot root control)))))

def source {n : Nat} (read : ConstantBit n → Bool) (bits paths : List Wire) (root : Wire) :
    WCode n → AdaptiveCircuit
  | [] => .done
  | .literal p :: code => (literalSource p).seq (source read bits paths root code)
  | .lookup control ports :: code =>
      (tableLookupProgram (portMask read ports) bits (lookupRoot root control) paths).seq
        (source read bits paths root code)

theorem compile_run {n : Nat} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (root : Wire) (code : WCode n) (start : Nat) (history : Fin start → Bool) :
    ((compile bits paths root code start).instantiate read history).run =
      (source read bits paths root code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p =>
      simp only [compile, NaiveChallenge.instantiate_castFinish, source]
      rw [append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, literal_run,
        ← AdaptiveCircuit.run_seq]
    | lookup control ports =>
      simp only [compile, NaiveChallenge.instantiate_castFinish, source]
      rw [append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, portProgram_run,
        ← AdaptiveCircuit.run_seq]

def literalRecords {n : Nat} : WCode n → Nat
  | [] => 0
  | .literal p :: code => ECDSAAdd.measurementCount p + literalRecords code
  | .lookup _ _ :: code => literalRecords code

def literalToffolis {n : Nat} : WCode n → Nat
  | [] => 0
  | .literal p :: code => ECDSAAdd.toffoliCount p + literalToffolis code
  | .lookup _ _ :: code => literalToffolis code

/-- Each guard may serve as lookup root, and the path bank is long enough for every traversal. -/
def LookupLayouts {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n) : Prop :=
  bits.length ≤ paths.length ∧ ∀ control ports, WInstr.lookup control ports ∈ code →
    (lookupRoot root control :: bits ++ paths).Nodup

theorem codeRecords_eq {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : LookupLayouts bits paths root code) :
    codeRecords bits paths root code =
      literalRecords code + traversals code * (2 ^ bits.length - 1) := by
  induction code with
  | nil => simp [codeRecords, literalRecords, traversals]
  | cons i code ih =>
    have htail : LookupLayouts bits paths root code :=
      ⟨hl.1, fun c p hp => hl.2 c p (List.mem_cons_of_mem _ hp)⟩
    cases i with
    | literal p => simp [codeRecords, literalRecords, traversals, ih htail, Nat.add_assoc]
    | lookup c p =>
      rw [codeRecords, portOps_measurements p bits paths _ hl.1 (hl.2 c p (by simp)), ih htail]
      simp [literalRecords, traversals, Nat.add_mul]
      omega

theorem compile_tCount {n : Nat} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (root : Wire) (code : WCode n) (hl : LookupLayouts bits paths root code)
    (start : Nat) (history : Fin start → Bool) :
    ((compile bits paths root code start).instantiate read history).tCount =
      7 * literalToffolis code + 7 * traversals code * (2 ^ bits.length - 1) := by
  induction code generalizing start with
  | nil => simp [compile, Straight.instantiate, AdaptiveCircuit.tCount, literalToffolis, traversals]
  | cons i code ih =>
    have htail : LookupLayouts bits paths root code :=
      ⟨hl.1, fun c p hp => hl.2 c p (List.mem_cons_of_mem _ hp)⟩
    cases i with
    | literal p =>
      simp only [compile, NaiveChallenge.instantiate_castFinish]
      rw [append_tCount_fixed _ _ _ _ _ (fun h => ih htail _ h), literal_program_tCount]
      simp [literalToffolis, traversals]
      ring
    | lookup c p =>
      simp only [compile, NaiveChallenge.instantiate_castFinish]
      rw [append_tCount_fixed _ _ _ _ _ (fun h => ih htail _ h),
        portProgram_tCount _ _ _ _ _ _ _ hl.1 (hl.2 c p (by simp))]
      simp [literalToffolis, traversals]
      ring

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 3000000

theorem portTemplate_counts {n : Nat} (read : ConstantBit n → Bool) (control : Option Wire)
    (ports : List (LookupPort n)) (address : Nat) :
    ECDSAAdd.toffoliCount ((portTemplate control ports address).instantiate read) = 0 ∧
      ECDSAAdd.measurementCount ((portTemplate control ports address).instantiate read) = 0 := by
  induction ports with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ports ih =>
    simp only [portTemplate_cons, ECDSAAdd.ShorPort.Tmpl.instantiate_cons,
      ECDSAAdd.ShorPort.TInstr.instantiate]
    split
    · cases control <;> simpa [ECDSAAdd.toffoliCount, ECDSAAdd.measurementCount] using ih
    · exact ih

theorem specialize_counts {n : Nat} (read : ConstantBit n → Bool) (code : WCode n)
    (address : Nat) :
    ECDSAAdd.toffoliCount ((specialize code address).instantiate read) = literalToffolis code ∧
      ECDSAAdd.measurementCount ((specialize code address).instantiate read) = literalRecords code := by
  induction code with
  | nil => exact ⟨rfl, rfl⟩
  | cons i code ih =>
    simp only [specialize, List.flatMap_cons, ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      ECDSAAdd.toffoliCount_append, ECDSAAdd.measurementCount_append] at ih ⊢
    cases i with
    | literal p =>
      simp [WInstr.specialize, ECDSAAdd.ShorPort.Tmpl.instantiate_lit,
        literalToffolis, literalRecords, ih.1, ih.2]
    | lookup c p =>
      have h := portTemplate_counts read c p address
      simpa [WInstr.specialize, h.1, h.2, literalToffolis, literalRecords] using ih

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

theorem portTemplate_inst_some {n : Nat} (read : ConstantBit n → Bool) (c : Wire)
    (ports : List (LookupPort n)) (address : Nat) :
    (portTemplate (some c) ports address).instantiate read =
      (portMask read ports address).map (ECDSAAdd.Instr.CX c) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    simp only [portTemplate_cons, ECDSAAdd.ShorPort.Tmpl.instantiate_cons,
      ECDSAAdd.ShorPort.TInstr.instantiate]
    rw [ih]
    by_cases h : read (p.ref address) = p.value <;>
      simp [portMask, portTargets, tableBitsMask, h]

theorem portTemplate_inst_none {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (address : Nat) :
    (portTemplate none ports address).instantiate read =
      (portMask read ports address).map ECDSAAdd.Instr.X := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    simp only [portTemplate_cons, ECDSAAdd.ShorPort.Tmpl.instantiate_cons,
      ECDSAAdd.ShorPort.TInstr.instantiate]
    rw [ih]
    by_cases h : read (p.ref address) = p.value <;>
      simp [portMask, portTargets, tableBitsMask, h]

theorem merge_tableXorGates (c d : Wire) (ws : List Wire) (hcd : c ≠ d) (hc : c ∉ ws) (hd : d ∉ ws)
    (hn : ws.Nodup) (s : BasisState) :
    Classical.run (tableXorGates c ws ++ tableXorGates d ws) s =
      Classical.run ([.CX c d] ++ tableXorGates d ws ++ [.CX c d]) s := by
  simp only [Classical.run_append, Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [run_tableXorGates c ws s hn hc, run_tableXorGates d ws _ hn hd,
      run_tableXorGates d ws _ hn hd]
  funext w
  by_cases wd : w = d
  · subst w
    simp [tableXorState, upd, hcd, hc, hd, Bool.xor_comm]
  · simp [tableXorState, upd, wd, hd, Bool.xor_comm,
      Bool.and_xor_distrib_right]

theorem run_cxMask (q : Wire) (selected : List Wire) (m : List Bool) (st : ECDSAAdd.State) :
    ECDSAAdd.run (selected.map (ECDSAAdd.Instr.CX q)) m st =
      ⟨st.phase, Classical.run (tableXorGates q selected) st.basis⟩ := by
  induction selected generalizing st with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, ECDSAAdd.run, tableXorGates, Classical.run_cons, Classical.applyGate]
    rw [ih]
    congr 2
    exact (Bridge.upd_eq_update st.basis w (st.basis w ^^ st.basis q)).symm

theorem mapCX_records (q : Wire) (ws : List Wire) :
    ECDSAAdd.measurementCount (ws.map (ECDSAAdd.Instr.CX q)) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [ECDSAAdd.measurementCount] using ih

theorem merge_cx_masks (c d : Wire) (ws : List Wire) (hcd : c ≠ d)
    (hc : c ∉ ws) (hd : d ∉ ws) (hn : ws.Nodup) (st : ECDSAAdd.State)
    (m : List Bool) :
    ECDSAAdd.run (ws.map (ECDSAAdd.Instr.CX c) ++ ws.map (ECDSAAdd.Instr.CX d)) m st =
      ECDSAAdd.run ([.CX c d] ++ ws.map (ECDSAAdd.Instr.CX d) ++ [.CX c d]) m st := by
  simp only [ECDSAAdd.run_append, mapCX_records, List.take_zero, List.drop_zero,
    ECDSAAdd.measurementCount, run_cxMask, ECDSAAdd.run]
  simp only [← Bridge.upd_eq_update]
  have h := merge_tableXorGates c d ws hcd hc hd hn st.basis
  simp only [Classical.run_append, Classical.run_cons, Classical.run_nil, Classical.applyGate] at h
  exact congrArg (ECDSAAdd.State.mk st.phase) h

def constantTargets : List Wire → Nat → List Wire
  | [], _ => []
  | w :: ws, k => (if k % 2 = 1 then [w] else []) ++ constantTargets ws (k / 2)

theorem constantTargets_map (c : Wire) (ws : List Wire) (k : Nat) :
    ECDSAAdd.Arithmetic.maskedConstant c ws k =
      (constantTargets ws k).map (ECDSAAdd.Instr.CX c) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : k % 2 = 1 <;> simp [ECDSAAdd.Arithmetic.maskedConstant, constantTargets, h, ih]

theorem constantTargets_sublist (ws : List Wire) (k : Nat) : List.Sublist (constantTargets ws k) ws := by
  induction ws generalizing k with
  | nil => simp [constantTargets]
  | cons w ws ih =>
    by_cases h : k % 2 = 1
    · simpa [constantTargets, h] using (ih (k/2)).cons₂ w
    · simpa [constantTargets, h] using (ih (k/2)).cons w

theorem merge_constant_segments (c d : Wire) (a b e : List Wire) (ka kb ke : Nat)
    (hcd : c ≠ d) (hc : c ∉ a ++ b ++ e) (hd : d ∉ a ++ b ++ e)
    (hn : (a ++ b ++ e).Nodup) (st : ECDSAAdd.State) (m : List Bool) :
    ECDSAAdd.run ((ECDSAAdd.Arithmetic.maskedConstant c a ka ++
      ECDSAAdd.Arithmetic.maskedConstant c b kb ++ ECDSAAdd.Arithmetic.maskedConstant c e ke) ++
      (ECDSAAdd.Arithmetic.maskedConstant d a ka ++
      ECDSAAdd.Arithmetic.maskedConstant d b kb ++ ECDSAAdd.Arithmetic.maskedConstant d e ke)) m st =
      ECDSAAdd.run ([.CX c d] ++ (ECDSAAdd.Arithmetic.maskedConstant d a ka ++
      ECDSAAdd.Arithmetic.maskedConstant d b kb ++ ECDSAAdd.Arithmetic.maskedConstant d e ke) ++
      [.CX c d]) m st := by
  let ws := constantTargets a ka ++ constantTargets b kb ++ constantTargets e ke
  have hsub : List.Sublist ws (a ++ b ++ e) := by
    simpa [ws, List.append_assoc] using (constantTargets_sublist a ka).append ((constantTargets_sublist b kb).append (constantTargets_sublist e ke))
  have hnc : c ∉ ws := fun h => hc (hsub.subset h)
  have hnd : d ∉ ws := fun h => hd (hsub.subset h)
  have hwn : ws.Nodup := hsub.nodup hn
  have h := merge_cx_masks c d ws hcd hnc hnd hwn st m
  simpa only [constantTargets_map, ← List.map_append, ws] using h

theorem run_cxMask_eq_xMask (q : Wire) (selected : List Wire) (m : List Bool)
    (st : ECDSAAdd.State) (hq : q ∉ selected) (hv : st.basis q = true) :
    ECDSAAdd.run (selected.map (ECDSAAdd.Instr.CX q)) m st =
      ECDSAAdd.run (selected.map ECDSAAdd.Instr.X) m st := by
  induction selected generalizing st with
  | nil => rfl
  | cons w ws ih =>
    have hqw : q ≠ w := fun h => hq (by simp [h])
    have hqs : q ∉ ws := fun h => hq (by simp [h])
    simp only [List.map_cons, ECDSAAdd.run, hv, Bool.xor_true]
    exact ih _ hqs (by simp [ECDSAAdd.writeBit, hqw, hv])

/-- Specializing a combined leaf is exactly the corresponding classical XOR mask. -/
theorem portTemplate_run {n : Nat} (read : ConstantBit n → Bool) (control : Option Wire)
    (ports : List (LookupPort n)) (address : Nat) (root : Wire) (m : List Bool)
    (st : ECDSAAdd.State) (ht : (portTargets ports).Nodup)
    (hq : lookupRoot root control ∉ portTargets ports) (hv : st.basis root = true) :
    ECDSAAdd.run ((portTemplate control ports address).instantiate read) m st =
      ⟨st.phase, tableXorState (portMask read ports address)
        (st.basis (lookupRoot root control)) st.basis⟩ := by
  have hm := tableBitsMask_nodup (portTargets ports)
    (ports.map fun p => decide (read (p.ref address) = p.value)) ht
  have hqm : lookupRoot root control ∉ portMask read ports address :=
    fun h => hq (tableBitsMask_subset _ _ h)
  cases control with
  | some c =>
    rw [portTemplate_inst_some, run_cxMask]
    exact congrArg (ECDSAAdd.State.mk st.phase)
      (run_tableXorGates c (portMask read ports address) st.basis hm hqm)
  | none =>
    rw [portTemplate_inst_none, ← run_cxMask_eq_xMask root _ m st hqm hv, run_cxMask]
    exact congrArg (ECDSAAdd.State.mk st.phase)
      (run_tableXorGates root (portMask read ports address) st.basis hm hqm)

/-- The address and the clean lookup path are stable throughout specialization. -/
def SimulationValid (bits paths : List Wire) (root address : Nat) (st : ECDSAAdd.State) : Prop :=
  Clean paths st.basis ∧ tableAddressValue bits st.basis = address ∧ st.basis root = true

def Placed {n : Nat} (bits paths : List Wire) (root : Wire) : WInstr n → Prop
  | .literal p => ∀ w ∈ root :: bits ++ paths, w ∉ ECDSAAdd.wires p
  | .lookup control ports =>
      (lookupRoot root control :: bits ++ paths).Nodup ∧
      (portTargets ports).Nodup ∧
      (root :: lookupRoot root control :: bits ++ paths).Disjoint (portTargets ports)

theorem literal_preserves_simulation {n : Nat} (p : ECDSAAdd.Program)
    (bits paths : List Wire) (root address : Nat) (hp : Placed (n := n) bits paths root (.literal p))
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths root address st) (m : List Bool) :
    SimulationValid bits paths root address (ECDSAAdd.run p m st) := by
  have frame (w : Wire) (hw : w ∈ root :: bits ++ paths) :
      (ECDSAAdd.run p m st).basis w = st.basis w :=
    ECDSAAdd.run_preserves_outside p m st w (hp w hw)
  dsimp only [SimulationValid]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [frame w (by simp [hw])]
    exact hs.1 w hw
  · rw [tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.2.1
  · rw [frame root (by simp)]
    exact hs.2.2

theorem lookup_preserves_simulation {n : Nat} (read : ConstantBit n → Bool)
    (control : Option Wire) (ports : List (LookupPort n)) (bits paths : List Wire)
    (root address : Nat) (hp : Placed bits paths root (.lookup control ports))
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths root address st) :
    SimulationValid bits paths root address
      ⟨st.phase, tableXorState (portMask read ports address)
        (st.basis (lookupRoot root control)) st.basis⟩ := by
  have frame (w : Wire) (hw : w ∈ root :: bits ++ paths) :
      tableXorState (portMask read ports address) (st.basis (lookupRoot root control)) st.basis w =
        st.basis w := by
    apply tableXorState_outside
    intro hm
    exact List.disjoint_left.mp hp.2.2 (by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem root (List.mem_cons_of_mem _ hw)) (tableBitsMask_subset _ _ hm)
  dsimp only [SimulationValid]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [frame w (by simp [hw])]
    exact hs.1 w hw
  · rw [tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.2.1
  · rw [frame root (by simp)]
    exact hs.2.2

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

theorem simulationCoefficients_mass (xs ys : List ℂ) :
    ((coherentSeqCoefficients xs ys).map Complex.normSq).sum =
      (xs.map Complex.normSq).sum * (ys.map Complex.normSq).sum := by
  induction xs with
  | nil => simp [coherentSeqCoefficients]
  | cons x xs ih =>
    simp only [coherentSeqCoefficients, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, Complex.normSq_mul]
    rw [List.sum_map_mul_left]
    change Complex.normSq x * (ys.map Complex.normSq).sum +
      ((coherentSeqCoefficients xs ys).map Complex.normSq).sum = _
    rw [ih]
    ring

theorem simulationAligned_append {α β : Type*} {R : α → β → Prop}
    {xs ys : List α} {us vs : List β} (h : List.Forall₂ R xs us) (k : List.Forall₂ R ys vs) :
    List.Forall₂ R (xs ++ ys) (us ++ vs) := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h ih

theorem simulationAligned_seq
    {R₁ R₂ R : InstrumentBranch → ℂ → Prop}
    {bs₁ bs₂ : Instrument} {cs₁ cs₂ : List ℂ}
    (h₁ : List.Forall₂ R₁ bs₁ cs₁) (h₂ : List.Forall₂ R₂ bs₂ cs₂)
    (h : ∀ b₁ c₁ b₂ c₂, R₁ b₁ c₁ → R₂ b₂ c₂ → R (b₁.seq b₂) (c₁*c₂)) :
    List.Forall₂ R (Instrument.seq bs₁ bs₂) (coherentSeqCoefficients cs₁ cs₂) := by
  induction h₁ with
  | nil => exact .nil
  | @cons b c bs cs hb _ ih =>
    have one : List.Forall₂ R (bs₂.map fun b₂ => b.seq b₂) (cs₂.map fun c₂ => c*c₂) := by
      clear ih
      induction h₂ with
      | nil => exact .nil
      | @cons b₂ c₂ bs₂ cs₂ hb₂ _ ih₂ => exact .cons (h b c b₂ c₂ hb hb₂) ih₂
    exact simulationAligned_append one ih

theorem run_append_records (p q : ECDSAAdd.Program) (m₁ m₂ : List Bool)
    (st : ECDSAAdd.State) (hm : m₁.length = ECDSAAdd.measurementCount p) :
    ECDSAAdd.run (p ++ q) (m₁ ++ m₂) st =
      ECDSAAdd.run q m₂ (ECDSAAdd.run p m₁ st) := by
  rw [ECDSAAdd.run_append, ← hm, List.take_left, List.drop_left]

/-- Every literal branch has a record of the same length and an input-independent coefficient. -/
theorem literal_simulation (p : ECDSAAdd.Program) :
    ∃ cs : List ℂ, List.Forall₂ (fun b c =>
      b.history.length = ECDSAAdd.measurementCount p ∧
      ∀ st, b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run p b.history st)) (literalSource p).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  let read : ConstantBit 1 → Bool := fun _ => false
  let history : Fin 0 → Bool := Fin.elim0
  have hr := literal_run p 0 read history
  refine ⟨(literalSource p).run.map (fun _ => Bridge.invSqrtTwo ^ ECDSAAdd.measurementCount p),
    ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro b hb
    rw [← hr] at hb
    constructor
    · have h := straight_history_length (Bridge.translate (literalT p) 0) read history b hb
      simpa [literal_meas] using h
    · intro st
      have h := Bridge.translate_branch read (literalT p) (Bridge.static_lit p) 0 history b hb st
      have hib : Bridge.instB read (literalT p) = p := Bridge.instB_lit read p
      rw [hib, literal_meas] at h
      exact h
  · rw [List.map_map]
    have hcf : (Complex.normSq ∘ fun _ : InstrumentBranch =>
        Bridge.invSqrtTwo ^ ECDSAAdd.measurementCount p) =
        fun _ => ((1 : ℝ) / 2) ^ ECDSAAdd.measurementCount p := by
      funext b
      rw [Function.comp_apply, map_pow, Bridge.normSq_invSqrtTwo]
    rw [hcf, List.map_const', List.sum_replicate, ← hr, Bridge.straight_run_length]
    simp only [literal_meas, Nat.sub_zero, Nat.zero_add, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num

def SimulationBranch {n : Nat} (read : ConstantBit n → Bool) (code : WCode n)
    (bits paths : List Wire) (root : Wire) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords code ∧
    ∀ address st, SimulationValid bits paths root address st →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize code address).instantiate read) m st)

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

def lookupSlots {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + lookupSlots ops
  | .erase _ _ _ :: ops => 3 + lookupSlots ops

theorem lookupSlots_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupSlots (xs ++ ys) = lookupSlots xs + lookupSlots ys := by
  induction xs with
  | nil => simp [lookupSlots]
  | cons x xs ih => cases x <;> simp [lookupSlots, ih, Nat.add_assoc]

theorem andEraseProgram_slots (n start : Nat) (a b t : Wire) :
    (andEraseProgram n start a b t).gateSlots = 3 := by
  simp [andEraseProgram, recordGates, controlledZ, Straight.gateSlots]

theorem lookupProgram_slots {n : Nat} (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n ops start).gateSlots = lookupSlots ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [lookupProgram, lookupSlots, Straight.gateSlots_append,
      gateProgram_slots, andEraseProgram_slots, ih]

theorem unaryLookupOps_slots {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (size : Nat) (hs : ∀ address root, (leaf address root).length = size)
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (hl : tree.Layout q paths) :
    lookupSlots (unaryLookupOps leaf tree q paths) =
      tree.leaves * size + 10 * tree.internalNodes := by
  induction hl with
  | leaf label q paths hn => simp [unaryLookupOps, lookupSlots, hs, UnaryActionTree.leaves,
      UnaryActionTree.internalNodes]
  | node bit q path zero one rest hn hz ho ihz iho =>
    simp only [unaryLookupOps, lookupSlots_append, lookupSlots, ordinaryOp, List.length_map,
      computeZeroAnd, List.length_cons, List.length_nil, Nat.add_zero, ihz, iho,
      UnaryActionTree.leaves, UnaryActionTree.internalNodes]
    ring

theorem addressTree_leaves (bits : List Wire) (base stride : Nat) :
    (tableAddressTree bits base stride).leaves = 2 ^ bits.length := by
  induction bits generalizing base stride with
  | nil => rfl
  | cons bit bits ih =>
    simp [tableAddressTree, UnaryActionTree.leaves, ih, pow_succ]
    omega

/-- One combined leaf has a slot for every port in every physical table row. -/
theorem portProgram_slots {n : Nat} (ports : List (LookupPort n))
    (bits paths : List Wire) (root start : Nat) (hl : bits.length ≤ paths.length)
    (hn : (root :: bits ++ paths).Nodup) :
    (lookupProgram n (portOps ports bits paths root) start).gateSlots =
      2 ^ bits.length * ports.length + 10 * (2 ^ bits.length - 1) := by
  rw [lookupProgram_slots, portOps, unaryLookupOps_slots _ ports.length
    (by intro address q; simp [portLeaf]) _ _ _ (tableAddressTree_layout _ _ _ _ _ hl hn),
    addressTree_leaves]
  have h := tableAddressTree_nodes bits 0 1
  omega

def codeSlots {n : Nat} (bits : List Wire) : WCode n → Nat
  | [] => 0
  | .literal p :: code => Bridge.tmplSlots (literalT (n := n) p) + codeSlots bits code
  | .lookup _ ports :: code =>
      (2 ^ bits.length * ports.length + 10 * (2 ^ bits.length - 1)) + codeSlots bits code

/-- Exact emitted slot count; coefficient readers never affect this structural ledger. -/
theorem compile_slots {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : LookupLayouts bits paths root code) (start : Nat) :
    (compile bits paths root code start).gateSlots = codeSlots bits code := by
  induction code generalizing start with
  | nil => simp [compile, codeSlots, Straight.gateSlots]
  | cons i code ih =>
    have htail : LookupLayouts bits paths root code :=
      ⟨hl.1, fun c p hp => hl.2 c p (List.mem_cons_of_mem _ hp)⟩
    cases i with
    | literal p =>
      simp [compile, codeSlots, Straight.gateSlots_append, Bridge.translate_gateSlots, ih htail]
    | lookup c p =>
      simp [compile, codeSlots, Straight.gateSlots_append,
        portProgram_slots p bits paths _ _ hl.1 (hl.2 c p (by simp)), ih htail]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def geometryOK (bits paths : List Wire) (root : Wire) (control : Option Wire)
    (targets : List Wire) : Bool :=
  decide (lookupRoot root control :: bits ++ paths).Nodup && decide targets.Nodup &&
    ((root :: lookupRoot root control :: bits ++ paths).all fun w => !targets.contains w)

def lookupPlacedOK {n : Nat} (bits paths : List Wire) (root : Wire) : WInstr n → Bool
  | .literal _ => true
  | .lookup c p => geometryOK bits paths root c (portTargets p)

theorem lookupPlacedOK_iff {n : Nat} (bits paths : List Wire) (root : Wire) (i : WInstr n) :
    lookupPlacedOK bits paths root i = true ↔
      match i with | .literal _ => True | .lookup c p => Placed bits paths root (.lookup c p) := by
  cases i <;> simp [lookupPlacedOK, geometryOK, Placed, Bool.and_eq_true, and_assoc, List.all_eq_true, List.disjoint_left, or_imp, forall_and]

/-- Literal segments occur intact in every row specialization. -/
theorem literal_wires_subset {n : Nat} (read : ConstantBit n → Bool) (code : WCode n)
    (address : Nat) (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ code) :
    ECDSAAdd.wires p ⊆ ECDSAAdd.wires ((specialize code address).instantiate read) := by
  induction code with
  | nil => simp at hp
  | cons i code ih =>
    simp only [specialize, List.flatMap_cons, ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      ECDSAAdd.wires_append]
    rcases List.mem_cons.mp hp with h | h
    · cases h
      simp [WInstr.specialize, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    · exact (ih h).trans (Finset.subset_union_right)

theorem indexedPorts_targets {n : Nat} (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    portTargets (indexedPorts ws refs v) = ws := by
  induction ws generalizing refs with
  | nil => rfl
  | cons w ws ih =>
    simpa [indexedPorts, portTargets] using congrArg (List.cons w) (ih (fun a i => refs a (i+1)))

def geometryCodeOK {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n) : Bool :=
  code.all (lookupPlacedOK bits paths root)

@[simp] theorem geometry_append {n : Nat} (bits paths : List Wire) (root : Wire)
    (xs ys : WCode n) : geometryCodeOK bits paths root (xs ++ ys) =
      (geometryCodeOK bits paths root xs && geometryCodeOK bits paths root ys) := by
  simp [geometryCodeOK]

@[simp] theorem geometry_literal {n : Nat} (bits paths : List Wire) (root : Wire)
    (p : ECDSAAdd.Program) : geometryCodeOK bits paths root (wLiteral (n := n) p) = true := rfl

@[simp] theorem geometry_mask {n : Nat} (bits paths : List Wire) (root : Wire)
    (c : Option Wire) (ws : List Wire) (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    geometryCodeOK bits paths root (wMask c ws refs v) = geometryOK bits paths root c ws := by
  simp [geometryCodeOK, wMask, lookupPlacedOK, indexedPorts_targets]

@[simp] theorem geometry_point {n : Nat} (bits paths : List Wire) (root c : Wire)
    (r : ECDSAAdd.PointReg) (fin : Nat → ConstantBit n) (xr yr : Nat → Nat → ConstantBit n) :
    geometryCodeOK bits paths root (wPoint c r fin xr yr) =
      geometryOK bits paths root (some c) (r.finite :: r.x ++ r.y) := by
  simp only [geometryCodeOK, wPoint, List.all_cons, List.all_nil, Bool.and_true, lookupPlacedOK]
  congr 1
  simp only [portTargets, List.map_cons, List.map_append]; rw [show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _, show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _]

@[simp] theorem geometry_shortXor {n : Nat} (bits paths : List Wire) (root : Wire)
    (L : ECDSAAdd.Arithmetic.ControlledPointLayout) (fin : Nat → ConstantBit n)
    (xr : Nat → Nat → ConstantBit n) (y0 : Nat → ConstantBit n) :
    geometryCodeOK bits paths root (wShortXor L fin xr y0) =
      geometryOK bits paths root none (L.point.finite :: (L.point.x ++ L.point.y.take 1)) := by
  simp only [geometryCodeOK, wShortXor, List.all_cons, List.all_nil, Bool.and_true, lookupPlacedOK]
  congr 1
  simp only [portTargets, List.map_cons, List.map_append]; rw [show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _, show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _]
  all_goals rfl

theorem geometry_zeroWith {n : Nat} (bits paths : List Wire) (root : Wire)
    (tail : Wire → WCode n) (h : ∀ w, geometryCodeOK bits paths root (tail w) = true)
    (c : Wire) (bs : List ECDSAAdd.Arithmetic.ZeroBit) :
    geometryCodeOK bits paths root (wZeroWith tail c bs) = true := by
  induction bs generalizing c with
  | nil => exact h c
  | cons b bs ih => simp [wZeroWith, ih]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

def normalizeWInstr {n : Nat} : WInstr n → WInstr n
  | .literal p => .literal (ECDSAAdd.Baselines.normalizeProgram p)
  | .lookup c p => .lookup c p

def normalizeW {n : Nat} (code : WCode n) : WCode n := code.map normalizeWInstr

theorem portTemplate_normalize {n : Nat} (control : Option Wire)
    (ports : List (LookupPort n)) (address : Nat) :
    ECDSAAdd.ShorPort.Tmpl.map ECDSAAdd.Baselines.normalizeInstr (portTemplate control ports address) =
      portTemplate control ports address := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    cases control <;> simp only [portTemplate_cons, ECDSAAdd.ShorPort.Tmpl.map,
      List.map_cons, ECDSAAdd.ShorPort.TInstr.map, ECDSAAdd.Baselines.normalizeInstr]
    all_goals congr 1

theorem specialize_normalize {n : Nat} (code : WCode n) (address : Nat) :
    specialize (normalizeW code) address =
      ECDSAAdd.ShorPort.Tmpl.map ECDSAAdd.Baselines.normalizeInstr (specialize code address) := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p =>
      change ECDSAAdd.ShorPort.Tmpl.lit (ECDSAAdd.Baselines.normalizeProgram p) ++
        specialize (normalizeW code) address =
        ECDSAAdd.ShorPort.Tmpl.map ECDSAAdd.Baselines.normalizeInstr
          (ECDSAAdd.ShorPort.Tmpl.lit p ++ specialize code address)
      rw [ih]
      simp [ECDSAAdd.ShorPort.Tmpl.map, ECDSAAdd.ShorPort.Tmpl.lit,
        ECDSAAdd.Baselines.normalizeProgram, List.map_map, ECDSAAdd.ShorPort.TInstr.map,
        Function.comp_def]
    | lookup c ports =>
      change portTemplate c ports address ++ specialize (normalizeW code) address =
        ECDSAAdd.ShorPort.Tmpl.map ECDSAAdd.Baselines.normalizeInstr
          (portTemplate c ports address ++ specialize code address)
      rw [ih]
      unfold ECDSAAdd.ShorPort.Tmpl.map
      rw [List.map_append]
      change portTemplate c ports address ++ _ =
        ECDSAAdd.ShorPort.Tmpl.map ECDSAAdd.Baselines.normalizeInstr (portTemplate c ports address) ++ _
      rw [portTemplate_normalize]

theorem specialize_normalize_run {n : Nat} (read : ConstantBit n → Bool)
    (code : WCode n) (address : Nat) (m : List Bool) (st : ECDSAAdd.State) :
    ECDSAAdd.run ((specialize (normalizeW code) address).instantiate read) m st =
      ECDSAAdd.run ((specialize code address).instantiate read) m st := by
  rw [specialize_normalize, ECDSAAdd.ShorPort.Tmpl.instantiate_normalize,
    ECDSAAdd.Baselines.normalize_run]

theorem literalRecords_normalize {n : Nat} (code : WCode n) :
    literalRecords (normalizeW code) = literalRecords code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    simp only [normalizeW] at ih
    cases i <;> simp [normalizeW, normalizeWInstr, literalRecords,
      ECDSAAdd.Baselines.normalize_measurements, ih]

theorem literalToffolis_normalize {n : Nat} (code : WCode n) :
    literalToffolis (normalizeW code) ≤ literalToffolis code := by
  induction code with
  | nil => exact le_rfl
  | cons i code ih =>
    cases i with
    | literal p =>
      simpa [normalizeW, normalizeWInstr, literalToffolis] using
        Nat.add_le_add (ECDSAAdd.Baselines.normalize_toffoli p) ih
    | lookup c p => simpa [normalizeW, normalizeWInstr, literalToffolis] using ih

@[simp] theorem traversals_normalize {n : Nat} (code : WCode n) :
    traversals (normalizeW code) = traversals code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    simp only [normalizeW] at ih
    cases i <;> simp [normalizeW, normalizeWInstr, traversals, ih]

theorem portProgram_wellFormed {n : Nat} (ports : List (LookupPort n))
    (bits paths : List Wire) (q start : Nat) (hl : bits.length ≤ paths.length)
    (hn : (q :: bits ++ paths).Nodup)
    (hd : (q :: bits ++ paths).Disjoint (portTargets ports)) :
    (lookupProgram n (portOps ports bits paths q) start).WellFormed := by
  apply lookupProgram_wellFormed
  apply unaryLookupOps_physical _ _ _ _ (tableAddressTree_layout _ _ _ _ _ hl hn)
  intro label root hr g hg
  obtain ⟨port, hp, rfl⟩ := List.mem_map.mp hg
  change root ≠ port.target
  intro he
  have hroot : root ∈ q :: bits ++ paths := by
    rcases List.mem_cons.mp hr with rfl | h
    · simp
    · simp [h]
  have htarget : port.target ∈ portTargets ports := List.mem_map.mpr ⟨port, hp, rfl⟩
  exact List.disjoint_left.mp hd (by simpa [he] using hroot) htarget

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open Secp256k1
noncomputable section
set_option maxHeartbeats 3000000
local instance : Fact (Nat.Prime p) := ⟨Secp256k1.p_prime⟩

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.Bridge
open Quantum Secp256k1 Challenge NaiveChallenge
open ECDSAAdd.ShorPort (Tmpl finiteT maskedT xorT maskedPointT pairXorT shortXorT bitTestT
  pairTailT zeroWithT pairEqualT shortEqualT constAddT recoveryT genericT cornersT)
noncomputable section

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-! ## Port templates as bridge templates -/

section PortGeneric
variable {n : Nat}

/-- An ecdsa-lib template instruction as a bridge template instruction. -/
def ofPort : ECDSAAdd.ShorPort.TInstr n → TInstr n
  | .lit i => .lit i
  | .gated r v i => .when r v i

/-! ### Gated instructions -/

/-- Every gated instruction of `t` satisfies `P`. -/
def PortGated (P : ECDSAAdd.Instr → Prop) (t : Tmpl n) : Prop :=
  ∀ r v i, ECDSAAdd.ShorPort.TInstr.gated r v i ∈ t → P i

/-- The gated gates of the template: an `X`, or a `CX` on distinct wires, on sites of `S`. -/
def PortGood (S : List Nat) : ECDSAAdd.Instr → Prop
  | .X w => w ∈ S
  | .CX c w => c ≠ w ∧ c ∈ S ∧ w ∈ S
  | _ => False

theorem portGated_lit {P : ECDSAAdd.Instr → Prop} (p : ECDSAAdd.Program) :
    PortGated P (ECDSAAdd.ShorPort.Tmpl.lit p : Tmpl n) := by
  intro r v i hm
  obtain ⟨j, -, hj⟩ := List.mem_map.mp hm
  cases hj

/-! ### Gated-instruction counts -/

/-! ### Static consequences of one instantiation -/

theorem portLit_mem (read : ConstantBit n → Bool) {t : Tmpl n} {i : ECDSAAdd.Instr}
    (h : ECDSAAdd.ShorPort.TInstr.lit i ∈ t) : i ∈ t.instantiate read :=
  List.mem_flatMap.mpr ⟨_, h, List.mem_singleton_self i⟩

theorem portCorrWires {w : Nat} :
    ∀ cs : List ECDSAAdd.Correction, w ∈ cs.flatMap corrWires → w ∈ ECDSAAdd.correctionWires cs
  | [], h => by simp at h
  | c :: cs, h => by
    rw [List.flatMap_cons, List.mem_append] at h
    cases c with
    | Z a =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_singleton]
      rcases h with h | h
      · left
        simpa [corrWires] using h
      · exact Or.inr (portCorrWires cs h)
    | CZ a b =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      rcases h with h | h
      · left
        simpa [corrWires] using h
      · exact Or.inr (portCorrWires cs h)

theorem portInstrWires {i : ECDSAAdd.Instr} {w : Nat} (h : w ∈ instrWires i) :
    w ∈ ECDSAAdd.Instr.wires i := by
  cases i with
  | X a => simpa [instrWires, ECDSAAdd.Instr.wires] using h
  | CX a b => simpa [instrWires, ECDSAAdd.Instr.wires] using h
  | CCX a b c => simpa [instrWires, ECDSAAdd.Instr.wires] using h
  | measureX t c0 c1 =>
    simp only [instrWires, List.mem_cons, List.mem_append] at h
    simp only [ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_singleton]
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (portCorrWires c0 h))
    · exact Or.inr (portCorrWires c1 h)

theorem portMemWires {i : ECDSAAdd.Instr} {w : Nat} (hw : w ∈ ECDSAAdd.Instr.wires i) :
    ∀ {p : ECDSAAdd.Program}, i ∈ p → w ∈ ECDSAAdd.wires p
  | [], hi => by simp at hi
  | j :: p, hi => by
    simp only [ECDSAAdd.wires, Finset.mem_union]
    rcases List.mem_cons.mp hi with rfl | h
    · exact Or.inl hw
    · exact Or.inr (portMemWires hw h)

theorem portGoodWires {S : List Nat} {i : ECDSAAdd.Instr} {w : Nat} (h : PortGood S i)
    (hw : w ∈ instrWires i) : w ∈ S := by
  cases i with
  | X a =>
    have h' : a ∈ S := h
    simp only [instrWires, List.mem_singleton] at hw
    rw [hw]
    exact h'
  | CX a b =>
    have h' : a ≠ b ∧ a ∈ S ∧ b ∈ S := h
    simp only [instrWires, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · rw [hw]; exact h'.2.1
    · rw [hw]; exact h'.2.2
  | CCX a b c => exact False.elim h
  | measureX t c0 c1 => exact False.elim h

theorem portWires (read : ConstantBit n → Bool) {S : List Nat} {t : Tmpl n}
    (hg : PortGated (PortGood S) t)
    (hw : ECDSAAdd.wires (t.instantiate read) ⊆ S.toFinset) :
    ∀ w ∈ tmplWires (List.map ofPort t), w ∈ S := by
  intro w hw'
  rw [tmplWires, List.mem_flatMap] at hw'
  obtain ⟨a, ha, hwa⟩ := hw'
  obtain ⟨g, hg0, rfl⟩ := List.mem_map.mp ha
  cases g with
  | lit i =>
    exact List.mem_toFinset.mp (hw (portMemWires (portInstrWires hwa) (portLit_mem read hg0)))
  | gated r v i => exact portGoodWires (hg r v i hg0) hwa

/-! ### Normalisation -/

end PortGeneric

/-! ## The gated gates of `finiteT` -/

section PortCombinators
variable {n : Nat} {P : ECDSAAdd.Instr → Prop}

/-! ### Counts -/

end PortCombinators

/-! ## The gated gates on the fixed layout -/

section PortLayout

/-- The point register of the ECDSAAdd challenge is the bridge's point register. -/
theorem portPointWires :
    ECDSAAdd.Arithmetic.PointAddLayout.pointWires ECDSAAdd.Challenge.point = pointWires := by
  rw [pointWires_split]
  show 1 :: ((List.range 256).map (· + 2) ++ (List.range 256).map (· + 258)) = _
  rw [map_add_range, map_add_range]

theorem portWorkEq :
    (ECDSAAdd.Baselines.layout.work : List Nat) = List.range' 514 9300 ++ [9814, 9815, 9816] := by
  have hc := ECDSAAdd.Baselines.core_wires
  have hsplit : List.range' 1 9813 = List.range' 1 513 ++ List.range' 514 9300 :=
    (List.range'_append (s := 1) (m := 513) (n := 9300) (step := 1)).symm
  have hin : ECDSAAdd.Arithmetic.PointAddLayout.pointWires ECDSAAdd.Baselines.layout.core.input =
      List.range' 1 513 := portPointWires
  have h2 : ECDSAAdd.Arithmetic.PointAddLayout.pointWires ECDSAAdd.Baselines.layout.core.output ++
      ECDSAAdd.Baselines.layout.core.work = List.range' 514 9300 := by
    rw [ECDSAAdd.Arithmetic.PointAddLayout.wires, hsplit, List.append_assoc, hin] at hc
    exact List.append_cancel_left hc
  show ECDSAAdd.Arithmetic.PointAddLayout.pointWires ECDSAAdd.Baselines.layout.core.output ++
      (ECDSAAdd.Baselines.layout.core.work ++ [9814, 9815, 9816]) = _
  rw [← List.append_assoc, h2]

theorem portWork_range : ∀ w : Nat, w ∈ ECDSAAdd.Baselines.layout.work → 514 ≤ w ∧ w < 206624 := by
  intro w hw
  have hw' : w ∈ List.range' 514 9300 ++ [9814, 9815, 9816] := by rw [← portWorkEq]; exact hw
  rcases List.mem_append.mp hw' with h | h
  · have := List.mem_range'_1.mp h
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega

end PortLayout

end
end ShorECDLP.Entrant.Bridge


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

abbrev NegLayout := ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout

theorem negate_256_counts (K : NegLayout) (q p c : Nat)
    (hw : K.work.length = K.word.length) (hn : K.word.length = 256) :
    ECDSAAdd.toffoliCount (K.program q p c) = 1022 ∧
      ECDSAAdd.measurementCount (K.program q p c) = 1022 := by
  have h := K.program_counts q p c hw (by omega)
  simpa [hn] using h

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
noncomputable section
set_option maxHeartbeats 3000000

theorem pointY_neg_mod (P : Point) : pointY (-P) = (ECDSAAdd.p - pointY P) % ECDSAAdd.p := by
  rw [ECDSAAdd.ShorPort.pointY_neg, ZMod.neg_val', ECDSAAdd.ShorPort.coords_y]
  norm_num [ShorECDLP.p, ECDSAAdd.p]

theorem pointY_neg_twice_mod (P : Point) :
    (ECDSAAdd.p - pointY (-P)) % ECDSAAdd.p = pointY P := by
  have h := pointY_neg_mod (-P)
  simpa only [neg_neg] using h.symm

theorem run_no_records (p : Program) (hm : measurementCount p = 0) (m : List Bool) (st : State) :
    run p m st = run p ([]) st := by
  rw [← run_take p m st, hm, List.take_zero]

/-- The negative-double word may be cleared with the available doubled coordinates only
when its flag identifies that exact corner. Negation must precede the XOR. -/
theorem negative_corner_clear (K : NegLayout) (q : Wire) (r : PointReg) (D : Point)
    (hk : K.word = r.y) (hn : (K.wires q).Nodup)
    (hw : K.work.length = K.word.length) (npos : 0 < K.word.length)
    (hpc : ECDSAAdd.p + SquareReduction.c = 2 ^ K.word.length)
    (hpoint : (PointAddLayout.pointWires r).Nodup) (hq : q ∉ PointAddLayout.pointWires r)
    (hx : r.x.length = 256) (hy : r.y.length = 256)
    (st : State) (hY : ECDSAAdd.regValue r.y st.basis < ECDSAAdd.p)
    (hwork : ECDSAAdd.regValue K.work st.basis = 0) (hcin : st.basis K.cin = false)
    (hzero : st.basis K.zero = false)
    (hcorner : st.basis q = true → Holds.holds st.basis r (-D)) (m : List Bool) :
    run (K.program q ECDSAAdd.p SquareReduction.c ++ maskedPointConstant q r D) m st =
      run (maskedPointConstant q r (-D)) ([]) st := by
  let u := run (K.program q ECDSAAdd.p SquareReduction.c) m st
  let v := run (maskedPointConstant q r D) ([]) u
  let old := run (maskedPointConstant q r (-D)) ([]) st
  have hN := K.program_correct q hn hw npos ECDSAAdd.p SquareReduction.c
    (ECDSAAdd.regValue r.y st.basis) hpc (by norm_num [SquareReduction.c]) hY st m
    (by rw [hk]) hwork hcin hzero
  change u.phase = st.phase ∧ _ at hN
  rw [hk] at hN
  have hxy := (List.nodup_append'.mp (List.nodup_cons.mp hpoint).2).2.2
  have hfinite : r.finite ∉ r.y := fun hm =>
    (List.nodup_cons.mp hpoint).1 (List.mem_append_right _ hm)
  have hqY : q ∉ r.y := fun hm => hq (by simp [PointAddLayout.pointWires, hm])
  have hqU : u.basis q = st.basis q := hN.2.2 q hqY
  have hfiniteU : u.basis r.finite = st.basis r.finite := hN.2.2 _ hfinite
  have hxU : ECDSAAdd.regValue r.x u.basis = ECDSAAdd.regValue r.x st.basis := by
    apply ECDSAAdd.Arithmetic.regValue_congr
    intro w hw
    exact hN.2.2 w (List.disjoint_left.mp hxy hw)
  have ev := maskedPointConstant_correct q r D hpoint hq hx hy u ([])
  have eo := maskedPointConstant_correct q r (-D) hpoint hq hx hy st ([])
  have hfiniteEq : v.basis r.finite = old.basis r.finite := by
    rw [ev.finite, eo.finite, hqU, hfiniteU, ECDSAAdd.ShorPort.pointFinite_neg]
  have hxEq : ECDSAAdd.regValue r.x v.basis = ECDSAAdd.regValue r.x old.basis := by
    rw [ev.x, eo.x, hqU, hxU, ECDSAAdd.ShorPort.pointX_neg]
  have hyEq : ECDSAAdd.regValue r.y v.basis = ECDSAAdd.regValue r.y old.basis := by
    rw [ev.y, eo.y, hqU, hN.2.1]
    cases hqbit : st.basis q with
    | false => simp
    | true =>
      have hcoords := (point_holds _ _ _).mp (hcorner hqbit)
      rw [hcoords.2.2]
      simp [pointY_neg_twice_mod]
  have heq : v = old := by
    apply State.extensionality
    · exact (ev.phase.trans hN.1).trans eo.phase.symm
    funext w
    by_cases hf : w = r.finite
    · subst w; exact hfiniteEq
    by_cases hxm : w ∈ r.x
    · exact Bridge.regValue_bits r.x _ _ (by simpa only [Bridge.regValueB_eq] using hxEq) w hxm
    by_cases hym : w ∈ r.y
    · exact Bridge.regValue_bits r.y _ _ (by simpa only [Bridge.regValueB_eq] using hyEq) w hym
    have hout : w ∉ PointAddLayout.pointWires r := by
      simpa only [PointAddLayout.pointWires, List.mem_cons, List.mem_append, not_or] using ⟨⟨hf,hxm⟩,hym⟩
    exact ((ev.outside w hout).trans (hN.2.2 w hym)).trans (eo.outside w hout).symm
  rw [run_append, run_take, run_no_records _ (maskedPointConstant_counts q r D).2]
  exact heq

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section

theorem odd_sub_low_bit (p y : Nat) (hp : p % 2 = 1) (hy : y ≤ p) :
    (p-y).testBit 0 = !(y.testBit 0) := by
  simp only [Nat.testBit_zero]
  by_cases h : y % 2 = 1
  · have hn : (p-y) % 2 ≠ 1 := by omega
    simp [h, hn]
  · have hn : (p-y) % 2 = 1 := by omega
    simp [h, hn]

theorem neg_y_low_bit (y : ECDSAAdd.Fp) (hy : y ≠ 0) :
    (-y).val.testBit 0 = !(y.val.testBit 0) := by
  rw [ZMod.neg_val, if_neg hy]
  exact odd_sub_low_bit ECDSAAdd.p y.val (by norm_num [ECDSAAdd.p]) y.val_lt.le

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
noncomputable section

theorem torsion_unit_remainder_ne_zero (P : Point) (n m : Nat)
    (hP : P ≠ 0) (horder : n • P = 0) (hrem : n % m = 1) : m • P ≠ 0 := by
  intro hm
  have hn : n = n / m * m + 1 := by
    simpa only [hrem, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n m).symm
  have hmul : (n / m * m) • P = 0 := by
    rw [Nat.mul_comm, mul_nsmul, hm, nsmul_zero]
  rw [hn, add_nsmul, hmul, one_nsmul, zero_add] at horder
  exact hP horder

theorem finite_point_parity (P : Point) (hP : P ≠ 0) (horder : ShorECDLP.order • P = 0) :
    ECDSAAdd.Entrant.yBit (-P) = !(ECDSAAdd.Entrant.yBit P) := by
  have hdouble : P+P ≠ 0 := by
    simpa only [two_nsmul] using torsion_unit_remainder_ne_zero P ShorECDLP.order 2 hP horder
      (by norm_num [ShorECDLP.order])
  cases P with
  | zero => exact (hP rfl).elim
  | @some x y h =>
    have hy : y ≠ -y := (doubling_enabled_iff h).mpr (fun he =>
      hdouble (eq_neg_iff_add_eq_zero.mp he))
    have hy0 : y ≠ 0 := by intro hz; apply hy; simp [hz]
    rw [ECDSAAdd.ShorPort.yBit_eq, ECDSAAdd.ShorPort.yBit_eq, ECDSAAdd.ShorPort.pointY_neg]
    exact neg_y_low_bit y hy0

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

def LookupOn {n : Nat} (support : List Wire) : LookupOp n → Prop
  | .gates gs => ∀ g ∈ gs, ∀ w ∈ gateWires (slotGate g), w ∈ support
  | .erase a b t => a ∈ support ∧ b ∈ support ∧ t ∈ support

theorem gateProgram_support {n start : Nat} (gs : List (TemplateGate n)) (support : List Wire)
    (hs : ∀ g ∈ gs, ∀ w ∈ gateWires (slotGate g), w ∈ support) :
    ShorECDLP.NaiveChallenge.straightWires (gateProgram (cursor := start) gs) ⊆ support := by
  induction gs with
  | nil => simp [gateProgram, ShorECDLP.NaiveChallenge.straightWires]
  | cons g gs ih =>
    intro w hw
    simp only [gateProgram, ShorECDLP.NaiveChallenge.straightWires, List.mem_append] at hw
    rcases hw with h | h
    · exact hs g (by simp) w h
    · exact ih (fun g hg => hs g (List.mem_cons_of_mem _ hg)) h

theorem andEraseProgram_support (n start a b t : Nat) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (ht : t ∈ support) :
    ShorECDLP.NaiveChallenge.straightWires (andEraseProgram n start a b t) ⊆ support := by
  intro w hw
  simp only [andEraseProgram, Paper2607_13816.ChallengeMigration.recordGates,
    controlledZ, ShorECDLP.NaiveChallenge.straightWires, gateWires, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hw
  aesop

theorem lookup_cast_wires {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    ShorECDLP.NaiveChallenge.straightWires (Paper2607_13816.ChallengeMigration.castFinish h p) = ShorECDLP.NaiveChallenge.straightWires p := by
  subst f
  rfl

theorem lookupProgram_support {n : Nat} (ops : List (LookupOp n)) (start : Nat)
    (support : List Wire) (hs : ∀ op ∈ ops, LookupOn support op) :
    ShorECDLP.NaiveChallenge.straightWires (lookupProgram n ops start) ⊆ support := by
  induction ops generalizing start with
  | nil => simp [lookupProgram, ShorECDLP.NaiveChallenge.straightWires]
  | cons op ops ih =>
    have ht (k : Nat) := ih k (fun o ho => hs o (List.mem_cons_of_mem _ ho))
    have ho := hs op (by simp)
    cases op with
    | gates gs =>
      rw [lookupProgram, Bridge.straightWires_append]
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact gateProgram_support gs support ho hw
      · exact ht start hw
    | erase a b t =>
      simp only [lookupProgram, lookup_cast_wires, Bridge.straightWires_append]
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact andEraseProgram_support n start a b t support ho.1 ho.2.1 ho.2.2 hw
      · exact ht (start+1) hw

theorem ordinaryOp_on {n : Nat} (gs : Circuit) (support : List Wire)
    (hs : ∀ g ∈ gs, ∀ w ∈ gateWires g, w ∈ support) : LookupOn support (@ordinaryOp n gs) := by
  intro g hg w hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  exact hs k hk w hw

theorem unaryLookupOps_support {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths support : List Wire)
    (hq : q ∈ support) (hb : ∀ w ∈ tree.indexWires, w ∈ support) (hp : paths ⊆ support)
    (hleaf : ∀ label root, root ∈ support → LookupOn support (.gates (leaf label root))) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, LookupOn support op := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps] using hleaf label q hq
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hbit := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path ∈ support := hp (by simp)
      have hrest : rest ⊆ support := fun w hw => hp (List.mem_cons_of_mem _ hw)
      have hz := ihz path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires, hw])) hrest
      have ho := iho path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires, hw])) hrest
      have hcompute : LookupOn support (@ordinaryOp n (computeZeroAnd q bit path)) := by
        apply ordinaryOp_on
        intro g hg w hw
        simp only [computeZeroAnd, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;>
          simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hw
        all_goals aesop
      have hcx : LookupOn support (@ordinaryOp n ([.CX q path])) := by
        apply ordinaryOp_on
        intro g hg w hw
        simp only [List.mem_singleton] at hg
        subst g
        simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption
      have hx : LookupOn support (@ordinaryOp n ([.X bit])) := by
        apply ordinaryOp_on
        intro g hg w hw
        simp only [List.mem_singleton] at hg
        subst g
        simp only [gateWires, List.mem_singleton] at hw
        simpa [hw] using hbit
      simp only [unaryLookupOps, List.forall_mem_append, List.forall_mem_cons,
        List.mem_nil_iff, false_implies]
      exact ⟨⟨⟨⟨⟨hcompute,fun _ => trivial⟩,hz⟩,⟨hcx,fun _ => trivial⟩⟩,ho⟩,
        hcx,hx,⟨hq,hbit,hpath⟩,hx,fun _ => trivial⟩

theorem portProgram_support {n : Nat} (ports : List (LookupPort n)) (bits paths : List Wire)
    (root start : Nat) (support : List Wire) (hq : root ∈ support) (hb : bits ⊆ support)
    (hp : paths ⊆ support) (ht : portTargets ports ⊆ support) :
    ShorECDLP.NaiveChallenge.straightWires (lookupProgram n (portOps ports bits paths root) start) ⊆ support := by
  apply lookupProgram_support
  apply unaryLookupOps_support _ _ _ _ _ hq
  · intro w hw
    exact hb ((tableAddressTree_mem_index _ _ _ _).mp hw)
  · exact hp
  · intro label q hq g hg w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    change w ∈ [q,p.target] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hq
    · have he : w = p.target := List.mem_singleton.mp hw
      rw [he]
      exact ht (List.mem_map.mpr ⟨p,hp,rfl⟩)

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def mapPointReg (f : Nat → Nat) (r : PointReg) : PointReg :=
  ⟨f r.finite, r.x.map f, r.y.map f⟩

def mapCore (f : Nat → Nat) (L : PointAddLayout) : PointAddLayout where
  input := mapPointReg f L.input
  output := mapPointReg f L.output
  dx := L.dx.map f
  dy := L.dy.map f
  slope := L.slope.map f
  square := L.square.map f
  offset := L.offset.map f
  candidateX := L.candidateX.map f
  delta := L.delta.map f
  product := L.product.map f
  candidateY := L.candidateY.map f
  constant := L.constant.map f
  divisor := L.divisor.map f
  inverse := L.inverse.map f
  inputXHigh := f L.inputXHigh
  inputYHigh := f L.inputYHigh
  equalX := f L.equalX
  equalNegY := f L.equalNegY
  generic := f L.generic
  double := f L.double
  pool := L.pool.map f

def mapControlled (f : Nat → Nat) (L : ControlledPointLayout) : ControlledPointLayout where
  core := mapCore f L.core
  control := f L.control
  genericSelect := f L.genericSelect
  doubleSelect := f L.doubleSelect
  infinitySelect := f L.infinitySelect

theorem mapCore_words (f : Nat → Nat) (L : PointAddLayout) :
    (mapCore f L).words = L.words.map (List.map f) := rfl

theorem mapControlled_wires (f : Nat → Nat) (L : ControlledPointLayout) :
    (mapControlled f L).wires = L.wires.map f := by
  simp [mapControlled, mapCore, mapPointReg, ControlledPointLayout.wires,
    ControlledPointLayout.extras, ControlledPointLayout.selectors, PointAddLayout.wires,
    PointAddLayout.pointWires, PointAddLayout.work, PointAddLayout.words, PointAddLayout.flags,
    List.flatten_cons, List.flatten_nil, List.map_append]

theorem mapControlled_widths (f : Nat → Nat) (L : ControlledPointLayout) (hw : L.Widths) :
    (mapControlled f L).Widths := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mapControlled, mapCore, mapPointReg] using hw.inputX
  · simpa [mapControlled, mapCore, mapPointReg] using hw.inputY
  · simpa [mapControlled, mapCore, mapPointReg] using hw.outputX
  · simpa [mapControlled, mapCore, mapPointReg] using hw.outputY
  · intro r hr
    change r ∈ (mapCore f L.core).words at hr
    rw [mapCore_words] at hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    simpa using hw.words s hs
  · simpa [mapControlled, mapCore] using hw.divisor
  · simpa [mapControlled, mapCore] using hw.inverse
  · simpa [mapControlled, mapCore] using hw.pool

theorem mapControlled_nodup (f : Nat → Nat) (hf : Function.Injective f)
    (L : ControlledPointLayout) (hn : L.wires.Nodup) : (mapControlled f L).wires.Nodup := by
  rw [mapControlled_wires]
  exact hn.map hf

/-- The native finite flag is placed on the Streaming infinity port; free X gates
convert polarity. The arithmetic work bank lies above all persistent ports. -/
def streamWire (w : Nat) : Nat :=
  if w = 0 then 836 else if w = 1 then 838 else if w < 258 then w+261
    else if w < 514 then w+322 else w+10000

theorem streamWire_injective : Function.Injective streamWire := by
  intro a b h
  unfold streamWire at h
  split_ifs at h <;> omega

def streamLayout : ControlledPointLayout := mapControlled streamWire ECDSAAdd.Baselines.layout

theorem streamLayout_widths : streamLayout.Widths :=
  mapControlled_widths _ _ ECDSAAdd.Baselines.layout_widths

theorem streamLayout_nodup : streamLayout.wires.Nodup :=
  mapControlled_nodup _ streamWire_injective _ ECDSAAdd.Baselines.layout_nodup

theorem streamLayout_point : streamLayout.point =
    ⟨838, List.range' 263 256, List.range' 580 256⟩ := by
  change (⟨838, _, _⟩ : PointReg) = ⟨838, List.range' 263 256, List.range' 580 256⟩
  congr 1

theorem streamLayout_control : streamLayout.control = 836 := rfl

end
end ShorECDLP.Entrant.WEX

/-! Consolidated module: Main. -/

/-! EDITABLE. Entrant: Shor's ECDLP circuit with the ecdsa.fail controlled point addition.

One observed trial at 263-bit phase precision (two 263-qubit phase registers and one QFT
ancilla), 526 controlled additions of table points, each the Lean-verified finite-addend
circuit of ecdsa.fail (vendored in `ECDSAAdd.Part1..4` and `ECDSALib`) on its 1,898-site
layout, with the control wire renamed to the phase qubit. The generic bridge (`Bridge`) turns
any such provider into the challenge certificate; this module instantiates it.

Resources (all bounds equal the proved counts):
* qubits 2,425 = 1,898 sites of the addition + 526 phase qubits + 1 QFT ancilla;
* T-model 8,157,919,152 = 526 additions × 7 × 2,215,341 Toffoli + 1,033,590 (QFT rotations);
* measurements 818,391,828 = 526 × 1,555,877 + 526 phase-register measurements. -/

/-! ## The ecdsa.fail finite-addend template as the bridge's controlled-addition provider.

Block `j` is the vendored template `finiteT layout (portRow j) (portRowD j)` (control on wire 0,
point register on wires 1..513, workspace `layout.work`), normalised (`CCX a a t ↦ CX a t`) and
read as a bridge template (`gated ↦ when`).  The coefficient table has 528 rows,
`2^i • G` for `i ≤ 263` and `2^i • Q` for `i ≤ 263`: block `j` reads the addend `C` from row
`portRow j` and the ordinate of `-(C + C)` from row `portRowD j = portRow j + 1`.

* Specification: `finiteT_spec` (every addend `2^i • G` and `2^i • d • G` is a finite multiple
  of the generator).
* Static counts: the template's gated instructions are single `X`/`CX` gates on sites of
  `sitesQ layout` (`portGated_finiteT`), so measurements, Toffolis, wires and validity of the
  template follow from one instantiation (`Q = G`); the gated gates add at most 7,706 slots. -/

namespace ShorECDLP.Entrant.Bridge
open Quantum Secp256k1 Challenge NaiveChallenge
open ECDSAAdd.ShorPort (Tmpl finiteT maskedT xorT maskedPointT pairXorT shortXorT bitTestT
  pairTailT zeroWithT pairEqualT shortEqualT constAddT recoveryT genericT cornersT)
noncomputable section

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-! ## Port templates as bridge templates -/


/-! ## The coefficient table -/

section PortTable

end PortTable

/-! ## The provider -/

section PortProvider

end PortProvider

end
end ShorECDLP.Entrant.Bridge

/-! ## Submission -/

namespace ShorECDLP.Entrant.BridgeRegression
open Challenge
noncomputable section

end
end ShorECDLP.Entrant.BridgeRegression


namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
noncomputable section
set_option maxHeartbeats 3000000

theorem pointEffect_eq {r : PointReg} {F : Bool} {X Y : Nat} {s t u : State}
    (ht : PointEffect r F X Y s t) (hu : PointEffect r F X Y s u) : t = u := by
  apply State.extensionality
  · exact ht.phase.trans hu.phase.symm
  funext w
  by_cases hf : w = r.finite
  · subst w; exact ht.finite.trans hu.finite.symm
  by_cases hx : w ∈ r.x
  · apply Bridge.regValue_bits r.x _ _ _ w hx
    simpa only [Bridge.regValueB_eq] using ht.x.trans hu.x.symm
  by_cases hy : w ∈ r.y
  · apply Bridge.regValue_bits r.y _ _ _ w hy
    simpa only [Bridge.regValueB_eq] using ht.y.trans hu.y.symm
  have ho : w ∉ PointAddLayout.pointWires r := by
    simpa only [PointAddLayout.pointWires, List.mem_append, List.mem_cons, not_or] using ⟨⟨hf,hx⟩,hy⟩
  exact (ht.outside w ho).trans (hu.outside w ho).symm

theorem run_append_nil (p q : Program) (s : State) :
    run (p ++ q) ([]) s = run q ([]) (run p ([]) s) := by
  rw [run_append]
  simp

theorem masked_points_commute (r : PointReg) (c d : Wire) (C D : Point)
    (hn : (PointAddLayout.pointWires r).Nodup)
    (hc : c ∉ PointAddLayout.pointWires r) (hd : d ∉ PointAddLayout.pointWires r)
    (hx : r.x.length = 256) (hy : r.y.length = 256) (s : State) :
    run (maskedPointConstant c r C ++ maskedPointConstant d r D) ([]) s =
      run (maskedPointConstant d r D ++ maskedPointConstant c r C) ([]) s := by
  let u := run (maskedPointConstant c r C) ([]) s
  let v := run (maskedPointConstant d r D) ([]) s
  have ec := maskedPointConstant_correct c r C hn hc hx hy s ([])
  have ed := maskedPointConstant_correct d r D hn hd hx hy s ([])
  have edu := maskedPointConstant_correct d r D hn hd hx hy u ([])
  have ecv := maskedPointConstant_correct c r C hn hc hx hy v ([])
  have huq : u.basis d = s.basis d := ec.outside d hd
  have hvq : v.basis c = s.basis c := ed.outside c hc
  rw [huq] at edu
  rw [hvq] at ecv
  rw [run_append_nil, run_append_nil]
  apply pointEffect_eq (ec.trans edu)
  simpa only [Bool.xor_comm, Nat.xor_comm] using ed.trans ecv

def maskChain (r : PointReg) (entries : List (Wire × Point)) : Program :=
  entries.flatMap fun entry => maskedPointConstant entry.1 r entry.2

theorem maskChain_records (r : PointReg) (entries : List (Wire × Point)) :
    measurementCount (maskChain r entries) = 0 := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [maskChain] at ih
    simp [maskChain, maskedPointConstant_counts, ih]

theorem maskChain_commute (r : PointReg) (entries : List (Wire × Point)) (q : Wire) (D : Point)
    (hn : (PointAddLayout.pointWires r).Nodup) (hq : q ∉ PointAddLayout.pointWires r)
    (he : ∀ e ∈ entries, e.1 ∉ PointAddLayout.pointWires r)
    (hx : r.x.length = 256) (hy : r.y.length = 256) (s : State) :
    run (maskChain r entries ++ maskedPointConstant q r D) ([]) s =
      run (maskedPointConstant q r D ++ maskChain r entries) ([]) s := by
  induction entries generalizing s with
  | nil => simp [maskChain]
  | cons entry entries ih =>
    have ht := ih (fun e he' => he e (List.mem_cons_of_mem _ he'))
    have hc := masked_points_commute r entry.1 q entry.2 D hn (he entry (by simp)) hq hx hy s
    rw [run_append_nil, run_append_nil] at hc
    change run ((maskedPointConstant entry.1 r entry.2 ++ maskChain r entries) ++
      maskedPointConstant q r D) ([]) s =
      run (maskedPointConstant q r D ++
        (maskedPointConstant entry.1 r entry.2 ++ maskChain r entries)) ([]) s
    rw [List.append_assoc, run_append_nil, ht, run_append_nil, hc]
    simp only [run_append_nil]

/-- A flagged negative-double clear may be placed before the other corner XORs. -/
theorem negative_corner_replace (K : NegLayout) (q : Wire) (r : PointReg) (D : Point)
    (entries : List (Wire × Point)) (tail : Program) (htail : measurementCount tail = 0)
    (hk : K.word = r.y) (hn : (K.wires q).Nodup)
    (hw : K.work.length = K.word.length) (npos : 0 < K.word.length)
    (hpc : ECDSAAdd.p + SquareReduction.c = 2 ^ K.word.length)
    (hpoint : (PointAddLayout.pointWires r).Nodup) (hq : q ∉ PointAddLayout.pointWires r)
    (he : ∀ e ∈ entries, e.1 ∉ PointAddLayout.pointWires r)
    (hx : r.x.length = 256) (hy : r.y.length = 256)
    (st : State) (hY : ECDSAAdd.regValue r.y st.basis < ECDSAAdd.p)
    (hwork : ECDSAAdd.regValue K.work st.basis = 0) (hcin : st.basis K.cin = false)
    (hzero : st.basis K.zero = false)
    (hcorner : st.basis q = true → Holds.holds st.basis r (-D)) (m : List Bool) :
    run ((K.program q ECDSAAdd.p SquareReduction.c ++ maskedPointConstant q r D) ++
      maskChain r entries ++ tail) m st =
      run (maskChain r entries ++ maskedPointConstant q r (-D) ++ tail) ([]) st := by
  have hc := negative_corner_clear K q r D hk hn hw npos hpc hpoint hq hx hy
    st hY hwork hcin hzero hcorner m
  have hm : measurementCount (maskChain r entries ++ tail) = 0 := by
    rw [measurementCount_append, maskChain_records, htail]
  rw [List.append_assoc, run_append, run_take, run_no_records _ hm, hc]
  have hcomm := maskChain_commute r entries q (-D) hpoint hq he hx hy st
  rw [run_append_nil, run_append_nil] at hcomm
  simpa only [run_append_nil] using congrArg (fun s => run tail ([]) s) hcomm.symm

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
noncomputable section
set_option maxHeartbeats 3000000

theorem negate_physical (K : NegLayout) (q p c : Nat) (hn : (K.wires q).Nodup)
    (hw : K.work.length = K.word.length) : GatePhysical (K.program q p c) := by
  have count := List.nodup_iff_count.mp hn
  have cq : q ∉ K.word := by
    intro hm
    have h := count q
    have hh := List.count_pos_iff.mpr hm
    simp only [CompactRecoveryNegateLayout.wires, List.count_cons, List.count_append,
      beq_self_eq_true, ite_true] at h
    omega
  have nd : (K.cin :: K.word ++ K.carries).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := count w
    have ht := (List.take_sublist (K.word.length-1) K.work).count_le w
    simp only [CompactRecoveryNegateLayout.wires, CompactRecoveryNegateLayout.carries,
      List.count_cons, List.count_append] at h ⊢
    omega
  have away (control : Wire) (hc : control = q ∨ control = K.zero) :
      ∀ w ∈ some control, w ∉ K.cin :: K.word ++ K.carries := by
    intro w hw' hm
    have he : control = w := by simpa using hw'
    subst w
    have h := count control
    have hh := List.count_pos_iff.mpr hm
    have ht := (List.take_sublist (K.word.length-1) K.work).count_le control
    simp only [CompactRecoveryNegateLayout.wires, CompactRecoveryNegateLayout.carries,
      List.count_cons, List.count_append] at h hh
    rcases hc with rfl | rfl <;> simp only [beq_self_eq_true, ite_true] at h <;> omega
  have checkNd : (q :: K.zero :: (zeroPorts K.word K.work).flatMap ZeroBit.wires).Nodup := by
    have perm := zeroPorts_perm K.word K.work hw.symm
    apply List.nodup_iff_count.mpr
    intro w
    have h := count w
    have hperm := perm.count_eq w
    simp only [CompactRecoveryNegateLayout.wires, List.count_cons, List.count_append] at h ⊢
    rw [hperm]
    simp only [List.count_append]
    omega
  have check := equalConstant_physical q K.zero (zeroPorts K.word K.work) 0 checkNd
  have flip := maskedConstant_physical q K.word (2^K.word.length-1) cq
  have add1 := mappedConstAdd_physical (some q) K.word K.carries K.cin (p+1) nd (away q (Or.inl rfl))
  have add2 := mappedConstAdd_physical (some K.zero) K.word K.carries K.cin c nd (away K.zero (Or.inr rfl))
  simp only [CompactRecoveryNegateLayout.program, CompactRecoveryNegateLayout.checkZero,
    CompactRecoveryNegateLayout.complement, CompactRecoveryNegateLayout.add, gatePhysical_append]
  exact ⟨⟨⟨⟨check,flip⟩,add1⟩,add2⟩,check⟩

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
noncomputable section
set_option maxHeartbeats 3000000

def negateYLayout (L : ControlledPointLayout) : NegLayout :=
  ⟨L.point.y, L.dialogPool.take 256, L.core.poolWire 256, L.core.poolWire 257⟩

theorem negateYLayout_pool (L : ControlledPointLayout) (hw : L.Widths) :
    (negateYLayout L).work ++ [(negateYLayout L).cin, (negateYLayout L).zero] =
      L.dialogPool.take 258 := L.recoveryNegate_pool hw

theorem negateYLayout_widths (L : ControlledPointLayout) (hw : L.Widths) :
    (negateYLayout L).word.length = 256 ∧
      (negateYLayout L).work.length = (negateYLayout L).word.length := by
  simp [negateYLayout, ControlledPointLayout.point, hw.inputY, L.dialogPool_length hw]

theorem negateYLayout_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ((negateYLayout L).wires L.core.equalNegY).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 258 L.dialogPool).count_le q
  rw [← negateYLayout_pool L hw] at pool
  simp only [negateYLayout, CompactRecoveryNegateLayout.wires, dialogUsedWires, inPlaceFlags,
    PointAddLayout.pointWires, List.count_cons, List.count_append, List.count_nil] at h pool ⊢
  omega

def cornerEntries (L : ControlledPointLayout) (C : Point) : List (Wire × Point) :=
  [(L.infinitySelect,C), (L.doubleSelect,C), (L.doubleSelect,C+C), (L.genericSelect,-C)]

theorem corners_chain (L : ControlledPointLayout) (C : Point) :
    maskChain L.point (cornerEntries L C) = pointInPlaceCorners L C := by
  simp [maskChain, cornerEntries, pointInPlaceCorners, List.append_assoc]

theorem merged_point_masks (r : PointReg) (c d : Wire) (C : Point)
    (hn : (PointAddLayout.pointWires r).Nodup)
    (hc : c ∉ PointAddLayout.pointWires r)
    (hd : d ∉ PointAddLayout.pointWires r) (hcd : c ≠ d)
    (st : State) (m : List Bool) :
    run (maskedPointConstant c r C ++ maskedPointConstant d r C) m st =
      run ([.CX c d] ++ maskedPointConstant d r C ++ [.CX c d]) m st := by
  apply merge_constant_segments c d ([r.finite] : List Wire) r.x r.y
    (pointFinite C).toNat (pointX C) (pointY C) hcd
  · simpa [PointAddLayout.pointWires] using hc
  · simpa [PointAddLayout.pointWires] using hd
  · simpa [PointAddLayout.pointWires] using hn

theorem run_replace_inside (a b p q : ECDSAAdd.Program)
    (hc : ECDSAAdd.measurementCount p = ECDSAAdd.measurementCount q)
    (he : ∀ m st, ECDSAAdd.run p m st = ECDSAAdd.run q m st)
    (m : List Bool) (st : ECDSAAdd.State) :
    ECDSAAdd.run (a ++ p ++ b) m st = ECDSAAdd.run (a ++ q ++ b) m st := by
  simp only [ECDSAAdd.run_append, ECDSAAdd.measurementCount_append, hc, he]

def mergedInPlaceCorners (L : ControlledPointLayout) (C : Point) : Program :=
  ([.CX L.infinitySelect L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
    [.CX L.infinitySelect L.doubleSelect]) ++
    maskedPointConstant L.doubleSelect L.point (C+C) ++
    maskedPointConstant L.genericSelect L.point (-C)

theorem mergedInPlaceCorners_run (L : ControlledPointLayout) (C : Point)
    (hn : (PointAddLayout.pointWires L.point).Nodup)
    (hc : L.infinitySelect ∉ PointAddLayout.pointWires L.point)
    (hd : L.doubleSelect ∉ PointAddLayout.pointWires L.point)
    (hcd : L.infinitySelect ≠ L.doubleSelect) (st : State) (m : List Bool) :
    run (pointInPlaceCorners L C) m st = run (mergedInPlaceCorners L C) m st := by
  have h := run_replace_inside []
    (maskedPointConstant L.doubleSelect L.point (C+C) ++ maskedPointConstant L.genericSelect L.point (-C))
    (maskedPointConstant L.infinitySelect L.point C ++ maskedPointConstant L.doubleSelect L.point C)
    ([.CX L.infinitySelect L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
      [.CX L.infinitySelect L.doubleSelect])
    (by simp [ECDSAAdd.measurementCount_append, maskedPointConstant_counts, ECDSAAdd.measurementCount])
    (fun m st => merged_point_masks L.point L.infinitySelect L.doubleSelect C hn hc hd hcd st m) m st
  simpa [pointInPlaceCorners, mergedInPlaceCorners, List.append_assoc] using h

def singleRowCorners (L : ControlledPointLayout) (C : Point) : Program :=
  (negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
    maskedPointConstant L.core.equalNegY L.point (C+C) ++
    mergedInPlaceCorners L C ++ maskedPointConstant L.core.equalNegY L.point (-C)

theorem singleRowCorners_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (st : State) (hY : ECDSAAdd.regValue L.point.y st.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool st.basis = 0)
    (hcorner : st.basis L.core.equalNegY = true → Holds.holds st.basis L.point (-(C+C)))
    (m : List Bool) :
    run (singleRowCorners L C) m st = run (pointDialogCorners L C) ([]) st := by
  have width := negateYLayout_widths L hw
  have aux (q : Wire) (hq : q ∈ (negateYLayout L).work ++
      [(negateYLayout L).cin, (negateYLayout L).zero]) : st.basis q = false := by
    rw [negateYLayout_pool L hw] at hq
    exact (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq)
  have flagAway (q : Wire) (hq : q ∈ L.inPlaceFlags) :
      q ∉ PointAddLayout.pointWires L.point := by
    intro bad
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have hb := List.count_pos_iff.mpr bad
    have hf := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at h
    omega
  have hroot : L.core.equalNegY ∉ PointAddLayout.pointWires L.point :=
    flagAway _ (by simp [inPlaceFlags])
  have hentries : ∀ e ∈ cornerEntries L C, e.1 ∉ PointAddLayout.pointWires L.point := by
    intro e he
    simp only [cornerEntries, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact flagAway _ (by simp [inPlaceFlags])
  have hpoint : (PointAddLayout.pointWires L.point).Nodup :=
    (L.dialogUsed_nodup hn).of_append_left.of_append_left.of_append_left
  have heq := negative_corner_replace (negateYLayout L) L.core.equalNegY L.point (C+C)
    (cornerEntries L C) (maskedPointConstant L.core.equalNegY L.point (-C))
    (maskedPointConstant_counts _ _ _).2 rfl (negateYLayout_nodup L hw hn) width.2
    (by rw [width.1]; decide) (by rw [width.1]; norm_num [ECDSAAdd.p, SquareReduction.c])
    hpoint hroot hentries hw.inputX hw.inputY st hY
    ((ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq])))
    (aux _ (by simp)) (aux _ (by simp)) hcorner m
  have hcd : L.infinitySelect ≠ L.doubleSelect := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  have hmerge := run_replace_inside
    ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
      maskedPointConstant L.core.equalNegY L.point (C+C))
    (maskedPointConstant L.core.equalNegY L.point (-C))
    (pointInPlaceCorners L C) (mergedInPlaceCorners L C)
    (by simp [pointInPlaceCorners, mergedInPlaceCorners, ECDSAAdd.measurementCount_append,
      maskedPointConstant_counts, ECDSAAdd.measurementCount])
    (fun m st => mergedInPlaceCorners_run L C hpoint
      (flagAway _ (by simp [inPlaceFlags])) (flagAway _ (by simp [inPlaceFlags])) hcd st m) m st
  have hold : run ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
      maskedPointConstant L.core.equalNegY L.point (C+C) ++ pointInPlaceCorners L C ++
      maskedPointConstant L.core.equalNegY L.point (-C)) m st =
      run (pointDialogCorners L C) ([]) st := by
    simpa only [corners_chain, pointDialogCorners, List.append_assoc] using heq
  have hold' : run (((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
      maskedPointConstant L.core.equalNegY L.point (C+C)) ++ pointInPlaceCorners L C ++
      maskedPointConstant L.core.equalNegY L.point (-C)) m st =
      run (pointDialogCorners L C) ([]) st := by
    simpa only [List.append_assoc] using hold
  simpa only [singleRowCorners, List.append_assoc] using hmerge.symm.trans hold'


def secondCorners (L : ControlledPointLayout) (C : Point) : Program :=
  (negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
  maskedPointConstant L.core.equalNegY L.point (C+C) ++
  ([.CX L.infinitySelect L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
    [.CX L.infinitySelect L.doubleSelect]) ++
  maskedPointConstant L.doubleSelect L.point (C+C) ++
  ([.CX L.genericSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (-C) ++
    [.CX L.genericSelect L.core.equalNegY])

theorem secondCorners_run (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (C : Point) (m : List Bool) (st : State) :
    run (singleRowCorners L C) m st = run (secondCorners L C) m st := by
  have hpoint : (PointAddLayout.pointWires L.point).Nodup :=
    (L.dialogUsed_nodup hn).of_append_left.of_append_left.of_append_left
  have away (q : Wire) (hq : q ∈ L.inPlaceFlags) : q ∉ PointAddLayout.pointWires L.point := by
    intro bad
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have hb := List.count_pos_iff.mpr bad
    have hf := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at h
    omega
  have hcd : L.genericSelect ≠ L.core.equalNegY := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  have h := run_replace_inside
    ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
      maskedPointConstant L.core.equalNegY L.point (C+C) ++
      ([.CX L.infinitySelect L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
        [.CX L.infinitySelect L.doubleSelect]) ++ maskedPointConstant L.doubleSelect L.point (C+C)) ([] : Program)
    (maskedPointConstant L.genericSelect L.point (-C) ++ maskedPointConstant L.core.equalNegY L.point (-C))
    ([.CX L.genericSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (-C) ++
      [.CX L.genericSelect L.core.equalNegY])
    (by simp [ECDSAAdd.measurementCount_append, maskedPointConstant_counts, ECDSAAdd.measurementCount])
    (fun m st => merged_point_masks L.point L.genericSelect L.core.equalNegY (-C) hpoint
      (away _ (by simp [inPlaceFlags])) (away _ (by simp [inPlaceFlags])) hcd st m) m st
  simpa [singleRowCorners, mergedInPlaceCorners, secondCorners, List.append_assoc] using h


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
noncomputable section
set_option maxHeartbeats 3000000

/-- The modified corner block has exactly the original boundary contract. -/
theorem singleRowCorners_boundary [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (hc : C ≠ 0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect = dialogInfinity b R)
    (hd : f L.doubleSelect = dialogDouble b R C)
    (hi : f L.genericSelect = dialogInversePoint b R C)
    (hh : f L.core.equalNegY = dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (singleRowCorners L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro st m hs
  have values := (point_holds _ _ _).mp hs.point
  have hY : ECDSAAdd.regValue L.point.y st.basis < ECDSAAdd.p := by
    rw [values.2.2]
    exact (point_coordinates_lt _).2
  have hcorner : st.basis L.core.equalNegY = true →
      Holds.holds st.basis L.point (-(C+C)) := by
    intro hbit
    have hH : dialogException b R C = true :=
      hh.symm.trans ((hs.flags _ (by simp [inPlaceFlags])).symm.trans hbit)
    have hR : R = dialogExceptionPoint C := by
      simp only [dialogException, Bool.and_eq_true, decide_eq_true_eq] at hH
      exact hH.2
    have hG : dialogOrdinary b R C = false := by
      apply Bool.eq_false_iff.mpr
      intro hg
      exact ((dialogOrdinary_true b R C hc).mp hg).2.2.2.2 hR
    have hpointR := hs.point
    rw [hG] at hpointR
    simpa only [Bool.false_eq_true, if_false, hR, dialogExceptionPoint] using hpointR
  rw [singleRowCorners_eq L hw hn C st hY hs.clean hcorner m]
  exact dialogBoundary_corners L hw hn R C hc b f ho hd hi hh st ([]) hs

theorem secondCorners_boundary [DecidableEq Point] (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (R C : Point) (hc : C ≠ 0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect = dialogInfinity b R)
    (hd : f L.doubleSelect = dialogDouble b R C)
    (hi : f L.genericSelect = dialogInversePoint b R C)
    (hh : f L.core.equalNegY = dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (secondCorners L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro st m hs
  rw [← secondCorners_run L hn C m st]
  exact singleRowCorners_boundary L hw hn R C hc b f ho hd hi hh st m hs

theorem secondCorners_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) :
    toffoliCount (secondCorners L C) = 1022 ∧ measurementCount (secondCorners L C) = 1022 := by
  have widths := negateYLayout_widths L hw
  have counts := negate_256_counts (negateYLayout L) L.core.equalNegY ECDSAAdd.p SquareReduction.c
    widths.2 widths.1
  simp [secondCorners, counts.1, counts.2, maskedPointConstant_counts, toffoliCount, measurementCount]

theorem singleRowCorners_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) : GatePhysical (singleRowCorners L C) := by
  have orig := pointDialogCorners_physical L hn C
  simp only [pointDialogCorners, gatePhysical_append] at orig
  have away : L.core.equalNegY ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires, inPlaceFlags, List.count_append, List.count_cons, List.count_nil,
      beq_self_eq_true, ite_true] at h
    omega
  have neg := negate_physical (negateYLayout L) L.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_nodup L hw hn) (negateYLayout_widths L hw).2
  have mask := maskedPointConstant_physical L.core.equalNegY L.point (C+C) away
  have hcd : L.infinitySelect ≠ L.doubleSelect := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  have cx : GatePhysical [ECDSAAdd.Instr.CX L.infinitySelect L.doubleSelect] := by
    simpa [GatePhysical, ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate] using hcd
  have old := orig.1.1
  simp only [pointInPlaceCorners, gatePhysical_append] at old
  have changed : GatePhysical (mergedInPlaceCorners L C) := by
    simp only [mergedInPlaceCorners, gatePhysical_append]
    tauto
  simpa only [singleRowCorners, gatePhysical_append] using ⟨⟨⟨neg,mask⟩,changed⟩,orig.2⟩


theorem secondCorners_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) : GatePhysical (secondCorners L C) := by
  have old := singleRowCorners_physical L hw hn C
  simp only [singleRowCorners, mergedInPlaceCorners, gatePhysical_append] at old
  have hcd : L.genericSelect ≠ L.core.equalNegY := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  have cx : GatePhysical [ECDSAAdd.Instr.CX L.genericSelect L.core.equalNegY] := by
    simpa [GatePhysical, ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate] using hcd
  simp only [secondCorners, gatePhysical_append]
  tauto


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def finiteOneS_base (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  shortEqual L L.core.equalX L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ Arith.genericS L cx cy ++ secondCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  shortEqual L L.core.double L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

def finiteOneS (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  finiteOneS_base L C cx cy ++ Arith.padding (L.core.poolWire 0) 51716



section OneSpec
attribute [local irreducible] run ECDSAAdd.wires shortEqual pairEqual genericS
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

theorem pointEqual_decide [DecidableEq Point] (R C : Point) : pointEqual R C = decide (R=C) := by
  simp only [pointEqual, pointCode_injective.eq_iff]

-- Adapted from the vendored finite-addend proof, Apache-2.0; the corner block is replaced.
theorem finiteOneS_base_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteOneS_base L (.some hc) cx cy)
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
    simp [pointEqual_decide,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,pointEqual_decide]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,pointEqual_decide]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,pointEqual_decide]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,pointEqual_decide]
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
  have h7 := Arith.boundary_genericS L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := secondCorners_boundary L hw hn R C hC b (dialogFlagState L O D I G E H K)
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
    simpa [E,H,S,dialogExceptionEnabled,pointEqual_decide] using hf.2.2.2
  have h10 := pairFlag_output L hw hn S C (exceptionBit C) b O D I false E H K (by
    simp only [E, exceptionBit, hE])
  rw [heout,Bool.xor_self] at h10
  simp only [pointEqual_decide] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := shortFlag_equalD L hw hn S (C+C) b false D I false E false K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [pointEqual_decide] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false E false K
  simp only [pointEqual_decide] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((h0.seq h1).seq h2).seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq
    h10).seq h11).seq h12).seq h14).seq h15
  simpa only [finiteOneS_base,List.append_assoc,dialogFlagState_zero] using h


theorem finiteOneS_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteOneS L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  exact (finiteOneS_base_spec L hw hn R hc b).seq
    (Arith.padding_boundary L hw (if b then R+.some hc else R) b 51716)

end OneSpec
end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section

attribute [local irreducible] Arith.genericS Arith.padding ECDSAAdd.Frontier.arithS ECDSAAdd.Frontier.SquareOB5.program

theorem finiteOneS_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) (h₁ : decide (cy ≠ -cy) = true) (h₂ : exceptionBit C = true) :
    toffoliCount (finiteOneS L C cx cy) = 2156628 ∧
      measurementCount (finiteOneS L C cx cy) = 1556899 := by
  have old := ECDSAAdd.ShorPort.finiteS_counts L hw hn C cx cy h₁ h₂
  have new := secondCorners_counts L hw C
  have oldg := ECDSAAdd.ShorPort.genericS_counts L hw hn cx cy
  have newg := Arith.genericS_counts L hw hn cx cy
  have pad := Arith.padding_counts (L.core.poolWire 0) 51716
  have zero : toffoliCount (pointDialogCorners L C) = 0 ∧
      measurementCount (pointDialogCorners L C) = 0 := by
    simp [pointDialogCorners, pointInPlaceCorners, maskedPointConstant_counts]
  simp only [finiteOneS,finiteOneS_base, ECDSAAdd.ShorPort.finiteS, toffoliCount_append, measurementCount_append,
    zero.1, zero.2, new.1, new.2] at old ⊢
  constructor <;> omega

theorem finiteOneS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : GatePhysical (finiteOneS L C cx cy) := by
  have old := ECDSAAdd.ShorPort.finiteS_physical L hw hn C cx cy
  have new := secondCorners_physical L hw hn C
  have gen := Arith.genericS_physical L hw hn cx cy
  have pad := Arith.padding_physical (L.core.poolWire 0) 51716
  simp only [finiteOneS,finiteOneS_base, ECDSAAdd.ShorPort.finiteS, gatePhysical_append] at old ⊢
  tauto

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 3000000

def xorWhenT {n : Nat} (value : Bool) : List Wire → (Nat → CBit n) → Tmpl n
  | [], _ => []
  | w :: ws, ref => .gated (ref 0) value (.X w) :: xorWhenT value ws (fun i => ref (i+1))

theorem xorWhenT_false {n : Nat} (read : CBit n → Bool) (ws : List Wire) (ref : Nat → CBit n) :
    (xorWhenT false ws ref).instantiate read = (xorT ws ref).instantiate (fun r => !(read r)) := by
  induction ws generalizing ref with
  | nil => rfl
  | cons w ws ih =>
    simp only [xorWhenT, xorT, Tmpl.instantiate_cons, TInstr.instantiate, ih]
    by_cases h : read (ref 0) = true
    · simp [h]
    · have hf : read (ref 0) = false := Bool.eq_false_iff.mpr h
      simp [hf]

def shortNegT {n : Nat} (L : ControlledPointLayout) (fin : CBit n) (xr : Nat → CBit n)
    (y0 : CBit n) : Tmpl n :=
  [.gated fin false (.X L.point.finite)] ++ xorT L.point.x xr ++
    xorWhenT false (L.point.y.take 1) (fun _ => y0)

theorem shortNegT_inst (read : CBit n → Bool) (L : ControlledPointLayout) (hw : L.Widths)
    (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n) (P : Point)
    (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i)
    (hy : (!read y0) = (pointY P).testBit 0) :
    (shortNegT L fin xr y0).instantiate read = xorConstant (shortSrc L) (shortCode P) := by
  have hxl : L.point.x.length = 256 := hw.inputX
  have hb : (pointFinite P).toNat ≤ 1 := by cases pointFinite P <;> decide
  have hX : pointX P < 2^256 := (point_coordinates_lt P).1.trans (by norm_num [ECDSAAdd.p])
  generalize hm : pointX P + 2^256 * (pointY P % 2) = m
  have hcode : shortCode P = (pointFinite P).toNat + 2 * m := by rw [← hm]; rfl
  have hmod : shortCode P % 2 = (pointFinite P).toNat := by rw [hcode]; omega
  have hdiv : shortCode P / 2 = m := by rw [hcode]; omega
  have hlow : m % 2^256 = pointX P % 2^256 := by
    rw [← hm, Nat.add_mul_mod_self_left]
  have hhigh : m / 2^256 = pointY P % 2 := by
    rw [← hm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt hX, Nat.zero_add]
  have hsrc : shortSrc L = L.point.finite :: (L.point.x ++ L.point.y.take 1) := rfl
  rw [hsrc, xorConstant, hmod, hdiv, xorConstant_append, hxl, hhigh,
    xorConstant_congr L.point.x m (pointX P) (by rw [hxl]; exact hlow)]
  simp only [shortNegT, Tmpl.instantiate_append, xorT_inst read L.point.x xr _ hx,
    List.append_assoc]
  rw [xorWhenT_false]
  rw [xorT_inst (fun r => !(read r)) (L.point.y.take 1) (fun _ => y0) (pointY P % 2) (by
    intro i hi
    have hl := List.length_take_le 1 L.point.y
    have hi0 : i = 0 := by omega
    subst hi0
    change (!read y0) = _
    rw [hy, testBit_zero', testBit_zero', Nat.mod_mod])]
  congr 1
  simp only [Tmpl.instantiate_cons, Tmpl.instantiate_nil, TInstr.instantiate, hf, List.append_nil]
  cases pointFinite P <;> rfl


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd (Wire)
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000

theorem xorWhenT_true {n : Nat} (ws : List Wire) (ref : Nat → ECDSAAdd.ShorPort.CBit n) :
    xorWhenT true ws ref = ECDSAAdd.ShorPort.xorT ws ref := by
  induction ws generalizing ref with
  | nil => rfl
  | cons w ws ih => exact congrArg (List.cons _) (ih (fun i => ref (i+1)))

theorem portTemplate_indexed_when {n : Nat} (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (value : Bool) (address : Nat) :
    portTemplate none (indexedPorts ws refs value) address = xorWhenT value ws (refs address) := by
  induction ws generalizing refs with
  | nil => rfl
  | cons w ws ih =>
    simp only [indexedPorts, portTemplate_cons, xorWhenT]
    exact congrArg (List.cons _) (ih (fun a i => refs a (i+1)))

def wShortNegXor {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  [.lookup none (⟨wBit rows .doubleInfinity, false, L.point.finite⟩ ::
    indexedPorts L.point.x (wFields rows .doubleX) true ++
    indexedPorts (L.point.y.take 1) (fun a _ => wBit rows .doubleY 0 a) false)]

@[simp] theorem specialize_shortNegXor {n : Nat} (L : ControlledPointLayout)
    (rows : Nat → Fin n) (address : Nat) :
    specialize (wShortNegXor L rows) address = shortNegT L
      (wBit rows .doubleInfinity 0 address) (wFields rows .doubleX address) (wBit rows .doubleY 0 address) := by
  simp [wShortNegXor, specialize, WInstr.specialize, shortNegT,
    portTemplate_append, portTemplate_indexed_when, xorWhenT_true]

def wShortNegEqual {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (rows : Nat → Fin n) : WCode n :=
  wShortNegXor L rows ++
    wLiteral (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
    wShortNegXor L rows

def wCornersOne {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c) ++
  wPoint L.core.equalNegY L.point (wBit rows .doubleInfinity) (wFields rows .doubleX)
    (wFields rows .doubleY) ++
  wLiteral ([.CX L.infinitySelect L.doubleSelect]) ++
  wPoint L.doubleSelect L.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral ([.CX L.infinitySelect L.doubleSelect]) ++
  wPoint L.doubleSelect L.point (wBit rows .doubleInfinity) (wFields rows .doubleX)
    (wFields rows .doubleY) ++
  wLiteral ([.CX L.genericSelect L.core.equalNegY]) ++
  wPoint L.core.equalNegY L.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) ++
  wLiteral ([.CX L.genericSelect L.core.equalNegY])

/-- The paired tests share the loaded parity when the two field bits are complementary. -/
def wPairTailOpposite {n : Nat} (y t₁ t₂ : Wire) (r₁ r₂ : Nat → ConstantBit n)
    (w : Wire) : WCode n :=
  [.lookup none ([⟨r₁, false, y⟩]), .literal ([.CCX w y t₁, .X y, .CCX w y t₂]),
    .lookup none ([⟨r₂, false, y⟩])]

def wPairEqualOpposite {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (r₁ r₂ : Nat → ConstantBit n) : WCode n :=
  wPairXor L fin xr ++ wZeroWith (wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂)
    L.control (pairPorts L) ++ wPairXor L fin xr

@[simp] theorem traversals_pairTailOpposite {n : Nat} (y t₁ t₂ : Wire)
    (r₁ r₂ : Nat → ConstantBit n) (w : Wire) :
    traversals (wPairTailOpposite y t₁ t₂ r₁ r₂ w) = 2 := rfl

/-- One-row finite-addend schedule. No reference to a following doubling row occurs. -/
def wFiniteOne {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairEqualOpposite L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortNegEqual L L.core.equalX L.core.equalNegY rows ++
  wLiteral (pointDialogGenericFlag L) ++ wGeneric L rows ++ wCornersOne L rows ++
  wLiteral (pointDialogGenericFlag L) ++
  wPairEqualOpposite L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortEqual L L.core.double L.doubleSelect (wBit rows .doubleInfinity)
    (wFields rows .doubleX) (wBit rows .doubleY) ++
  wLiteral (zeroFlag L.point.finite L.control L.genericSelect) ++
  wLiteral ([.CX L.control L.core.equalX]) ++ wLiteral ([.CX L.control L.core.double]) ++
  wLiteral (Arith.padding (L.core.poolWire 0) 51716)

@[simp] theorem traversals_shortNegXor {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    traversals (wShortNegXor L rows) = 1 := rfl

@[simp] theorem traversals_cornersOne {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    traversals (wCornersOne L rows) = 4 := by simp [wCornersOne]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 4000000

def shortNegEqualT {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n) : Tmpl n :=
  shortNegT L fin xr y0 ++ Tmpl.lit (zeroControlled c t
    (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++ shortNegT L fin xr y0

theorem shortNegEqualT_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (c t : Wire) (fin : CBit n) (xr : Nat → CBit n) (y0 : CBit n)
    (P : Point) (hf : read fin = !pointFinite P)
    (hx : ∀ i < L.point.x.length, read (xr i) = (pointX P).testBit i)
    (hy : (!read y0) = (pointY P).testBit 0) :
    (shortNegEqualT L c t fin xr y0).instantiate read = shortEqual L c t P := by
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  have hsrc := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 258) hsl).1
  simp only [shortNegEqualT, shortEqual, equalConstant, hsrc, Tmpl.instantiate_append,
    Tmpl.instantiate_lit, shortNegT_inst read L hw fin xr y0 P hf hx hy]

@[simp] theorem specialize_shortNegEqual {n : Nat} (L : ControlledPointLayout)
    (c t : Wire) (rows : Nat → Fin n) (address : Nat) :
    specialize (wShortNegEqual L c t rows) address = shortNegEqualT L c t
      (wBit rows .doubleInfinity 0 address) (wFields rows .doubleX address) (wBit rows .doubleY 0 address) := by
  simp [wShortNegEqual, shortNegEqualT]

theorem fieldBits_reads {n : Nat} {read : CBit n → Bool} {row : Fin n} {P : Point}
    (h : RowReads read row P) (f : PointField) (k : Nat) (hk : fieldValue (toA P) f = k) :
    ∀ i < 256, read (fieldBits row f i) = k.testBit i := by
  intro i hi
  rw [fieldBits, h.bit f i hi, hk]

theorem wCornersOne_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (rows : Nat → Fin n) (address : Nat) (C : Point)
    (h : RowReads read (rows address) C) :
    (specialize (wCornersOne L rows) address).instantiate read = secondCorners L C := by
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have fC : read (bitRef (rows address) .infinity 0) = !pointFinite C := by
    rw [h.bit _ 0 (by decide), infinity_bit]
  have fN : read (bitRef (rows address) .infinity 0) = !pointFinite (-C) := by
    rw [fC, ECDSAAdd.ShorPort.pointFinite_neg]
  have fD : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (C+C) := by
    rw [h.bit _ 0 (by decide), doubleInfinity_bit]
  have xC := fieldBits_reads h .x _ (field_x C)
  have yC := fieldBits_reads h .y _ (field_y C)
  have xN : ∀ i < 256, read (fieldBits (rows address) .x i) = (pointX (-C)).testBit i := by
    rw [ECDSAAdd.ShorPort.pointX_neg]
    exact xC
  have yN := fieldBits_reads h .negY _ (field_negY C)
  have xD := fieldBits_reads h .doubleX _ (field_doubleX C)
  have yD := fieldBits_reads h .doubleY _ (field_doubleY C)
  rw [← hxl] at xC xN xD
  rw [← hyl] at yC yN yD
  simp only [wCornersOne, specialize_append, specialize_point, specialize_literal,
    wBit, wFields, Tmpl.instantiate_append, Tmpl.instantiate_lit,
    maskedPointT_inst read _ L.point _ _ _ C fC xC yC,
    maskedPointT_inst read _ L.point _ _ _ (C+C) fD xD yD,
    maskedPointT_inst read _ L.point _ _ _ (-C) fN xN yN,
    secondCorners]
  simp only [List.append_assoc]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 4000000

theorem oppositeTail_inst {n : Nat} (read : CBit n → Bool) (y t₁ t₂ w : Wire)
    (r₁ r₂ : Nat → CBit n) (address : Nat)
    (h : read (r₂ address) = !(read (r₁ address))) :
    (specialize (wPairTailOpposite y t₁ t₂ r₁ r₂ w) address).instantiate read =
      (pairTailT y t₁ t₂ (r₁ address) (r₂ address) w).instantiate read := by
  cases h₁ : read (r₁ address) <;>
    simp [wPairTailOpposite, specialize, WInstr.specialize, portTemplate, pairTailT,
      bitTestT, Tmpl.instantiate, Tmpl.lit, TInstr.instantiate, h₁, h]

theorem oppositeEqual_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (address : Nat)
    (h : read (r₂ address) = !(read (r₁ address))) :
    (specialize (wPairEqualOpposite L t₁ t₂ fin xr r₁ r₂) address).instantiate read =
      (pairEqualT L t₁ t₂ (fin address) (xr address) (r₁ address) (r₂ address)).instantiate read := by
  have hz (c : Wire) (bs : List ZeroBit) :
      (specialize (wZeroWith (wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂) c bs) address).instantiate read =
        (zeroWithT (pairTailT (yLow L) t₁ t₂ (r₁ address) (r₂ address)) c bs).instantiate read := by
    induction bs generalizing c with
    | nil => exact oppositeTail_inst read _ _ _ _ _ _ address h
    | cons b bs ih => simp [wZeroWith, zeroWithT, ih]
  simp only [wPairEqualOpposite, pairEqualT, specialize_append, specialize_pairXor,
    Tmpl.instantiate_append, hz]

theorem wFiniteOne_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (rows : Nat → Fin n) (address : Nat) {cx cy : ECDSAAdd.Fp}
    (hc : curve.toAffine.Nonsingular cx cy) (h : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point) + .some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0) :
    (specialize (wFiniteOne L rows) address).instantiate read = finiteOneS L (.some hc) cx cy := by
  set C : Point := .some hc
  have hxl : L.point.x.length = 256 := hw.inputX
  have fC : read (bitRef (rows address) .infinity 0) = !pointFinite C := by
    rw [h.bit _ 0 (by decide), infinity_bit]
  have fD : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (C+C) := by
    rw [h.bit _ 0 (by decide), doubleInfinity_bit]
  have fH : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (dialogExceptionPoint C) := by
    rw [fD, dialogExceptionPoint, ECDSAAdd.ShorPort.pointFinite_neg]
  have xC := fieldBits_reads h .x _ (field_x C)
  have xD := fieldBits_reads h .doubleX _ (field_doubleX C)
  have xH : ∀ i < 256, read (fieldBits (rows address) .doubleX i) =
      (pointX (dialogExceptionPoint C)).testBit i := by
    rw [dialogExceptionPoint, ECDSAAdd.ShorPort.pointX_neg]
    exact xD
  rw [← hxl] at xC xD xH
  have yC : read (bitRef (rows address) .y 0) = yBit C := by
    rw [h.bit _ 0 (by decide), field_y, yBit_eq]
  have yN : read (bitRef (rows address) .negY 0) = yBit (-C) := by
    rw [h.bit _ 0 (by decide), field_negY, yBit_eq]
  have hy0 : cy ≠ 0 := by
    intro hy
    apply h₁
    simp [hy]
  have hop : read (bitRef (rows address) .negY 0) =
      !(read (bitRef (rows address) .y 0)) := by
    rw [yN, yC, yBit_eq, yBit_eq, pointY_neg]
    exact neg_y_low_bit cy hy0
  have yD : read (bitRef (rows address) .doubleY 0) = (pointY (C+C)).testBit 0 := by
    rw [h.bit _ 0 (by decide), field_doubleY]
  have parity := finite_point_parity (C+C) hD hDo
  rw [yBit_eq, yBit_eq] at parity
  have yH : (!read (bitRef (rows address) .doubleY 0)) =
      (pointY (dialogExceptionPoint C)).testBit 0 := by
    rw [yD, dialogExceptionPoint]
    exact parity.symm
  have e1 : pointInPlaceDoubleEnable L cy = [.CX L.control L.core.double] := by
    unfold pointInPlaceDoubleEnable
    exact if_pos h₁
  have e2 : pointDialogExceptionEnable L C = [.CX L.control L.core.equalX] := by
    unfold pointDialogExceptionEnable
    exact if_pos h₂
  have d1 : decide (cy ≠ -cy) = true := decide_eq_true h₁
  have hp (t₁ t₂ : Wire) :
      (specialize (wPairEqualOpposite L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY)) address).instantiate read =
        pairEqual L t₁ t₂ true true C (-C) := by
    rw [oppositeEqual_inst read L t₁ t₂ _ _ _ _ address (by simpa [wBit] using hop)]
    exact pairEqualT_inst read L t₁ t₂ _ _ _ _ C (-C) fC xC yC yN
  simp only [wFiniteOne, specialize_append, specialize_literal, hp,
    specialize_shortNegEqual, specialize_shortEqual, specialize_generic,
    Tmpl.instantiate_append, Tmpl.instantiate_lit, wBit, wFields,
    finiteOneS,finiteOneS_base, e1, e2, d1, h₂,
    shortNegEqualT_inst read L hw _ _ _ _ _ (dialogExceptionPoint C) fH xH yH,
    shortEqualT_inst read L hw _ _ _ _ _ (C+C) fD xD yD,
    Arith.genericT_inst L hc h, wCornersOne_inst read L hw rows address C h]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 4000000

theorem singleRowCorners_used (L : ControlledPointLayout) (hw : L.Widths)
    (_hn : L.wires.Nodup) (C : Point) :
    ECDSAAdd.wires (singleRowCorners L C) ⊆ L.dialogUsedWires.toFinset := by
  have res (q : Wire) (hq : q ∈ L.inPlaceFlags) : q ∈ L.dialogUsedWires := by
    simp [dialogUsedWires, hq]
  have pointMem (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ L.dialogUsedWires := by
    simp [dialogUsedWires, hq]
  have poolMem (q : Wire) (hq : q ∈ (negateYLayout L).work ++
      [(negateYLayout L).cin, (negateYLayout L).zero]) : q ∈ L.dialogUsedWires := by
    rw [negateYLayout_pool L hw] at hq
    have hp := List.mem_of_mem_take hq
    simp [dialogUsedWires, hp]
  have kn : ECDSAAdd.wires ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c) ⊆
      L.dialogUsedWires.toFinset := by
    apply Finset.Subset.trans ((negateYLayout L).program_support _ _ _ (negateYLayout_widths L hw).2)
    intro q hq
    simp only [CompactRecoveryNegateLayout.wires, List.mem_toFinset, List.mem_cons, List.mem_append] at hq
    apply List.mem_toFinset.mpr
    rcases hq with rfl | rfl | rfl | hq | hq
    · exact res _ (by simp [inPlaceFlags])
    · exact poolMem _ (by simp)
    · exact poolMem _ (by simp)
    · have hy : q ∈ L.point.y := hq
      exact pointMem _ (by simp [PointAddLayout.pointWires, hy])
    · exact poolMem _ (by simp [hq])
  have mask (q : Wire) (hq : q ∈ L.inPlaceFlags) (D : Point) :
      ECDSAAdd.wires (maskedPointConstant q L.point D) ⊆ L.dialogUsedWires.toFinset := by
    apply Finset.Subset.trans (maskedPointConstant_support q L.point D)
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact List.mem_toFinset.mpr (res _ hq)
    · exact List.mem_toFinset.mpr (pointMem w hw)
  have cx : ECDSAAdd.wires ([.CX L.infinitySelect L.doubleSelect]) ⊆ L.dialogUsedWires.toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl <;> exact List.mem_toFinset.mpr (res _ (by simp [inPlaceFlags]))
  have m1 := mask L.core.equalNegY (by simp [inPlaceFlags]) (C+C)
  have m2 := mask L.doubleSelect (by simp [inPlaceFlags]) C
  have m3 := mask L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have m4 := mask L.genericSelect (by simp [inPlaceFlags]) (-C)
  have m5 := mask L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  simp only [singleRowCorners, mergedInPlaceCorners, ECDSAAdd.wires_append, Finset.union_subset_iff]
  tauto

attribute [local irreducible] Arith.genericS Arith.padding ECDSAAdd.Frontier.arithS ECDSAAdd.Frontier.SquareOB5.program

theorem secondCorners_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) : ECDSAAdd.wires (secondCorners L C) ⊆ L.dialogUsedWires.toFinset := by
  have old := singleRowCorners_used L hw hn C
  simp only [singleRowCorners, mergedInPlaceCorners, ECDSAAdd.wires_append, Finset.union_subset_iff] at old
  have cx : ECDSAAdd.wires ([.CX L.genericSelect L.core.equalNegY]) ⊆ L.dialogUsedWires.toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl <;> apply List.mem_toFinset.mpr <;> simp [dialogUsedWires, inPlaceFlags]
  simp only [secondCorners, ECDSAAdd.wires_append, Finset.union_subset_iff]
  tauto

theorem finiteOneS_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) :
    ECDSAAdd.wires (finiteOneS L C cx cy) ⊆ L.dialogUsedWires.toFinset := by
  have old := ECDSAAdd.ShorPort.finiteS_used L hw hn C cx cy
  have new := secondCorners_used L hw hn C
  have gen := Arith.genericS_used L hw hn cx cy
  have pad : ECDSAAdd.wires (Arith.padding (L.core.poolWire 0) 51716) ⊆ L.dialogUsedWires.toFinset := by
    apply Finset.Subset.trans (Arith.padding_support _ _)
    intro q hq
    have he : q = L.core.poolWire 0 := by simpa only [Finset.mem_singleton] using hq
    subst q
    have hm := ECDSAAdd.Frontier.Square5Placement.pool_member L hw 0 (by decide)
    exact List.mem_toFinset.mpr (by simp [dialogUsedWires,hm])
  simp only [finiteOneS,finiteOneS_base, ECDSAAdd.ShorPort.finiteS, ECDSAAdd.wires_append, Finset.union_subset_iff] at old ⊢
  tauto

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 4000000
attribute [local irreducible] run ECDSAAdd.wires

theorem one_boundary_frame (L : ControlledPointLayout) (P : Program)
    (hP : ECDSAAdd.wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem one_boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,
    List.count_cons,List.count_nil] at h1 ht ⊢
  omega

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge
open ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000

theorem finiteOne_literal_counts_of_point {n : Nat} (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) (address : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point) + .some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0) :
    literalToffolis (wFiniteOne L rows) = 2156628 ∧
      literalRecords (wFiniteOne L rows) = 1556899 := by
  let C : Point := .some hc
  let read : CBit n → Bool := fun ref => (fieldValue (toA C) ref.field).testBit ref.bit.val
  have hread : RowReads read (rows address) C := fun _ _ => rfl
  have inst := wFiniteOne_inst read L hw rows address hc hread h₁ h₂ hD hDo
  have counts := finiteOneS_counts L hw hn C cx cy (decide_eq_true h₁) h₂
  have literals := specialize_counts read (wFiniteOne L rows) address
  rw [inst] at literals
  exact ⟨literals.1.symm.trans counts.1, literals.2.symm.trans counts.2⟩

theorem finiteOne_literal_counts {n : Nat} (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) :
    literalToffolis (wFiniteOne L rows) = 2156628 ∧
      literalRecords (wFiniteOne L rows) = 1556899 := by
  let P : Point := Bridge.toB ShorECDLP.Secp256k1.G
  have hP : P ≠ 0 := ShorECDLP.Secp256k1.G_ne_zero
  cases hp : P with
  | zero => exact (hP hp).elim
  | @some cx cy hc =>
    have hk : toA (.some hc) = (1 : Nat) • ShorECDLP.Secp256k1.G := by
      rw [one_nsmul, ← hp]
      rfl
    have en := enables_of_multiple hc 1 hk
    have structural := double_triple_ne_zero (.some hc) 1 hk (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have ho : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0 := by
      rw [← hp]
      change ShorECDLP.order • (ShorECDLP.Secp256k1.G + ShorECDLP.Secp256k1.G) = 0
      rw [nsmul_add, ShorECDLP.Secp256k1.generator_nsmul_eq_zero, zero_add]
    exact finiteOne_literal_counts_of_point L hw hn rows 0 hc en.1 en.2 structural.1 ho

end
end ShorECDLP.Entrant.WEX

-- The assembly supplies the 29-addition producer.


namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 4000000

def flagPrepare (sign flag : Wire) : Program := [.CX sign flag, .X flag]
def flagClear (sign flag : Wire) : Program := [.X flag, .CX sign flag]
def flagPreparedState (sign flag : Wire) (st : State) : State :=
  ⟨st.phase, writeBit st.basis flag (!(st.basis flag ^^ st.basis sign))⟩
def flagClearedState (sign flag : Wire) (st : State) : State :=
  ⟨st.phase, writeBit st.basis flag ((!st.basis flag) ^^ st.basis sign)⟩

theorem flagPrepare_run (sign flag : Wire) (st : State) (m : List Bool) :
    run (flagPrepare sign flag) m st = flagPreparedState sign flag st := by
  apply State.extensionality
  · rfl
  funext w
  by_cases hw : w = flag <;> simp [flagPrepare, flagPreparedState, run, writeBit, hw]

theorem flagClear_run (sign flag : Wire) (hne : sign ≠ flag) (st : State) (m : List Bool) :
    run (flagClear sign flag) m st = flagClearedState sign flag st := by
  apply State.extensionality
  · rfl
  funext w
  by_cases hw : w = flag <;> simp [flagClear, flagClearedState, run, writeBit, hw, hne]

theorem reg_update_outside (ws : List Wire) (s : BasisState) (q : Wire) (b : Bool) (hq : q ∉ ws) :
    ECDSAAdd.regValue ws (writeBit s q b) = ECDSAAdd.regValue ws s := by
  apply ECDSAAdd.Arithmetic.regValue_congr
  intro w hw
  have hn : w ≠ q := fun h => hq (h ▸ hw)
  simp [writeBit, hn]

def signedYProgram (K : NegLayout) (sign flag p c : Nat) : Program :=
  flagPrepare sign flag ++ K.program flag p c ++ flagClear sign flag

/-- A borrowed clean arithmetic flag supplies the negative sign control and is restored. -/
theorem signedYProgram_run (K : NegLayout) (sign flag p c : Nat)
    (hn : (K.wires flag).Nodup) (hw : K.work.length = K.word.length) (npos : 0 < K.word.length)
    (hpc : p+c = 2^K.word.length) (hc : 1 < c) (hsign : sign ∉ K.word) (hsf : sign ≠ flag)
    (st : State) (hflag : st.basis flag = false) (hY : ECDSAAdd.regValue K.word st.basis < p)
    (hwork : ECDSAAdd.regValue K.work st.basis = 0) (hcin : st.basis K.cin = false)
    (hzero : st.basis K.zero = false) (m : List Bool) :
    (run (signedYProgram K sign flag p c) m st).phase = st.phase ∧
      ECDSAAdd.regValue K.word (run (signedYProgram K sign flag p c) m st).basis =
        (if st.basis sign then ECDSAAdd.regValue K.word st.basis
          else (p-ECDSAAdd.regValue K.word st.basis)%p) ∧
      ∀ w ∉ K.word, (run (signedYProgram K sign flag p c) m st).basis w = st.basis w := by
  have head := (List.nodup_cons.mp hn).1
  have fw : flag ∉ K.word := fun h => head (by simp [h])
  have fp : flag ∉ K.work := fun h => head (by simp [h])
  have fc : K.cin ≠ flag := by intro h; apply head; simp [h]
  have fz : K.zero ≠ flag := by intro h; apply head; simp [h]
  let v := flagPreparedState sign flag st
  let u := run (K.program flag p c) m v
  have vword : ECDSAAdd.regValue K.word v.basis = ECDSAAdd.regValue K.word st.basis :=
    reg_update_outside _ _ _ _ fw
  have vn := K.program_correct flag hn hw npos p c (ECDSAAdd.regValue K.word st.basis)
    hpc hc hY v m vword
    ((reg_update_outside _ _ _ _ fp).trans hwork)
    (by simpa [v, flagPreparedState, writeBit, fc] using hcin)
    (by simpa [v, flagPreparedState, writeBit, fz] using hzero)
  have vf : v.basis flag = !(st.basis sign) := by simp [v, flagPreparedState, writeBit, hflag]
  have vs : v.basis sign = st.basis sign := by
    simp [v, flagPreparedState, writeBit, hsf]
  have uf : u.basis flag = !(st.basis sign) := (vn.2.2 _ fw).trans vf
  have us : u.basis sign = st.basis sign := (vn.2.2 _ hsign).trans vs
  have hwhole : run (signedYProgram K sign flag p c) m st = flagClearedState sign flag u := by
    rw [signedYProgram, run_append, run_take, flagClear_run sign flag hsf,
      run_append, show measurementCount (flagPrepare sign flag) = 0 from rfl,
      List.take_zero, List.drop_zero, flagPrepare_run]
  rw [hwhole]
  refine ⟨vn.1, ?_, ?_⟩
  · rw [show ECDSAAdd.regValue K.word (flagClearedState sign flag u).basis =
        ECDSAAdd.regValue K.word u.basis from reg_update_outside _ _ _ _ fw]
    rw [vn.2.1, vf]
    by_cases hb : st.basis sign = true
    · simp [hb]
    · have hf : st.basis sign = false := Bool.eq_false_iff.mpr hb
      simp [hf]
  · intro w hw
    by_cases hf : w = flag
    · subst w
      simp [flagClearedState, writeBit, uf, us, hflag]
    · have hu := vn.2.2 w hw
      simpa [flagClearedState, v, flagPreparedState, writeBit, hf] using hu

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def windowBits : List Wire := List.range' 855 15
def windowPaths : List Wire := List.range' 10000 15
def windowRoot : Wire := 10015
def windowScratch : List Wire := streamLayout.work ++ windowPaths ++ [windowRoot]
def windowReady (s : BasisState) : Prop :=
  Paper2607_13816.ChallengeMigration.BatchedWindowValid s ∧ Clean windowScratch s

theorem mapControlled_work (f : Nat → Nat) (L : ControlledPointLayout) :
    (mapControlled f L).work = L.work.map f := by
  simp [mapControlled, mapCore, mapPointReg, ControlledPointLayout.work,
    ControlledPointLayout.outWork, ControlledPointLayout.temporary, ControlledPointLayout.selectors,
    PointAddLayout.pointWires, PointAddLayout.work, PointAddLayout.words, PointAddLayout.flags,
    List.flatten_cons, List.flatten_nil, List.map_append]

theorem streamWork_lower (w : Wire) (hw : w ∈ streamLayout.work) : 10514 ≤ w := by
  rw [streamLayout, mapControlled_work] at hw
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hw
  have hb := (Bridge.portWork_range n hn).1
  have hn0 : n ≠ 0 := by intro he; subst n; norm_num at hb
  have hn1 : n ≠ 1 := by intro he; subst n; norm_num at hb
  have hn258 : ¬ n < 258 := Nat.not_lt_of_ge ((by decide : 258 ≤ 514).trans hb)
  have hn514 : ¬ n < 514 := Nat.not_lt_of_ge hb
  simp only [streamWire, if_neg hn0, if_neg hn1, if_neg hn258, if_neg hn514]
  exact Nat.add_le_add_right hb 10000

theorem windowScratch_lower (w : Wire) (hw : w ∈ windowScratch) : 10000 ≤ w := by
  simp only [windowScratch, List.mem_append, List.mem_singleton] at hw
  rcases hw with (hw | hw) | hw
  · exact (by decide : 10000 ≤ 10514).trans (streamWork_lower w hw)
  · exact (List.mem_range'_1.mp hw).1
  · rw [hw]; decide

theorem point_wire_small (w : Wire) (hw : w ∈ pointLogicalWires) : w < 1000 := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem windowScratch_point_disjoint (w : Wire) (hw : w ∈ windowScratch) : w ∉ pointLogicalWires := by
  intro hp
  have hl := windowScratch_lower w hw
  have hs := point_wire_small w hp
  dsimp only [Wire] at *
  omega

theorem windowReady_active (s : BasisState) (hs : windowReady s) : s 836 = true := hs.1.1.1.2

theorem windowReady_write (P : Point) (s : BasisState) (hs : windowReady s) :
    windowReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_batchedReady P s hs.1.1, P, pointWrite_coordinates P s⟩, ?_⟩
  intro w hw
  rw [pointWrite_frame P s w (windowScratch_point_disjoint w hw)]
  exact hs.2 w hw

theorem windowReady_address (s : BasisState) (hs : windowReady s)
    (v : Wire) (hv : v ∈ streamAddress) (bit : Bool) : windowReady (s[v ↦ bit]) := by
  refine ⟨batchedWindowValid_address_update s hs.1 v hv bit, ?_⟩
  intro w hw
  have hl := windowScratch_lower w hw
  have hv' : 855 ≤ v ∧ v < 871 := by simpa [streamAddress] using hv
  have hne : w ≠ v := by dsimp only [Wire] at *; omega
  simpa [upd, hne] using hs.2 w hw

theorem windowReady_first (s : BasisState) (hs : FirstWindowInput s) (P : Point) :
    windowReady (pointWrite P s) := by
  refine ⟨firstWindowInput_pointWrite s hs P, ?_⟩
  intro w hw
  rw [pointWrite_frame P s w (windowScratch_point_disjoint w hw)]
  have hl := windowScratch_lower w hw
  apply hs.2 w
  · dsimp only [Wire] at *; omega
  · intro ha
    have : 855 ≤ w ∧ w < 871 := by simpa [streamAddress] using ha
    dsimp only [Wire] at *; omega

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

def StreamPoint (s : BasisState) (P : ECDSAAdd.Secp256k1.Point) : Prop :=
  s 838 = !ECDSAAdd.Arithmetic.pointFinite P ∧
    ECDSAAdd.regValue (List.range' 263 256) s = ECDSAAdd.Arithmetic.pointX P ∧
    ECDSAAdd.regValue (List.range' 580 256) s = ECDSAAdd.Arithmetic.pointY P

theorem fig14_pointCoordinates (P : Point) : fig14PointEncoding P = pointCoordinates P := by
  cases P <;> rfl

theorem StreamPoint.of_coordinates (s : BasisState) (P : Point)
    (hs : Secp256k1ZeroAllowedInputValid s) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    StreamPoint s (Bridge.toB P) := by
  rw [fig14_pointCoordinates] at hP
  have hf := congrArg Prod.fst hP
  have hx := congrArg (fun z : Bool × (Fp × Fp) => z.2.1.val) hP
  have hy := congrArg (fun z : Bool × (Fp × Fp) => z.2.2.val) hP
  simp only [pointStateCoordinates, ZMod.val_natCast] at hx hy
  rw [Nat.mod_eq_of_lt hs.2.2.1] at hx
  rw [Nat.mod_eq_of_lt hs.2.2.2] at hy
  refine ⟨hf.trans (ECDSAAdd.ShorPort.coords_finite (Bridge.toB P)), ?_, ?_⟩
  · rw [Bridge.regValueB_eq, regValue_wireValues]
    exact hx.trans (ECDSAAdd.ShorPort.coords_x (Bridge.toB P))
  · rw [Bridge.regValueB_eq, regValue_wireValues]
    exact hy.trans (ECDSAAdd.ShorPort.coords_y (Bridge.toB P))

theorem StreamPoint.state_eq (s t : BasisState) (P : Point)
    (hs : Secp256k1ZeroAllowedInputValid s) (ht : StreamPoint t (Bridge.toB P))
    (hf : ∀ w ∉ pointLogicalWires, t w = s w) : t = pointWrite P s := by
  have hp := StreamPoint.of_coordinates (pointWrite P s) P
    (pointWrite_valid P s hs) (pointWrite_coordinates P s)
  funext w
  by_cases hfinite : w = 838
  · subst w; exact ht.1.trans hp.1.symm
  by_cases hx : w ∈ List.range' 263 256
  · exact Bridge.regValue_bits _ _ _ (by
      simpa only [Bridge.regValueB_eq] using ht.2.1.trans hp.2.1.symm) w hx
  by_cases hy : w ∈ List.range' 580 256
  · exact Bridge.regValue_bits _ _ _ (by
      simpa only [Bridge.regValueB_eq] using ht.2.2.trans hp.2.2.symm) w hy
  have ho : w ∉ pointLogicalWires := by
    simpa only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] using ⟨hx,hy,hfinite⟩
  exact (hf w ho).trans (pointWrite_frame P s w ho).symm

end
end ShorECDLP.Entrant.WEX

/-! Coherent WEX window adapter for the body-parametric Streaming certificate. -/

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
attribute [local irreducible] run ECDSAAdd.regValue

theorem negateYLayout_nodup_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ((negateYLayout L).wires L.core.generic).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 258 L.dialogPool).count_le q
  rw [← negateYLayout_pool L hw] at pool
  simp only [negateYLayout, CompactRecoveryNegateLayout.wires, dialogUsedWires, inPlaceFlags,
    PointAddLayout.pointWires, List.count_cons, List.count_append, List.count_nil] at h pool ⊢
  omega

def windowSignProgram : Program := signedYProgram (negateYLayout streamLayout) 870
  streamLayout.core.generic ECDSAAdd.p SquareReduction.c

theorem windowSignProgram_point (st : State) (P : Point)
    (hs : StreamPoint st.basis P) (hc : ECDSAAdd.regValue streamLayout.work st.basis = 0)
    (m : List Bool) :
    (run windowSignProgram m st).phase = st.phase ∧
      StreamPoint (run windowSignProgram m st).basis (if st.basis 870 then P else -P) ∧
      ∀ w ∉ List.range' 580 256, (run windowSignProgram m st).basis w = st.basis w := by
  let L := streamLayout
  let K := negateYLayout L
  have width := negateYLayout_widths L streamLayout_widths
  have word : K.word = List.range' 580 256 := by
    change L.point.y = _
    rw [streamLayout_point]
  have genWork : L.core.generic ∈ L.work := one_boundary_work_subset L
    (List.mem_append_left _ (by simp [inPlaceFlags]))
  have genFalse : st.basis L.core.generic = false := (regValue_zero _ _).mp hc _ genWork
  have clean (q : Wire) (hq : q ∈ K.work ++ [K.cin,K.zero]) : st.basis q = false := by
    change q ∈ (negateYLayout L).work ++ [(negateYLayout L).cin,(negateYLayout L).zero] at hq
    rw [negateYLayout_pool L streamLayout_widths] at hq
    exact (regValue_zero _ _).mp hc q (one_boundary_work_subset L
      (List.mem_append_right _ (List.mem_of_mem_take hq)))
  have signNe : (870 : Wire) ≠ L.core.generic := by
    have h := streamWork_lower _ genWork
    dsimp only [Wire] at *
    omega
  have hY : ECDSAAdd.regValue K.word st.basis < ECDSAAdd.p := by
    rw [word, hs.2.2]
    exact (point_coordinates_lt P).2
  have h := signedYProgram_run K 870 L.core.generic ECDSAAdd.p SquareReduction.c
    (negateYLayout_nodup_generic L streamLayout_widths streamLayout_nodup) width.2
    (by rw [width.1]; decide) (by rw [width.1]; norm_num [ECDSAAdd.p,SquareReduction.c])
    (by norm_num [SquareReduction.c]) (by rw [word]; decide +kernel) signNe
    st genFalse hY ((regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq])))
    (clean _ (by simp)) (clean _ (by simp)) m
  change (run windowSignProgram m st).phase = _ ∧ _ at h
  rw [word] at h
  have hyOut : ECDSAAdd.regValue (List.range' 580 256) (run windowSignProgram m st).basis =
      (if st.basis 870 then ECDSAAdd.regValue (List.range' 580 256) st.basis else
        (ECDSAAdd.p-ECDSAAdd.regValue (List.range' 580 256) st.basis)%ECDSAAdd.p) := h.2.1
  have hf : (run windowSignProgram m st).basis 838 = st.basis 838 := h.2.2 _ (by decide +kernel)
  have hx : ECDSAAdd.regValue (List.range' 263 256) (run windowSignProgram m st).basis =
      ECDSAAdd.regValue (List.range' 263 256) st.basis := by
    apply ECDSAAdd.Arithmetic.regValue_congr
    intro w hw
    apply h.2.2 w
    simp only [List.mem_range'_1] at hw ⊢
    dsimp only [Wire] at *
    omega
  refine ⟨h.1, ?_, h.2.2⟩
  by_cases hsign : st.basis 870 = true
  · simp only [hsign, if_true]
    refine ⟨hf.trans hs.1, hx.trans hs.2.1, ?_⟩
    have hyEq : ECDSAAdd.regValue (List.range' 580 256) (run windowSignProgram m st).basis =
        ECDSAAdd.regValue (List.range' 580 256) st.basis := by simpa [hsign] using hyOut
    exact hyEq.trans hs.2.2
  · have hfalse : st.basis 870 = false := Bool.eq_false_iff.mpr hsign
    simp only [hfalse, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ECDSAAdd.ShorPort.pointFinite_neg] using hf.trans hs.1
    · simpa only [ECDSAAdd.ShorPort.pointX_neg] using hx.trans hs.2.1
    · have hyEq : ECDSAAdd.regValue (List.range' 580 256) (run windowSignProgram m st).basis =
          (ECDSAAdd.p-pointY P)%ECDSAAdd.p := by simpa [hfalse, hs.2.2] using hyOut
      exact hyEq.trans (pointY_neg_mod P).symm

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

def liveReady (s : BasisState) : Prop :=
  Paper2607_13816.ChallengeMigration.BatchedWindowValid s ∧
    Clean (streamLayout.work ++ windowPaths) s ∧ s windowRoot = true

theorem liveReady_write (P : Point) (s : BasisState) (hs : liveReady s) : liveReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_batchedReady P s hs.1.1, P, pointWrite_coordinates P s⟩, ?_, ?_⟩
  · intro w hw
    rw [pointWrite_frame P s w (windowScratch_point_disjoint w (List.mem_append_left _ hw))]
    exact hs.2.1 w hw
  · rw [pointWrite_frame P s windowRoot (windowScratch_point_disjoint windowRoot (by simp [windowScratch]))]
    exact hs.2.2

def inputPoint (s : BasisState) : Point := by
  classical
  exact if h : ∃ P, pointStateCoordinates s = fig14PointEncoding P then Classical.choose h else 0

theorem inputPoint_eq (s : BasisState) (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    inputPoint s = P := by
  classical
  let hex : ∃ R : Point, pointStateCoordinates s = fig14PointEncoding R := ⟨P,hP⟩
  rw [inputPoint, dif_pos hex]
  apply fig14PointEncoding_injective
  exact (Classical.choose_spec hex).symm.trans hP

def signPointState (s : BasisState) : BasisState :=
  pointWrite (if s 870 then inputPoint s else -inputPoint s) s

theorem windowSign_coherent : CoherentlyImplementsOn
    (literalSource (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady := by
  apply literal_coherent
  intro s hs m
  rw [ECDSAAdd.Baselines.normalize_run]
  obtain ⟨P,hP⟩ := hs.1.2
  have secp := hs.1.1.1.1
  have point := StreamPoint.of_coordinates s P secp hP
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr
      (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h := windowSignProgram_point ⟨false,s⟩ (Bridge.toB P) point work m
  apply ECDSAAdd.State.extensionality
  · exact h.1
  unfold signPointState
  rw [inputPoint_eq s P hP]
  apply StreamPoint.state_eq s _ _ secp
  · by_cases hb : s 870 = true
    · simpa [hb] using h.2.1
    · have hf : s 870 = false := Bool.eq_false_iff.mpr hb
      simpa [hf, Bridge.toB_neg] using h.2.1
  · intro w hw
    apply h.2.2 w
    intro hy
    exact hw (by simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, hy])

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
attribute [local irreducible] run ECDSAAdd.regValue

def flipInfinity (s : BasisState) : BasisState := writeBit s 838 (!s 838)

theorem flipInfinity_holds (s : BasisState) (P : Point) (hs : StreamPoint s P) :
    Holds.holds (flipInfinity s) streamLayout.point P := by
  apply (point_holds _ _ _).mpr
  rw [streamLayout_point]
  refine ⟨?_, ?_, ?_⟩
  · simp [flipInfinity, writeBit, hs.1]
  · exact (reg_update_outside (List.range' 263 256) s 838 (!s 838) (by decide +kernel)).trans hs.2.1
  · exact (reg_update_outside (List.range' 580 256) s 838 (!s 838) (by decide +kernel)).trans hs.2.2

theorem flipInfinity_stream (s : BasisState) (P : Point)
    (hs : Holds.holds s streamLayout.point P) : StreamPoint (flipInfinity s) P := by
  have h := (point_holds _ _ _).mp hs
  rw [streamLayout_point] at h
  refine ⟨?_, ?_, ?_⟩
  · simp [flipInfinity, writeBit, h.1]
  · exact (reg_update_outside (List.range' 263 256) s 838 (!s 838) (by decide +kernel)).trans h.2.1
  · exact (reg_update_outside (List.range' 580 256) s 838 (!s 838) (by decide +kernel)).trans h.2.2

theorem native_point_mem (w : Wire) :
    w ∈ PointAddLayout.pointWires streamLayout.point ↔ w ∈ pointLogicalWires := by
  rw [streamLayout_point]
  simp only [PointAddLayout.pointWires, pointLogicalWires, pointCorrectionX, pointCorrectionYInf,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem flip_run (st : State) (m : List Bool) :
    run ([.X 838]) m st = ⟨st.phase, flipInfinity st.basis⟩ := by
  simp only [run, flipInfinity]

/-- The native point adder, bracketed by free finite/infinity flag conversions. -/
theorem rowAdd_stream_run (s : BasisState) (P : ShorECDLP.Secp256k1.Point)
    (hs : Secp256k1ZeroAllowedInputValid s) (hp : pointStateCoordinates s = fig14PointEncoding P)
    (hq : s 836 = true) (hcwork : ECDSAAdd.regValue streamLayout.work s = 0)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (m : List Bool) :
    run (([.X 838]) ++ finiteOneS streamLayout (.some hc) cx cy ++ ([.X 838])) m ⟨false,s⟩ =
      ⟨false, pointWrite (P + toA (.some hc)) s⟩ := by
  let L := streamLayout
  let v : State := ⟨false, flipInfinity s⟩
  let u := run (finiteOneS L (.some hc) cx cy) m v
  have hpoint := flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs hp)
  have h838 : (838 : Wire) ∉ L.work := by
    intro hm
    have h := streamWork_lower _ hm
    norm_num at h
  have work : ECDSAAdd.regValue L.work v.basis = 0 :=
    (reg_update_outside _ _ _ _ h838).trans hcwork
  have clean (w : Wire) (hw : w ∈ L.inPlaceFlags ++ L.dialogPool) : v.basis w = false :=
    (regValue_zero _ _).mp work w (one_boundary_work_subset L hw)
  have q : v.basis L.control = true := by
    change flipInfinity s 836 = true
    simpa [flipInfinity, writeBit] using hq
  have hi : PointDialogBoundary L (Bridge.toB P) true (fun _ => false) v.basis := by
    exact ⟨hpoint, q, fun w hw => clean w (by simp [hw]),
      (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))⟩
  have result := finiteOneS_spec L streamLayout_widths streamLayout_nodup (Bridge.toB P) hc true v m hi
  have hout : Holds.holds u.basis L.point (Bridge.toB P + .some hc) := by
    simpa only [if_true] using result.2.point
  have out := flipInfinity_stream u.basis (Bridge.toB P + .some hc) hout
  have frame (w : Wire) (hw : w ∉ pointLogicalWires) : flipInfinity u.basis w = s w := by
    have hpw : w ∉ PointAddLayout.pointWires L.point := fun h => hw ((native_point_mem w).mp h)
    have h838w : w ≠ 838 := fun h => hw (by simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, h])
    have f := one_boundary_frame L _ (finiteOneS_used L streamLayout_widths streamLayout_nodup _ cx cy)
      (Bridge.toB P) _ true v m hi result.2 w hpw
    simpa [v, flipInfinity, writeBit, h838w] using f
  have eq : flipInfinity u.basis = pointWrite (P + toA (.some hc)) s := by
    apply StreamPoint.state_eq s _ _ hs
    · exact out
    · exact frame
  have hwhole : run (([.X 838]) ++ finiteOneS L (.some hc) cx cy ++ ([.X 838])) m ⟨false,s⟩ =
      ⟨u.phase, flipInfinity u.basis⟩ := by
    rw [run_append, run_take, flip_run, run_append,
      show measurementCount ([.X 838]) = 0 from rfl, List.take_zero, List.drop_zero, flip_run]
  rw [hwhole]
  apply State.extensionality
  · exact result.1
  · exact eq

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout
open ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem literal_instr_subset {n : Nat} (read : CBit n → Bool) (code : WCode n)
    (address : Nat) (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ code)
    (i : ECDSAAdd.Instr) (hi : i ∈ p) : i ∈ (specialize code address).instantiate read := by
  induction code with
  | nil => simp at hp
  | cons j code ih =>
    simp only [specialize, List.flatMap_cons, Tmpl.instantiate_append]
    rcases List.mem_cons.mp hp with hj | hj
    · cases hj
      exact List.mem_append_left _ (by simpa [WInstr.specialize, Tmpl.instantiate_lit] using hi)
    · exact List.mem_append_right _ (ih hj)

theorem finiteOne_literal_facts {n : Nat} (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (rows : Nat → Fin n) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ wFiniteOne L rows) :
    ECDSAAdd.wires p ⊆ L.dialogUsedWires.toFinset ∧ GatePhysical p := by
  let P : Point := Bridge.toB ShorECDLP.Secp256k1.G
  have hP : P ≠ 0 := ShorECDLP.Secp256k1.G_ne_zero
  cases hgen : P with
  | zero => exact (hP hgen).elim
  | @some cx cy hc =>
    let C : Point := .some hc
    let read : CBit n → Bool := fun ref => (fieldValue (toA C) ref.field).testBit ref.bit.val
    have hr : RowReads read (rows 0) C := fun _ _ => rfl
    have hk : toA C = (1 : Nat) • ShorECDLP.Secp256k1.G := by
      rw [one_nsmul]
      change toA (.some hc) = _
      rw [← hgen]
      rfl
    have en := enables_of_multiple hc 1 hk
    have structural := double_triple_ne_zero C 1 hk (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have ho : ShorECDLP.order • (C+C) = 0 := by
      change ShorECDLP.order • ((.some hc : Point)+.some hc) = 0
      rw [← hgen]
      change ShorECDLP.order • (ShorECDLP.Secp256k1.G+ShorECDLP.Secp256k1.G) = 0
      rw [nsmul_add, ShorECDLP.Secp256k1.generator_nsmul_eq_zero, zero_add]
    have inst := wFiniteOne_inst read L hw rows 0 hc hr en.1 en.2 structural.1 ho
    have used := finiteOneS_used L hw hn C cx cy
    have phys := finiteOneS_physical L hw hn C cx cy
    rw [← inst] at used phys
    refine ⟨(literal_wires_subset read _ 0 p hp).trans used, ?_⟩
    intro i hi
    exact phys i (literal_instr_subset read _ 0 p hp i hi)

@[simp] theorem geometry_shortNegXor {n : Nat} (bits paths : List Wire) (root : Wire)
    (L : ControlledPointLayout) (rows : Nat → Fin n) :
    geometryCodeOK bits paths root (wShortNegXor L rows) =
      geometryOK bits paths root none (L.point.finite :: (L.point.x ++ L.point.y.take 1)) := by
  simp only [geometryCodeOK, wShortNegXor, List.all_cons, List.all_nil, Bool.and_true, lookupPlacedOK]
  congr 1
  simp only [portTargets, List.map_cons, List.map_append]
  rw [show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _,
    show List.map LookupPort.target _ = _ from indexedPorts_targets _ _ _]
  rfl

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
@[simp] theorem literalRecords_append {n : Nat} (xs ys : WCode n) :
    literalRecords (xs ++ ys) = literalRecords xs + literalRecords ys := by
  induction xs with
  | nil => simp [literalRecords]
  | cons x xs ih => cases x <;> simp [literalRecords,ih,Nat.add_assoc]

@[simp] theorem literalToffolis_append {n : Nat} (xs ys : WCode n) :
    literalToffolis (xs ++ ys) = literalToffolis xs + literalToffolis ys := by
  induction xs with
  | nil => simp [literalToffolis]
  | cons x xs ih => cases x <;> simp [literalToffolis,ih,Nat.add_assoc]

theorem x_disjoint_commutes (p : Program) (y : Wire) (hy : y ∉ wires p)
    (m n : List Bool) (s : State) :
    run p m (run [.X y] n s) = run [.X y] n (run p m s) := by
  apply run_disjoint_commute
  apply Finset.disjoint_left.mpr
  intro w hp hq
  have : w = y := by simpa [wires, Instr.wires] using hq
  subst w
  exact hy hp


open ECDSAAdd.Entrant

def chainPrefix (c : Wire) : List ZeroBit → Program
  | [] => []
  | b :: bs => chainAnd c b.input b.work ++ chainPrefix b.work bs

def chainSuffix (c : Wire) : List ZeroBit → Program
  | [] => []
  | b :: bs => chainSuffix b.work bs ++ chainErase c b.input b.work

def chainLast (c : Wire) : List ZeroBit → Wire
  | [] => c
  | b :: bs => chainLast b.work bs

theorem zeroWith_split (T : Wire → Program) (c : Wire) (bs : List ZeroBit) :
    zeroWith T c bs = chainPrefix c bs ++ T (chainLast c bs) ++ chainSuffix c bs := by
  induction bs generalizing c with
  | nil => simp [zeroWith, chainPrefix, chainSuffix, chainLast]
  | cons b bs ih => simp [zeroWith, chainPrefix, chainSuffix, chainLast, ih, List.append_assoc]

theorem prefix_avoids (c y : Wire) (bs : List ZeroBit)
    (hy : y ∉ c :: bs.flatMap ZeroBit.wires) : y ∉ wires (chainPrefix c bs) := by
  induction bs generalizing c with
  | nil => simp [chainPrefix, wires]
  | cons b bs ih =>
    have hs : y ≠ c ∧ y ≠ b.input ∧ y ≠ b.work ∧ y ∉ bs.flatMap ZeroBit.wires := by
      simpa [ZeroBit.wires] using hy
    simp only [chainPrefix, wires_append, Finset.mem_union, not_or]
    exact ⟨by simp [chainAnd, wires, Instr.wires, hs.1, hs.2.1, hs.2.2.1],
      ih b.work (by simpa [hs.2.2.1] using hs.2.2.2)⟩

theorem suffix_avoids (c y : Wire) (bs : List ZeroBit)
    (hy : y ∉ c :: bs.flatMap ZeroBit.wires) : y ∉ wires (chainSuffix c bs) := by
  induction bs generalizing c with
  | nil => simp [chainSuffix, wires]
  | cons b bs ih =>
    have hs : y ≠ c ∧ y ≠ b.input ∧ y ≠ b.work ∧ y ∉ bs.flatMap ZeroBit.wires := by
      simpa [ZeroBit.wires] using hy
    simp only [chainSuffix, wires_append, Finset.mem_union, not_or]
    exact ⟨ih b.work (by simpa [hs.2.2.1] using hs.2.2.2),
      by simp [chainErase, wires, Instr.wires, correctionWires, hs.1, hs.2.1, hs.2.2.1]⟩


theorem x_cross_program (p : Program) (y : Wire) (hy : y ∉ wires p)
    (m : List Bool) (s : State) :
    run ([.X y] ++ p) m s = run (p ++ [.X y]) m s := by
  rw [run_append, run_append]
  simp only [measurementCount, List.take_zero, List.drop_zero, run_take]
  simpa [run] using x_disjoint_commutes p y hy m ([] : List Bool) s


def conditionalX (b : Bool) (y : Wire) : Program := if b then [.X y] else []

theorem conditionalX_cross (p : Program) (y : Wire) (b : Bool) (hy : y ∉ wires p)
    (m : List Bool) (s : State) :
    run (conditionalX b y ++ p) m s = run (p ++ conditionalX b y) m s := by
  cases b with
  | false => simp [conditionalX]
  | true => simpa only [conditionalX, if_true] using x_cross_program p y hy m s

theorem run_equiv_prefix {p q : Program}
    (hc : measurementCount p = measurementCount q)
    (he : ∀ m s, run p m s = run q m s) (tail : Program) (m : List Bool) (s : State) :
    run (p ++ tail) m s = run (q ++ tail) m s := by
  rw [run_append, run_append, hc, he]

theorem run_equiv_suffix {p q : Program}
    (he : ∀ m s, run p m s = run q m s) (head : Program) (m : List Bool) (s : State) :
    run (head ++ p) m s = run (head ++ q) m s := by
  rw [run_append, run_append, he]


theorem move_pair_parities (pre tail post : Program) (y : Wire) (b₁ b₂ : Bool)
    (hp : y ∉ wires pre) (hq : y ∉ wires post) (m : List Bool) (s : State) :
    run (pre ++ conditionalX b₁ y ++ tail ++ conditionalX b₂ y ++ post) m s =
      run (conditionalX b₁ y ++ pre ++ tail ++ post ++ conditionalX b₂ y) m s := by
  have hcount : measurementCount (pre ++ conditionalX b₁ y) =
      measurementCount (conditionalX b₁ y ++ pre) := by
    cases b₁ <;> simp [conditionalX, measurementCount_append, measurementCount]
  have hleft := run_equiv_prefix hcount
    (fun m s => (conditionalX_cross pre y b₁ hp m s).symm)
    (tail ++ conditionalX b₂ y ++ post) m s
  have hright := run_equiv_suffix
    (fun m s => conditionalX_cross post y b₂ hq m s)
    (conditionalX b₁ y ++ pre ++ tail) m s
  simp only [List.append_assoc] at hleft hright ⊢
  exact hleft.trans hright


open ShorECDLP.Quantum ShorECDLP.Challenge
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.ShorPort

def wPairXorParity {n : Nat} (L : ControlledPointLayout) (fin : Nat → ConstantBit n)
    (xr : Nat → Nat → ConstantBit n) (yr : Nat → ConstantBit n) : WCode n :=
  [.lookup none (⟨fin, false, L.point.finite⟩ :: indexedPorts L.point.x xr true ++
    [⟨yr, false, yLow L⟩])]

theorem pairXorParity_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (yr : Nat → CBit n) (address : Nat) :
    (specialize (wPairXorParity L fin xr yr) address).instantiate read =
      (pairXorT L (fin address) (xr address)).instantiate read ++
        conditionalX (!read (yr address)) (yLow L) := by
  cases h : read (yr address) <;>
    simp [wPairXorParity, specialize, WInstr.specialize, portTemplate_append,
      pairXorT, portTemplate_indexed_none, Tmpl.instantiate,
      TInstr.instantiate, conditionalX, h]


def wPairTailBare {n : Nat} (y t₁ t₂ w : Wire) : WCode n :=
  wLiteral ([.CCX w y t₁, .X y, .CCX w y t₂])

def wPairEqualTight {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) : WCode n :=
  wPairXorParity L fin xr r₁ ++ wZeroWith (wPairTailBare (yLow L) t₁ t₂)
    L.control (pairPorts L) ++ wPairXorParity L fin xr r₂

theorem tight_traversals {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) :
    traversals (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) = 2 := by
  have hz : traversals (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂)
      L.control (pairPorts L)) = 0 :=
    traversals_zeroWith _ 0 (fun _ => rfl) _ _
  simp only [wPairEqualTight, traversals_append, hz]
  rfl


theorem tight_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (address : Nat) :
    (specialize (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) address).instantiate read =
      (pairXorT L (fin address) (xr address)).instantiate read ++
      conditionalX (!read (r₁ address)) (yLow L) ++
      chainPrefix L.control (pairPorts L) ++
      [.CCX (chainLast L.control (pairPorts L)) (yLow L) t₁, .X (yLow L),
       .CCX (chainLast L.control (pairPorts L)) (yLow L) t₂] ++
      chainSuffix L.control (pairPorts L) ++
      (pairXorT L (fin address) (xr address)).instantiate read ++
      conditionalX (!read (r₂ address)) (yLow L) := by
  have hz :
      (specialize (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂) L.control (pairPorts L))
        address).instantiate read =
      zeroWith (fun w => [.CCX w (yLow L) t₁, .X (yLow L), .CCX w (yLow L) t₂])
        L.control (pairPorts L) := by
    rw [specialize_zeroWith _ (fun w => Tmpl.lit [.CCX w (yLow L) t₁, .X (yLow L),
      .CCX w (yLow L) t₂]) address (fun w => by simp [wPairTailBare])]
    apply zeroWithT_inst
    intro w
    simp
  simp only [wPairEqualTight, specialize_append, Tmpl.instantiate_append, pairXorParity_inst, hz,
    zeroWith_split, List.append_assoc]


theorem oldTail_inst {n : Nat} (read : CBit n → Bool) (y t₁ t₂ w : Wire)
    (r₁ r₂ : CBit n) (h : read r₂ = !(read r₁)) :
    (pairTailT y t₁ t₂ r₁ r₂ w).instantiate read =
      conditionalX (!read r₁) y ++ [.CCX w y t₁, .X y, .CCX w y t₂] ++
        conditionalX (!read r₂) y := by
  cases hr : read r₁ <;> simp [pairTailT, bitTestT, Tmpl.instantiate,
    TInstr.instantiate, conditionalX, h, hr]

theorem oldPair_inst {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (address : Nat) (h : read (r₂ address) = !(read (r₁ address))) :
    (specialize (wPairEqual L t₁ t₂ fin xr r₁ r₂) address).instantiate read =
      (pairXorT L (fin address) (xr address)).instantiate read ++
      chainPrefix L.control (pairPorts L) ++ conditionalX (!read (r₁ address)) (yLow L) ++
      [.CCX (chainLast L.control (pairPorts L)) (yLow L) t₁, .X (yLow L),
       .CCX (chainLast L.control (pairPorts L)) (yLow L) t₂] ++
      conditionalX (!read (r₂ address)) (yLow L) ++ chainSuffix L.control (pairPorts L) ++
      (pairXorT L (fin address) (xr address)).instantiate read := by
  rw [specialize_pairEqual, pairEqualT, Tmpl.instantiate_append, Tmpl.instantiate_append]
  rw [zeroWithT_inst read _ _ (fun w => oldTail_inst read _ _ _ w _ _ h), zeroWith_split]
  simp only [List.append_assoc]


theorem move_pair_with_mask (mask pre middle post : Program) (y : Wire) (b₁ b₂ : Bool)
    (hm : y ∉ wires mask) (hp : y ∉ wires pre) (hq : y ∉ wires post)
    (m : List Bool) (s : ECDSAAdd.State) :
    run (mask ++ pre ++ conditionalX b₁ y ++ middle ++ conditionalX b₂ y ++ post ++ mask) m s =
      run (mask ++ conditionalX b₁ y ++ pre ++ middle ++ post ++ mask ++ conditionalX b₂ y) m s := by
  have hcount : measurementCount (pre ++ conditionalX b₁ y ++ middle ++ conditionalX b₂ y ++ post) =
      measurementCount (conditionalX b₁ y ++ pre ++ middle ++ post ++ conditionalX b₂ y) := by
    cases b₁ <;> cases b₂ <;>
      simp [conditionalX, measurementCount_append, measurementCount]
  have hleft := run_equiv_prefix hcount
    (fun m s => move_pair_parities pre middle post y b₁ b₂ hp hq m s) mask
  have hleft' := run_equiv_suffix hleft mask m s
  have hright := run_equiv_suffix (fun m s => conditionalX_cross mask y b₂ hm m s)
    (mask ++ conditionalX b₁ y ++ pre ++ middle ++ post) m s
  simp only [List.append_assoc] at hleft' hright ⊢
  exact hleft'.trans hright

theorem tight_run {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (address : Nat) (h : read (r₂ address) = !(read (r₁ address)))
    (hy : yLow L ∉ L.control :: (pairPorts L).flatMap ZeroBit.wires)
    (hm : yLow L ∉ wires ((pairXorT L (fin address) (xr address)).instantiate read))
    (m : List Bool) (s : ECDSAAdd.State) :
    run ((specialize (wPairEqual L t₁ t₂ fin xr r₁ r₂) address).instantiate read) m s =
      run ((specialize (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) address).instantiate read) m s := by
  rw [oldPair_inst read L t₁ t₂ fin xr r₁ r₂ address h, tight_inst]
  exact move_pair_with_mask _ _ _ _ (yLow L) _ _ hm
    (prefix_avoids _ _ _ hy) (suffix_avoids _ _ _ hy) m s


theorem port_none_avoids {n : Nat} (read : CBit n → Bool) (ports : List (LookupPort n))
    (address : Nat) (y : Wire) (hy : y ∉ portTargets ports) :
    y ∉ ECDSAAdd.wires ((portTemplate none ports address).instantiate read) := by
  induction ports with
  | nil => simp [portTemplate, Tmpl.instantiate, ECDSAAdd.wires]
  | cons p ports ih =>
    have h : y ≠ p.target ∧ y ∉ portTargets ports := by simpa [portTargets] using hy
    simp only [portTemplate_cons, Tmpl.instantiate_cons, TInstr.instantiate]
    by_cases hp : read (p.ref address) = p.value <;>
      simp [hp, ECDSAAdd.wires, Instr.wires, h.1, ih h.2]


theorem pair_chain_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂) :
    yLow L ∉ L.control :: (pairPorts L).flatMap ZeroBit.wires ∧ yLow L ∉ pairSrc L := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hp := zeroPorts_perm (pairSrc L) (L.dialogPool.take 257)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hc : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hp.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  have hc0 := (List.nodup_cons.mp hc).1
  have hc1 := (List.nodup_cons.mp (List.nodup_cons.mp hc).2).1
  have hnd1 := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  simp only [List.mem_cons, List.mem_append, not_or] at hc0 hc1 hnd1 ⊢
  exact ⟨⟨Ne.symm hc0.1, hc1.2.2⟩, hnd1.2.2.1⟩


theorem pairMask_avoids {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (address : Nat)
    (hy : yLow L ∉ pairSrc L) :
    yLow L ∉ ECDSAAdd.wires ((pairXorT L (fin address) (xr address)).instantiate read) := by
  rw [← specialize_pairXor L fin xr address]
  simp only [specialize, wPairXor, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize]
  apply port_none_avoids
  change yLow L ∉ L.point.finite :: portTargets (indexedPorts L.point.x xr true)
  rw [indexedPorts_targets]
  exact hy


theorem tight_pair_run {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) (address : Nat)
    (h : read (r₂ address) = !(read (r₁ address))) (m : List Bool) (s : ECDSAAdd.State) :
    run ((specialize (wPairEqual L t₁ t₂ fin xr r₁ r₂) address).instantiate read) m s =
      run ((specialize (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) address).instantiate read) m s := by
  have hy := pair_chain_avoids L hw hn t₁ t₂ ht1 ht2 h12
  exact tight_run read L t₁ t₂ fin xr r₁ r₂ address h hy.1
    (pairMask_avoids read L fin xr address hy.2) m s


theorem tight_pair_measurements {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (address : Nat) (h : read (r₂ address) = !(read (r₁ address))) :
    measurementCount ((specialize (wPairEqual L t₁ t₂ fin xr r₁ r₂) address).instantiate read) =
      measurementCount ((specialize (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) address).instantiate read) := by
  rw [oldPair_inst read L t₁ t₂ fin xr r₁ r₂ address h, tight_inst]
  cases read (r₁ address) <;> cases read (r₂ address) <;>
    simp [measurementCount_append, conditionalX, measurementCount, Nat.add_comm, Nat.add_left_comm]


theorem ytake_one (L : ControlledPointLayout) (hw : L.Widths) :
    L.point.y.take 1 = [yLow L] := by
  cases he : L.point.y with
  | nil =>
    have hh : L.point.y.length = 256 := hw.inputY
    rw [he] at hh
    simp at hh
  | cons w ws => simp [he, yLow]

theorem tight_geometry {n : Nat} (L : ControlledPointLayout) (hw : L.Widths)
    (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n)
    (r₁ r₂ : Nat → CBit n) (bits paths : List Wire) (root : Wire)
    (hshort : geometryOK bits paths root none (L.point.finite :: (L.point.x ++ L.point.y.take 1)) = true) :
    geometryCodeOK bits paths root (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) = true := by
  have htarget : geometryOK bits paths root none (L.point.finite :: (L.point.x ++ [yLow L])) = true := by
    simpa [ytake_one L hw] using hshort
  have ht (w : Wire) : geometryCodeOK bits paths root (wPairTailBare (n := n) (yLow L) t₁ t₂ w) = true := by
    simp [wPairTailBare, geometryCodeOK, lookupPlacedOK, wLiteral]
  have hz := geometry_zeroWith bits paths root _ ht L.control (pairPorts L)
  have hleaf (yr : Nat → CBit n) :
      geometryCodeOK bits paths root (wPairXorParity L fin xr yr) = true := by
    simp only [wPairXorParity, geometryCodeOK, List.all_cons, List.all_nil, Bool.and_true,
      lookupPlacedOK, portTargets, List.map_cons, List.map_append]
    rw [show List.map LookupPort.target (indexedPorts L.point.x xr true) = L.point.x from indexedPorts_targets _ _ _]
    exact htarget
  simp [wPairEqualTight, hleaf r₁, hleaf r₂, hz]


def ProgramEquivalent (p q : Program) : Prop :=
  measurementCount p = measurementCount q ∧ ∀ m s, run p m s = run q m s

theorem programEquivalent_refl (p : Program) : ProgramEquivalent p p := by
  exact ⟨rfl, fun _ _ => rfl⟩

theorem programEquivalent_append {p q p' q' : Program}
    (hp : ProgramEquivalent p p') (hq : ProgramEquivalent q q') :
    ProgramEquivalent (p ++ q) (p' ++ q') := by
  constructor
  · simp only [measurementCount_append, hp.1, hq.1]
  · intro m s
    simp only [ECDSAAdd.run_append, hp.1, hp.2, hq.2]

def CodeEquivalent {n : Nat} (read : CBit n → Bool) (address : Nat) (p q : WCode n) : Prop :=
  ProgramEquivalent ((specialize p address).instantiate read) ((specialize q address).instantiate read)

theorem codeEquivalent_refl {n : Nat} (read : CBit n → Bool) (address : Nat) (p : WCode n) :
    CodeEquivalent read address p p := programEquivalent_refl _

theorem codeEquivalent_append {n : Nat} (read : CBit n → Bool) (address : Nat)
    {p q p' q' : WCode n} (hp : CodeEquivalent read address p p')
    (hq : CodeEquivalent read address q q') : CodeEquivalent read address (p ++ q) (p' ++ q') := by
  simp only [CodeEquivalent, specialize_append, Tmpl.instantiate_append] at hp hq ⊢
  exact programEquivalent_append hp hq

def wFiniteTight {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairEqualTight L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortNegEqual L L.core.equalX L.core.equalNegY rows ++
  wLiteral (pointDialogGenericFlag L) ++ wGeneric L rows ++ wCornersOne L rows ++
  wLiteral (pointDialogGenericFlag L) ++
  wPairEqualTight L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortEqual L L.core.double L.doubleSelect (wBit rows .doubleInfinity)
    (wFields rows .doubleX) (wBit rows .doubleY) ++
  wLiteral (zeroFlag L.point.finite L.control L.genericSelect) ++
  wLiteral ([.CX L.control L.core.equalX]) ++ wLiteral ([.CX L.control L.core.double]) ++
  wLiteral (Arith.padding (L.core.poolWire 0) 51716)


attribute [local irreducible] wGeneric wCornersOne wPairEqual wPairEqualTight wShortNegEqual
  wShortEqual wLiteral pointDialogGenericFlag zeroFlag

theorem tight_pair_literal_counts {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) :
    literalToffolis (wPairEqualOpposite L t₁ t₂ fin xr r₁ r₂) =
      literalToffolis (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) ∧
    literalRecords (wPairEqualOpposite L t₁ t₂ fin xr r₁ r₂) =
      literalRecords (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) := by
  have hz (c : Wire) (bs : List ZeroBit) :
      literalToffolis (wZeroWith (wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂) c bs) =
        literalToffolis (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂) c bs) ∧
      literalRecords (wZeroWith (wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂) c bs) =
        literalRecords (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂) c bs) := by
    induction bs generalizing c with
    | nil => simp [wZeroWith, wPairTailOpposite, wPairTailBare, wLiteral, literalToffolis, literalRecords]
    | cons b bs ih => simp [wZeroWith, literalToffolis_append, literalRecords_append, ih]
  have h := hz L.control (pairPorts L)
  simpa [wPairEqualOpposite, wPairEqualTight, wPairXor, wPairXorParity, literalToffolis_append,
    literalRecords_append, literalToffolis, literalRecords] using h

theorem tight_finite_literal_counts {n : Nat} (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) :
    literalToffolis (wFiniteTight L rows) = 2156628 ∧ literalRecords (wFiniteTight L rows) = 1556899 := by
  have h₁ := tight_pair_literal_counts L L.doubleSelect L.genericSelect (wBit rows .infinity)
    (wFields rows .x) (wBit rows .y) (wBit rows .negY)
  have h₂ := tight_pair_literal_counts L L.infinitySelect L.core.equalNegY (wBit rows .infinity)
    (wFields rows .x) (wBit rows .y) (wBit rows .negY)
  have h : literalToffolis (wFiniteOne L rows) = literalToffolis (wFiniteTight L rows) ∧
      literalRecords (wFiniteOne L rows) = literalRecords (wFiniteTight L rows) := by
    constructor
    · simp only [wFiniteOne, wFiniteTight, literalToffolis_append, h₁.1, h₂.1]
    · simp only [wFiniteOne, wFiniteTight, literalRecords_append, h₁.2, h₂.2]
  have old := finiteOne_literal_counts L hw hn rows
  exact ⟨h.1.symm.trans old.1, h.2.symm.trans old.2⟩

theorem tight_finite_geometry {n : Nat} (L : ControlledPointLayout) (hw : L.Widths)
    (rows : Nat → Fin n) (bits paths : List Wire) (root : Wire)
    (hshort : geometryOK bits paths root none (L.point.finite :: (L.point.x ++ L.point.y.take 1)) = true)
    (hp : ∀ c ∈ [L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.equalNegY],
      geometryOK bits paths root (some c) (L.point.finite :: (L.point.x ++ L.point.y)) = true)
    (hc : ∀ r, geometryOK bits paths root (some L.core.generic) (L.recoveryConstant r).src = true) :
    geometryCodeOK bits paths root (wFiniteTight L rows) = true := by
  have heq (t₁ t₂ : Wire) (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) :
      geometryCodeOK bits paths root (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) = true :=
    tight_geometry L hw t₁ t₂ fin xr r₁ r₂ bits paths root hshort
  simp [wFiniteTight, wShortNegEqual, wGeneric, wRecovery, wCornersOne, wConstAdd,
    wShortEqual, List.cons_append, hshort, heq,
    hp L.doubleSelect (by simp),
    hp L.core.equalNegY (by simp), hc]

theorem zeroWith_literal_transfer {n : Nat} (t u : Wire → WCode n)
    (ht : ∀ w p, WInstr.literal p ∈ t w → WInstr.literal p ∈ u w)
    (c : Wire) (bs : List ZeroBit) (p : Program)
    (hp : WInstr.literal p ∈ wZeroWith t c bs) : WInstr.literal p ∈ wZeroWith u c bs := by
  induction bs generalizing c with
  | nil => exact ht c p hp
  | cons b bs ih =>
    simp only [wZeroWith, List.mem_append] at hp ⊢
    rcases hp with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (ih b.work h))
    · exact Or.inr h

theorem tight_pair_literal_transfer {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) (p : Program)
    (hp : WInstr.literal p ∈ wPairEqualTight L t₁ t₂ fin xr r₁ r₂) :
    WInstr.literal p ∈ wPairEqualOpposite L t₁ t₂ fin xr r₁ r₂ := by
  have ht (w : Wire) (p : Program)
      (h : WInstr.literal p ∈ wPairTailBare (n := n) (yLow L) t₁ t₂ w) :
      WInstr.literal p ∈ wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂ w := by
    simp [wPairTailBare, wPairTailOpposite, wLiteral] at h ⊢
    exact h
  have hmid : WInstr.literal p ∈ wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂) L.control (pairPorts L) := by
    simpa [wPairEqualTight, wPairXorParity] using hp
  have hmid' := zeroWith_literal_transfer _ _ ht L.control (pairPorts L) p hmid
  simpa [wPairEqualOpposite, wPairXor] using hmid'

def LiteralSubset {n : Nat} (p q : WCode n) : Prop :=
  ∀ i, WInstr.literal i ∈ p → WInstr.literal i ∈ q

theorem literalSubset_refl {n : Nat} (p : WCode n) : LiteralSubset p p := fun _ h => h

theorem literalSubset_append {n : Nat} {p q p' q' : WCode n}
    (hp : LiteralSubset p p') (hq : LiteralSubset q q') : LiteralSubset (p ++ q) (p' ++ q') := by
  intro i hi
  simp only [List.mem_append] at hi ⊢
  rcases hi with h | h
  · exact Or.inl (hp i h)
  · exact Or.inr (hq i h)

theorem tight_finite_literal_subset {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    LiteralSubset (wFiniteTight L rows) (wFiniteOne L rows) := by
  have hp1 : LiteralSubset
      (wPairEqualTight L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY))
      (wPairEqualOpposite L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY)) := tight_pair_literal_transfer _ _ _ _ _ _ _
  have hp2 : LiteralSubset
      (wPairEqualTight L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY))
      (wPairEqualOpposite L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY)) := tight_pair_literal_transfer _ _ _ _ _ _ _
  unfold wFiniteTight wFiniteOne
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ hp2
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ (literalSubset_refl _)
  refine literalSubset_append ?_ hp1
  exact literalSubset_refl _

theorem tight_against_twentyEight {n : Nat} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) (address : Nat)
    (h : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)))
    (hf1 : L.doubleSelect ∈ L.inPlaceFlags) (hf2 : L.genericSelect ∈ L.inPlaceFlags)
    (hf3 : L.infinitySelect ∈ L.inPlaceFlags) (hf4 : L.core.equalNegY ∈ L.inPlaceFlags)
    (hd : L.doubleSelect ≠ L.genericSelect) (hi : L.infinitySelect ≠ L.core.equalNegY) :
    CodeEquivalent read address (wFiniteOne L rows) (wFiniteTight L rows) := by
  have eqpair (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags)
      (hne : t₁ ≠ t₂) : CodeEquivalent read address
      (wPairEqualOpposite L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY))
      (wPairEqualTight L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY)) := by
    constructor
    · rw [oppositeEqual_inst read L t₁ t₂ _ _ _ _ address h, ← specialize_pairEqual]
      exact tight_pair_measurements read L t₁ t₂ _ _ _ _ address h
    · intro m s
      rw [oppositeEqual_inst read L t₁ t₂ _ _ _ _ address h, ← specialize_pairEqual]
      exact tight_pair_run read L hw hn t₁ t₂ ht1 ht2 hne _ _ _ _ address h m s
  have hp1 := eqpair L.doubleSelect L.genericSelect hf1 hf2 hd
  have hp2 := eqpair L.infinitySelect L.core.equalNegY hf3 hf4 hi
  unfold wFiniteOne wFiniteTight
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ hp2
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ hp1
  exact codeEquivalent_refl _ _ _



theorem tight_stream_equiv {n : Nat} (read : CBit n → Bool) (rows : Nat → Fin n) (address : Nat)
    (h : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address))) :
    CodeEquivalent read address (wFiniteOne streamLayout rows) (wFiniteTight streamLayout rows) := by
  apply tight_against_twentyEight read streamLayout streamLayout_widths streamLayout_nodup rows address h
  all_goals decide +kernel


open ECDSAAdd.Secp256k1

theorem tight_stream_program_equiv {n : Nat} (read : CBit n → Bool) (rows : Nat → Fin n) (address : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h : RowReads read (rows address) (.some hc)) (h₁ : cy ≠ -cy)
    (h₂ : exceptionBit (.some hc) = true) (hD : (.some hc : Point) + .some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0) :
    ProgramEquivalent ((specialize (wFiniteTight streamLayout rows) address).instantiate read)
      (finiteOneS streamLayout (.some hc) cx cy) := by
  have yC : read (bitRef (rows address) .y 0) = yBit (.some hc) := by
    rw [h.bit _ 0 (by decide), field_y, yBit_eq]
  have yN : read (bitRef (rows address) .negY 0) = yBit (-(.some hc : Point)) := by
    rw [h.bit _ 0 (by decide), ECDSAAdd.ShorPort.field_negY, yBit_eq]
  have hy0 : cy ≠ 0 := by
    intro hy
    apply h₁
    simp [hy]
  have hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)) := by
    change read (bitRef (rows address) .negY 0) = !(read (bitRef (rows address) .y 0))
    rw [yN, yC, yBit_eq, yBit_eq, pointY_neg]
    exact neg_y_low_bit cy hy0
  have he := tight_stream_equiv read rows address hop
  unfold CodeEquivalent at he
  unfold ProgramEquivalent at he ⊢
  rw [wFiniteOne_inst read streamLayout streamLayout_widths rows address hc h h₁ h₂ hD hDo] at he
  exact ⟨he.1.symm, fun m s => (he.2 m s).symm⟩


theorem wrapper_record_ledger {n : Nat} (bits paths : List Wire) (root : Wire)
    (p q : Program) (code : WCode n) (m k : Nat)
    (hr : literalRecords code = m) (ht : traversals code = k)
    (hl : LookupLayouts bits paths root (normalizeW (wLiteral p ++ code ++ wLiteral q))) :
    codeRecords bits paths root (normalizeW (wLiteral p ++ code ++ wLiteral q)) =
      measurementCount p + m + measurementCount q + k * (2 ^ bits.length - 1) := by
  rw [codeRecords_eq _ _ _ _ hl, literalRecords_normalize, traversals_normalize]
  simp only [literalRecords_append, wLiteral, literalRecords, Nat.add_zero, traversals_append,
    traversals, Nat.zero_add, hr, ht]


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem windowOne_geometry (rows : Nat → Fin 32768) :
    geometryCodeOK windowBits windowPaths windowRoot (wFiniteTight streamLayout rows) = true := by
  have hs : geometryOK windowBits windowPaths windowRoot none
      (streamLayout.point.finite :: (streamLayout.point.x ++ streamLayout.point.y.take 1)) = true := by decide +kernel
  have hpoint : ∀ c ∈ [streamLayout.infinitySelect,streamLayout.doubleSelect,
      streamLayout.genericSelect,streamLayout.core.equalNegY],
      geometryOK windowBits windowPaths windowRoot (some c)
        (streamLayout.point.finite :: (streamLayout.point.x ++ streamLayout.point.y)) = true := by decide +kernel
  have hconst (r : List Wire) : geometryOK windowBits windowPaths windowRoot (some streamLayout.core.generic)
      (streamLayout.recoveryConstant r).src = true := by
    change geometryOK windowBits windowPaths windowRoot (some streamLayout.core.generic)
      (streamLayout.dialogPool.take 256) = true
    decide +kernel
  exact tight_finite_geometry streamLayout streamLayout_widths rows windowBits windowPaths windowRoot hs hpoint hconst

theorem used_point_control_work (L : ControlledPointLayout) (w : Wire) (hw : w ∈ L.dialogUsedWires) :
    w ∈ PointAddLayout.pointWires L.point ∨ w = L.control ∨ w ∈ L.work := by
  simp only [dialogUsedWires, List.mem_append, List.mem_singleton] at hw
  rcases hw with ((hw | hw) | hw) | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (one_boundary_work_subset L (List.mem_append_left _ hw)))
  · exact Or.inr (Or.inr (one_boundary_work_subset L (List.mem_append_right _ hw)))

theorem window_reserved_gap (w : Wire) (hw : w ∈ windowRoot :: windowBits ++ windowPaths) :
    855 ≤ w ∧ w < 10514 := by
  simp only [windowRoot, windowBits, windowPaths, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem window_reserved_outside_used (w : Wire) (hw : w ∈ windowRoot :: windowBits ++ windowPaths) :
    w ∉ streamLayout.dialogUsedWires := by
  intro hu
  have hg := window_reserved_gap w hw
  rcases used_point_control_work streamLayout w hu with hp | hq | hp
  · have hl := point_wire_small w ((native_point_mem w).mp hp)
    have hb : w < 839 := by
      rw [streamLayout_point] at hp
      simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append, List.mem_range'_1] at hp
      dsimp only [Wire] at *
      omega
    dsimp only [Wire] at *
    omega
  · rw [streamLayout_control] at hq
    dsimp only [Wire] at *
    omega
  · have hl := streamWork_lower w hp
    dsimp only [Wire] at *
    omega

theorem windowOne_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ wFiniteTight streamLayout rows, Placed windowBits windowPaths windowRoot i := by
  intro i hi
  cases i with
  | literal p =>
    intro w hw hp
    exact window_reserved_outside_used w hw (List.mem_toFinset.mp
      ((finiteOne_literal_facts streamLayout streamLayout_widths streamLayout_nodup rows p
        (tight_finite_literal_subset streamLayout rows p hi)).1 hp))
  | lookup c ports =>
    exact (lookupPlacedOK_iff _ _ _ _).mp
      (List.all_eq_true.mp (windowOne_geometry rows) _ hi)

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem indexedPorts_length23 {n : Nat} (ws : List Wire)
    (refs : Nat → Nat → ConstantBit n) (v : Bool) : (indexedPorts ws refs v).length = ws.length := by
  have h := congrArg List.length (indexedPorts_targets ws refs v)
  simpa [portTargets] using h

theorem pairPortMask_append {n : Nat} (read : ConstantBit n → Bool)
    (left right : List (LookupPort n)) (address : Nat) :
    portMask read (left ++ right) address =
      portMask read left address ++ portMask read right address := by
  induction left with
  | nil => simp [portMask, portTargets, tableBitsMask]
  | cons p ps ih =>
    by_cases h : read (p.ref address) = p.value <;>
      simp [portMask, portTargets, tableBitsMask, h] at ih ⊢ <;> simp [ih]

/-- Two nodup port chunks may overlap while sharing one coherent traversal. -/
theorem pairPort_coherent {n : Nat} (read : ConstantBit n → Bool)
    (left right : List (LookupPort n)) (bits paths : List Wire) (root start : Nat)
    (history : Fin start → Bool) (hl : bits.length ≤ paths.length)
    (hn : (root :: bits ++ paths).Nodup)
    (ha : (portTargets left).Nodup) (hb : (portTargets right).Nodup)
    (hda : (root :: bits ++ paths).Disjoint (portTargets left))
    (hdb : (root :: bits ++ paths).Disjoint (portTargets right)) :
    CoherentlyImplementsOn
      ((lookupProgram n (portOps (left ++ right) bits paths root) start).instantiate read history)
      (Quantum.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (portMask read left l) ++
          tableXorGates q (portMask read right l))
        (tableAddressTree bits 0 1) root paths)) (Clean paths) := by
  have hbits : bits.Nodup := (List.nodup_cons.mp hn).2.of_append_left
  have h := endpointXorPair_coherent (portMask read left) (portMask read right)
    (tableAddressTree bits 0 1) root paths (tableAddressTree_layout _ _ _ _ _ hl hn)
    (fun l => tableBitsMask_nodup _ _ ha) (fun l => tableBitsMask_nodup _ _ hb)
    (by intro l w hw hm
        rw [tableAddressTree_index _ _ _ hbits] at hw
        exact List.disjoint_left.mp hda hw (tableBitsMask_subset _ _ hm))
    (by intro l w hw hm
        rw [tableAddressTree_index _ _ _ hbits] at hw
        exact List.disjoint_left.mp hdb hw (tableBitsMask_subset _ _ hm))
  unfold CoherentlyImplementsOn at h ⊢
  rw [portProgram_run]
  simpa [tableLookupProgram, tableLookup, pairPortMask_append, tableXorGates, List.map_append]
    using h

/-- Its ideal action is exactly two sequential field masks on the selected address. -/
theorem pairPort_coherent_state {n : Nat} (read : ConstantBit n → Bool)
    (left right : List (LookupPort n)) (bits paths : List Wire) (root start : Nat)
    (history : Fin start → Bool) (hl : bits.length ≤ paths.length)
    (hn : (root :: bits ++ paths).Nodup)
    (ha : (portTargets left).Nodup) (hb : (portTargets right).Nodup)
    (hda : (root :: bits ++ paths).Disjoint (portTargets left))
    (hdb : (root :: bits ++ paths).Disjoint (portTargets right)) :
    CoherentlyImplementsOn
      ((lookupProgram n (portOps (left ++ right) bits paths root) start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        tableXorState (portMask read right (tableAddressValue bits s)) (s root)
          (tableXorState (portMask read left (tableAddressValue bits s)) (s root) s)))
      (Clean paths) := by
  have hbits : bits.Nodup := (List.nodup_cons.mp hn).2.of_append_left
  apply (pairPort_coherent read left right bits paths root start history hl hn ha hb hda hdb).congrIdeal
  intro s hs
  rw [run_ket_agrees_classical _ _ (unaryActionUnitary_HPFree _ _ _ _ _
    (by intro l q; rw [Classical.hpFree_append]; exact ⟨tableXorGates_HPFree _ _, tableXorGates_HPFree _ _⟩)),
    endpointXorPair_run (portMask read left) (portMask read right)
      (tableAddressTree bits 0 1) root paths (tableAddressTree_layout _ _ _ _ _ hl hn)
      (fun l => tableBitsMask_nodup _ _ ha) (fun l => tableBitsMask_nodup _ _ hb)
      (by intro l w hw hm; rw [tableAddressTree_index _ _ _ hbits] at hw
          exact List.disjoint_left.mp hda hw (tableBitsMask_subset _ _ hm))
      (by intro l w hw hm; rw [tableAddressTree_index _ _ _ hbits] at hw
          exact List.disjoint_left.mp hdb hw (tableBitsMask_subset _ _ hm)) s hs]
  simp [tableAddressTree_route, ket]

/-- The same specialization result supports an optional outer control. -/
theorem pairPort_specialize_run_control {n : Nat} (read : ConstantBit n → Bool)
    (control : Option Wire) (left right : List (LookupPort n)) (address root : Nat)
    (m : List Bool) (st : ECDSAAdd.State) (ha : (portTargets left).Nodup)
    (hb : (portTargets right).Nodup) (hqa : lookupRoot root control ∉ portTargets left)
    (hqb : lookupRoot root control ∉ portTargets right) (hra : root ∉ portTargets left)
    (hv : st.basis root = true) :
    ECDSAAdd.run ((portTemplate control (left ++ right) address).instantiate read) m st =
      ⟨st.phase, tableXorState (portMask read right address) (st.basis (lookupRoot root control))
        (tableXorState (portMask read left address) (st.basis (lookupRoot root control)) st.basis)⟩ := by
  rw [portTemplate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.run_append,
    (portTemplate_counts read control left address).2]
  simp only [List.take_zero, List.drop_zero]
  rw [portTemplate_run read control left address root ([] : List Bool) st ha hqa hv]
  have hmaskRoot : root ∉ portMask read left address := by
    intro h; exact hra (tableBitsMask_subset _ _ h)
  have hmaskControl : lookupRoot root control ∉ portMask read left address := by
    intro h; exact hqa (tableBitsMask_subset _ _ h)
  have hroot : tableXorState (portMask read left address) (st.basis (lookupRoot root control))
      st.basis root = true := by
    rw [tableXorState_outside _ _ _ _ hmaskRoot, hv]
  have hcontrol : tableXorState (portMask read left address) (st.basis (lookupRoot root control))
      st.basis (lookupRoot root control) = st.basis (lookupRoot root control) := by
    exact tableXorState_outside _ _ _ _ hmaskControl
  rw [portTemplate_run read control right address root m _ hb hqb hroot]
  simp only [hcontrol]

/-- Placement allowing two independently distinct target chunks. -/
def PlacedPair {n : Nat} (bits paths : List Wire) (root : Wire) : WInstr n → Prop
  | .literal p => ∀ w ∈ root :: bits ++ paths, w ∉ ECDSAAdd.wires p
  | .lookup ctl ports =>
      (lookupRoot root ctl :: bits ++ paths).Nodup ∧
      (portTargets (ports.take 258)).Nodup ∧
      (portTargets (ports.drop 258)).Nodup ∧
      (root :: lookupRoot root ctl :: bits ++ paths).Disjoint (portTargets ports)

theorem placed_implies_pair {n : Nat} (bits paths : List Wire) (root : Wire)
    (i : WInstr n) (h : Placed bits paths root i) : PlacedPair bits paths root i := by
  cases i with
  | literal p => simpa only [PlacedPair, Placed] using h
  | lookup c ports =>
    dsimp only [PlacedPair, Placed] at h ⊢
    refine ⟨h.1, ?_, ?_, h.2.2⟩
    · simpa [portTargets, List.map_take] using h.2.1.take
    · simpa [portTargets, List.map_drop] using h.2.1.drop

/-- Both mask chunks preserve the lookup address, root and clean path bank. -/
theorem pair_lookup_preserves_simulation {n : Nat} (read : ConstantBit n → Bool)
    (control : Option Wire) (ports : List (LookupPort n)) (bits paths : List Wire)
    (root address : Nat) (hp : PlacedPair bits paths root (.lookup control ports))
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths root address st) :
    SimulationValid bits paths root address
      ⟨st.phase, tableXorState (portMask read (ports.drop 258) address)
        (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address)
          (st.basis (lookupRoot root control)) st.basis)⟩ := by
  dsimp only [PlacedPair] at hp
  have frame (w : Wire) (hw : w ∈ root :: bits ++ paths) :
      tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis) w =
        st.basis w := by
    have hd (v : Wire) (h : v ∈ portTargets ports) : v ≠ w := by
      intro e; subst v
      exact List.disjoint_left.mp hp.2.2.2 (by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem root (List.mem_cons_of_mem _ hw)) h
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
  dsimp only [SimulationValid]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw; rw [frame w (by simp [hw])]; exact hs.1 w hw
  · rw [tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.2.1
  · rw [frame root (by simp)]; exact hs.2.2

/-- Source-level form of the two-chunk coherent lookup. -/
theorem pairPort_source_state {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (LookupPort n)) (bits paths : List Wire) (q : Wire)
    (hl : bits.length ≤ paths.length) (hn : (q :: bits ++ paths).Nodup)
    (ha : (portTargets (ports.take 258)).Nodup)
    (hb : (portTargets (ports.drop 258)).Nodup)
    (hsep : (q :: bits ++ paths).Disjoint (portTargets ports)) :
    CoherentlyImplementsOn (tableLookupProgram (portMask read ports) bits q paths)
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        tableXorState (portMask read (ports.drop 258) (tableAddressValue bits s)) (s q)
          (tableXorState (portMask read (ports.take 258) (tableAddressValue bits s)) (s q) s)))
      (Clean paths) := by
  have hda : (q :: bits ++ paths).Disjoint (portTargets (ports.take 258)) := by
    apply List.disjoint_left.mpr
    intro w hw hm
    apply List.disjoint_left.mp hsep hw
    rw [portTargets, List.map_take] at hm
    exact List.take_subset _ _ hm
  have hdb : (q :: bits ++ paths).Disjoint (portTargets (ports.drop 258)) := by
    apply List.disjoint_left.mpr
    intro w hw hm
    apply List.disjoint_left.mp hsep hw
    rw [portTargets, List.map_drop] at hm
    exact List.drop_subset _ _ hm
  let history : Fin 0 → Bool := Fin.elim0
  have h := pairPort_coherent_state read (ports.take 258) (ports.drop 258) bits paths q 0
    history hl hn ha hb hda hdb
  unfold CoherentlyImplementsOn at h ⊢
  rw [portProgram_run, List.take_append_drop] at h
  exact h

theorem pair_source_simulation {n : Nat} (read : ConstantBit n → Bool)
    (bits paths : List Wire) (root : Wire) (hl : bits.length ≤ paths.length) (code : WCode n)
    (hp : ∀ i ∈ code, PlacedPair bits paths root i) :
    ∃ cs : List ℂ, List.Forall₂ (SimulationBranch read code bits paths root)
      (source read bits paths root code).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    refine ⟨[], rfl, ?_⟩
    intro address st hs
    simp [specialize,
      ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]
  | cons i code ih =>
    have htail := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    obtain ⟨tailCs, tailAligned, tailMass⟩ := htail
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      have hip : Placed bits paths root (.literal p : WInstr n) := by
        simpa only [Placed, PlacedPair] using hi
      obtain ⟨cs, aligned, mass⟩ := literal_simulation p
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨b₁.history ++ m₂, ?_, ?_⟩
        · simp [literalRecords, List.length_append, h₁.1, hm₂]
        · intro address st hs
          change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
          rw [h₁.2 st, map_smul,
            h₂ address (ECDSAAdd.run p b₁.history st)
              (literal_preserves_simulation (n := n) p bits paths root address hip st hs b₁.history)]
          simp only [specialize, List.flatMap_cons, WInstr.specialize,
            ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
          rw [run_append_records _ _ _ _ _ h₁.1]
          simp [smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num
    | lookup control ports =>
      dsimp only [PlacedPair] at hi
      have hsep : (lookupRoot root control :: bits ++ paths).Disjoint (portTargets ports) := by
        apply List.disjoint_left.mpr
        intro w hw hm
        exact List.disjoint_left.mp hi.2.2.2 (List.mem_cons_of_mem root hw) hm
      have hlookup := pairPort_source_state read ports bits paths (lookupRoot root control)
        hl hi.1 hi.2.1 hi.2.2.1 hsep
      obtain ⟨cs, aligned, mass⟩ := hlookup
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨m₂, hm₂, ?_⟩
        intro address st hs
        let next : ECDSAAdd.State := ⟨st.phase,
          tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
            (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis)⟩
        have step : b₁.kraus (Bridge.signedKet st) = c₁ • Bridge.signedKet next := by
          have hstep : b₁.kraus (ket st.basis) = c₁ • ket next.basis := by
            simpa [ket, next, hs.2.1] using h₁ st.basis hs.1
          simp only [Bridge.signedKet, map_smul, hstep]
          simp [next, smul_smul, mul_comm]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [step, map_smul, h₂ address next
          (pair_lookup_preserves_simulation read control ports bits paths root address hi st hs)]
        have hqa : lookupRoot root control ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hqb : lookupRoot root control ∉ portTargets (ports.drop 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_drop] at hm
          exact List.drop_subset _ _ hm
        have hra : root ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hi.2.2.2 (show root ∈ root :: lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hspec := pairPort_specialize_run_control read control (ports.take 258) (ports.drop 258)
          address root ([] : List Bool) st hi.2.1 hi.2.2.1 hqa hqb hra hs.2.2
        rw [List.take_append_drop] at hspec
        simp only [specialize, List.flatMap_cons, WInstr.specialize,
          ECDSAAdd.ShorPort.Tmpl.instantiate_append]
        rw [ECDSAAdd.run_append, (portTemplate_counts read control ports address).2,
          List.take_zero, List.drop_zero, hspec]
        simp [next, smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num

theorem pair_compile_specialization_coherent {n : Nat} (read : ConstantBit n → Bool)
    (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : bits.length ≤ paths.length) (hp : ∀ i ∈ code, PlacedPair bits paths root i)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run ((specialize code (tableAddressValue bits s)).instantiate read) m ⟨false, s⟩ =
        ⟨false, result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((compile bits paths root code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean paths s ∧ s root = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := pair_source_simulation read bits paths root hl code hp
  refine ⟨cs, ?_, mass⟩
  rw [compile_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have hresult := h (tableAddressValue bits s) ⟨false, s⟩ ⟨hs.1, rfl, hs.2.1⟩
  rw [Bridge.signedKet_false, hrun s hs.2.2 m, Bridge.signedKet_false] at hresult
  simpa [ket] using hresult

theorem pair_placed_normalize {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hp : ∀ i ∈ code, PlacedPair bits paths root i) :
    ∀ i ∈ normalizeW code, PlacedPair bits paths root i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j with
  | literal p => simpa [normalizeWInstr, PlacedPair, ECDSAAdd.Baselines.normalize_wires] using h
  | lookup c p => exact h

theorem pair_layouts_of_placed {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : bits.length ≤ paths.length) (hp : ∀ i ∈ code, PlacedPair bits paths root i) :
    LookupLayouts bits paths root code := by
  refine ⟨hl, ?_⟩
  intro c p hm
  have hi := hp (.lookup c p) hm
  dsimp only [PlacedPair] at hi
  exact hi.1

theorem pair_compile_wellFormed {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : bits.length ≤ paths.length) (hp : ∀ i ∈ code, PlacedPair bits paths root i)
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
      dsimp only [PlacedPair] at hi
      simp only [compile, NaiveChallenge.wellFormed_castFinish]
      apply straight_append_wellFormed
      · apply portProgram_wellFormed _ _ _ _ _ hl hi.1
        exact List.disjoint_left.mpr (fun w hw hm =>
          List.disjoint_left.mp hi.2.2.2 (List.mem_cons_of_mem root hw) hm)
      · exact ht _

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.ControlledPointLayout

def pairParityPorts {n : Nat} (L : ControlledPointLayout) (fin : Nat → ConstantBit n)
    (xr : Nat → Nat → ConstantBit n) (yr : Nat → ConstantBit n) : List (LookupPort n) :=
  ⟨fin, false, L.point.finite⟩ :: indexedPorts L.point.x xr true ++ [⟨yr, false, yLow L⟩]

def wPairShortFused {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (r₁ r₂ : Nat → ConstantBit n) (short : List (LookupPort n)) (z : Program) : WCode n :=
  wPairXorParity L fin xr r₁ ++ wZeroWith (wPairTailBare (yLow L) t₁ t₂)
    L.control (pairPorts L) ++ [.lookup none (pairParityPorts L fin xr r₂ ++ short)] ++
    wLiteral z ++ [.lookup none short]

/-- Fusing the adjacent leaves preserves their complete specialized program. -/
theorem specialize_pairShortFused {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n)
    (r₁ r₂ : Nat → ConstantBit n) (short : List (LookupPort n)) (z : Program) (address : Nat) :
    specialize (wPairShortFused L t₁ t₂ fin xr r₁ r₂ short z) address =
      specialize (wPairEqualTight L t₁ t₂ fin xr r₁ r₂ ++ [.lookup none short] ++
        wLiteral z ++ [.lookup none short]) address := by
  simp [wPairShortFused, wPairEqualTight, wPairXorParity, pairParityPorts,
    specialize, WInstr.specialize, portTemplate_append, List.append_assoc]

def shortNegPorts {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : List (LookupPort n) :=
  ⟨wBit rows .doubleInfinity, false, L.point.finite⟩ ::
    indexedPorts L.point.x (wFields rows .doubleX) true ++
    indexedPorts (L.point.y.take 1) (fun a _ => wBit rows .doubleY 0 a) false

theorem shortNegEqual_expanded {n : Nat} (L : ControlledPointLayout) (c t : Wire)
    (rows : Nat → Fin n) :
    wShortNegEqual L c t rows = [.lookup none (shortNegPorts L rows)] ++
      wLiteral (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
      [.lookup none (shortNegPorts L rows)] := by
  rfl

def wFinite23 {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairShortFused L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
    (zeroControlled L.core.equalX L.core.equalNegY (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
  wLiteral (pointDialogGenericFlag L) ++ wGeneric L rows ++ wCornersOne L rows ++
  wLiteral (pointDialogGenericFlag L) ++
  wPairEqualTight L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortEqual L L.core.double L.doubleSelect (wBit rows .doubleInfinity)
    (wFields rows .doubleX) (wBit rows .doubleY) ++
  wLiteral (zeroFlag L.point.finite L.control L.genericSelect) ++
  wLiteral ([.CX L.control L.core.equalX]) ++ wLiteral ([.CX L.control L.core.double]) ++
  wLiteral (Arith.padding (L.core.poolWire 0) 51716)

theorem specialize_finite23 {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n)
    (address : Nat) : specialize (wFinite23 L rows) address =
      specialize (wFiniteTight L rows) address := by
  rw [wFinite23, wFiniteTight, shortNegEqual_expanded]
  simp only [specialize_append, specialize_pairShortFused, List.append_assoc]

theorem traversals_pairShortFused {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → ConstantBit n) (xr : Nat → Nat → ConstantBit n) (r₁ r₂ : Nat → ConstantBit n)
    (short : List (LookupPort n)) (z : Program) :
    traversals (wPairShortFused L t₁ t₂ fin xr r₁ r₂ short z) = 3 := by
  have hz : traversals (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂)
      L.control (pairPorts L)) = 0 :=
    traversals_zeroWith _ 0 (fun _ => rfl) _ _
  simp [wPairShortFused, wPairXorParity, wLiteral, traversals_append, traversals, hz]

theorem traversals_finite23 {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    traversals (wFinite23 L rows) = 21 := by
  simp [wFinite23, traversals_pairShortFused, tight_traversals, traversals_shortEqual,
    traversals_generic, traversals_cornersOne, traversals, wLiteral, traversals_append]

/-- Adjacent distinct-target leaves may overlap after they are combined. -/
theorem fused_leaf_placed {n : Nat} (bits paths : List Wire) (root : Wire)
    (left right : List (LookupPort n)) (hlen : left.length = 258)
    (ha : Placed bits paths root (.lookup none left))
    (hb : Placed bits paths root (.lookup none right)) :
    PlacedPair bits paths root (.lookup none (left ++ right)) := by
  have ht : (left ++ right).take 258 = left := by simp [hlen]
  have hd : (left ++ right).drop 258 = right := by simp [hlen]
  dsimp only [Placed, PlacedPair] at ha hb ⊢
  refine ⟨ha.1, ?_, ?_, ?_⟩
  · rw [ht]; exact ha.2.1
  · rw [hd]; exact hb.2.1
  · apply List.disjoint_left.mpr
    intro w hw hm
    have hh : w ∈ portTargets left ∨ w ∈ portTargets right := by
      simpa [portTargets] using hm
    rcases hh with h | h
    · exact List.disjoint_left.mp ha.2.2 hw h
    · exact List.disjoint_left.mp hb.2.2 hw h

/-- All old instructions are retained except for the merged leaf. -/
theorem finite23_member {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n)
    (i : WInstr n) (hi : i ∈ wFinite23 L rows) :
    i ∈ wFiniteTight L rows ∨
      i = .lookup none (pairParityPorts L (wBit rows .infinity) (wFields rows .x)
        (wBit rows .negY) ++ shortNegPorts L rows) := by
  simp only [wFinite23, wFiniteTight, wPairShortFused, wPairEqualTight,
    wShortNegEqual, wShortNegXor, wPairXorParity, shortNegPorts, pairParityPorts,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  aesop

theorem finite23_literal_subset {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n)
    (p : Program) (hp : WInstr.literal p ∈ wFinite23 L rows) :
    WInstr.literal p ∈ wFiniteTight L rows := by
  rcases finite23_member L rows (.literal p) hp with old | fused
  · exact old
  · cases fused

/-- The concrete 23-traversal row satisfies the relaxed geometry. -/
theorem window23_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ wFinite23 streamLayout rows, PlacedPair windowBits windowPaths windowRoot i := by
  let left := pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .negY)
  let right := shortNegPorts streamLayout rows
  have leftMem : WInstr.lookup none left ∈ wFiniteTight streamLayout rows := by
    simp only [left, pairParityPorts, wFiniteTight, wPairEqualTight, wPairXorParity,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have rightMem : WInstr.lookup none right ∈ wFiniteTight streamLayout rows := by
    simp only [right, shortNegPorts, wFiniteTight, wShortNegEqual, wShortNegXor,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have hlen : left.length = 258 := by
    simp [left, pairParityPorts, indexedPorts_length23]
    exact streamLayout_widths.inputX
  have hleft := windowOne_placed rows _ leftMem
  have hright := windowOne_placed rows _ rightMem
  intro i hi
  rcases finite23_member streamLayout rows i hi with old | fused
  · exact placed_implies_pair _ _ _ _ (windowOne_placed rows i old)
  · subst i
    exact fused_leaf_placed windowBits windowPaths windowRoot left right hlen hleft hright

theorem pairShort_literal_counts {n : Nat} (L : ControlledPointLayout) (t₁ t₂ c t : Wire)
    (rows : Nat → Fin n) :
    literalToffolis (wPairShortFused L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
      (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)))) =
    literalToffolis (wPairEqualTight L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) ++ wShortNegEqual L c t rows) ∧
    literalRecords (wPairShortFused L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
      (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)))) =
    literalRecords (wPairEqualTight L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) ++ wShortNegEqual L c t rows) := by
  constructor <;> simp [wPairShortFused, wPairEqualTight, wPairXorParity,
    wShortNegEqual, wShortNegXor, wLiteral, literalToffolis_append, literalRecords_append,
    literalToffolis, literalRecords]

theorem finite23_literal_counts {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    literalToffolis (wFinite23 L rows) = literalToffolis (wFiniteTight L rows) ∧
    literalRecords (wFinite23 L rows) = literalRecords (wFiniteTight L rows) := by
  have h := pairShort_literal_counts L L.doubleSelect L.genericSelect L.core.equalX L.core.equalNegY rows
  constructor
  · simp only [wFinite23, wFiniteTight, literalToffolis_append, h.1]
    omega
  · simp only [wFinite23, wFiniteTight, literalRecords_append, h.2]
    omega

def rowAddCode (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ wFinite23 streamLayout rows ++ wLiteral ([.X 838])

theorem rowAddCode_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ rowAddCode rows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  simp only [rowAddCode, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [wLiteral, List.mem_singleton] at hi
    subst i
    change ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ ECDSAAdd.wires ([.X 838] : Program)
    intro w hw hp
    have hg := window_reserved_gap w hw
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hp
    rw [hp] at hg
    norm_num at hg
  · exact window23_placed rows i hi
  · simp only [wLiteral, List.mem_singleton] at hi
    subst i
    change ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ ECDSAAdd.wires ([.X 838] : Program)
    intro w hw hp
    have hg := window_reserved_gap w hw
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hp
    rw [hp] at hg
    norm_num at hg

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem normalized_literals_valid {n : Nat} (code : WCode n)
    (hp : ∀ p, WInstr.literal p ∈ code → GatePhysical p) :
    ∀ p, WInstr.literal p ∈ normalizeW code → ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i := by
  intro p hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  cases j with
  | literal q =>
    cases he
    exact ECDSAAdd.Baselines.normalize_physical q (hp q hj)
  | lookup c ports => cases he

theorem rowAddCode_physical (rows : Nat → Fin 32768) :
    ∀ p, WInstr.literal p ∈ rowAddCode rows → GatePhysical p := by
  intro p hp
  simp only [rowAddCode, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hp
    subst p
    simp [GatePhysical, PhysicalInstr, ECDSAAdd.ProperGate]
  · exact (finiteOne_literal_facts streamLayout streamLayout_widths streamLayout_nodup rows p
      (tight_finite_literal_subset streamLayout rows p (finite23_literal_subset streamLayout rows p hp))).2
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hp
    subst p
    simp [GatePhysical, PhysicalInstr, ECDSAAdd.ProperGate]

attribute [local irreducible] compile normalizeW rowAddCode

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩
attribute [local irreducible] compile ECDSAAdd.run

def rowPointState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q (tableAddressValue windowBits s)) s

theorem rowAddCode_run (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (rowAddCode probeRows))
      (tableAddressValue windowBits s)).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
        ⟨false,rowPointState coeffs Q s⟩ := by
  rw [specialize_normalize_run]
  let a := tableAddressValue windowBits s
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have secp := hs.1.1.1.1
  have hq := hs.1.1.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr
      (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = ECDSAAdd.ShorPort.toA (.some hc) := congrArg ECDSAAdd.ShorPort.toA he
    have hr : ECDSAAdd.ShorPort.RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      ECDSAAdd.ShorPort.readConstant_rowReads coeffs Q _ _ ce
    have ho : order • (.some hc : ECDSAAdd.Secp256k1.Point) = 0 := by
      rw [← he]
      exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [order])
    have hd : (.some hc : ECDSAAdd.Secp256k1.Point)+.some hc ≠ 0 := by
      simpa only [two_nsmul] using hp2
    have ht : (.some hc : ECDSAAdd.Secp256k1.Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl, succ_nsmul, two_nsmul] using hp3
    have en := ECDSAAdd.ShorPort.enables_true hc hd ht
    have hdo : order • ((.some hc : ECDSAAdd.Secp256k1.Point)+.some hc) = 0 := by
      rw [nsmul_add, ho, zero_add]
    have inst := tight_stream_program_equiv (readConstant coeffs Q) probeRows a hc hr en.1 en.2 hd hdo
    have wrapped := programEquivalent_append
      (programEquivalent_append (programEquivalent_refl ([.X 838])) inst)
      (programEquivalent_refl ([.X 838]))
    simp only [rowAddCode, specialize_append, specialize_literal, specialize_finite23,
      ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    change ECDSAAdd.run (([.X 838]) ++ _ ++ ([.X 838])) m ⟨false,s⟩ = _
    rw [wrapped.2 m ⟨false,s⟩]
    have result := rowAdd_stream_run s P secp hP hq work hc m
    simpa only [rowPointState, inputPoint_eq s P hP, ← ce] using result

theorem rowAdd_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((compile windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows)) start).instantiate
        (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) liveReady := by
  have h := pair_compile_specialization_coherent (readConstant coeffs Q) windowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) (by simp [windowBits,windowPaths])
    (pair_placed_normalize _ _ _ _ (rowAddCode_placed probeRows)) liveReady (rowPointState coeffs Q)
    (rowAddCode_run coeffs Q hQ hn) start history
  obtain ⟨cs, aligned, mass⟩ := h
  exact ⟨cs, aligned.imp (fun _ _ hb s hs => hb s
    ⟨fun w hw => hs.2.1 w (List.mem_append_right _ hw), hs.2.2, hs⟩), mass⟩

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

def rowAddSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  source (readConstant coeffs Q) windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))

theorem rowAddSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowAddSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) liveReady := by
  obtain ⟨cs, aligned, mass⟩ := rowAdd_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs, ?_, mass⟩
  simpa only [compile_run, rowAddSource] using aligned

def signSource : AdaptiveCircuit := literalSource (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
def middleSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (signSource.seq (rowAddSource coeffs Q)).seq signSource

def middleState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  signPointState (rowPointState coeffs Q (signPointState s))

theorem middle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (middleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) liveReady := by
  have hs : CoherentlyImplementsOn signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady := windowSign_coherent
  have first := composeCoherent hs (rowAddSource_coherent coeffs Q hQ hn)
    (fun s h => liveReady_write _ s h)
  have all := composeCoherent first hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  exact all

@[simp] theorem inputPoint_write (P : Point) (s : BasisState) : inputPoint (pointWrite P s) = P :=
  inputPoint_eq _ P (pointWrite_coordinates P s)

@[simp] theorem write_sign (P : Point) (s : BasisState) : pointWrite P s 870 = s 870 :=
  pointWrite_frame P s 870 (by decide +kernel)

@[simp] theorem write_address (P : Point) (s : BasisState) :
    tableAddressValue windowBits (pointWrite P s) = tableAddressValue windowBits s := by
  apply tableAddressValue_congr
  intro w hw
  apply pointWrite_frame
  simp only [windowBits, List.mem_range'_1] at hw
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem middleState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    middleState coeffs Q s = pointWrite
      (P + if s 870 then Single.Physical.tablePoint coeffs Q (tableAddressValue windowBits s)
        else -Single.Physical.tablePoint coeffs Q (tableAddressValue windowBits s)) s := by
  by_cases hb : s 870 = true
  · simp [middleState, signPointState, rowPointState, inputPoint_eq s P hP,
      pointWrite_overwrite, hb]
  · have hf : s 870 = false := Bool.eq_false_iff.mpr hb
    simp [middleState, signPointState, rowPointState, inputPoint_eq s P hP,
      pointWrite_overwrite, hf, add_comm]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
-- Adapted from the verified Streaming preparation proof, Apache-2.0.
def windowPrepareState : BasisState → BasisState := signedAddressState 836 870 windowBits

theorem windowPrepareState_frame (s : BasisState) (w : Wire) (hw : w ∉ windowBits) :
    windowPrepareState s w=s w := signedAddressState_frame 836 870 windowBits s w hw

theorem window_address_outside_point (w : Wire) (hw : w ∈ pointLogicalWires) : w ∉ windowBits := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [windowBits,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem window_prepare_word (s : BasisState) (bits : List Wire)
    (h : ∀ w ∈ bits, w ∉ windowBits) : wireValues bits (windowPrepareState s)=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact windowPrepareState_frame s w (h w hw)

theorem windowPrepareState_ready (s : BasisState) (hs : BatchedPointReady s) : BatchedPointReady (windowPrepareState s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hw
    rw [windowPrepareState_frame s w (by
      simp only [List.mem_append,List.mem_range'_1] at hw
      simp only [windowBits,List.mem_range'_1]
      omega)]
    exact hs.1.1.1 w hw
  · rw [windowPrepareState_frame s 837 (by decide)]
    exact hs.1.1.2.1
  · rw [window_prepare_word s (List.range' 263 256) (fun w hw => window_address_outside_point w (List.mem_append_left _ hw))]
    exact hs.1.1.2.2.1
  · rw [window_prepare_word s (List.range' 580 256) (fun w hw => window_address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]
    exact hs.1.1.2.2.2
  · rw [windowPrepareState_frame s 836 (by decide)]
    exact hs.1.2
  · intro w hw
    simp [batchWorkspace] at hw

theorem windowPrepareState_coordinates (s : BasisState) : pointStateCoordinates (windowPrepareState s)=pointStateCoordinates s := by
  unfold pointStateCoordinates
  rw [windowPrepareState_frame s 838 (by decide),
    window_prepare_word s (List.range' 263 256) (fun w hw => window_address_outside_point w (List.mem_append_left _ hw)),
    window_prepare_word s (List.range' 580 256) (fun w hw => window_address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]

theorem windowPrepareState_pointWrite (P : Point) (s : BasisState) :
    windowPrepareState (pointWrite P s)=pointWrite P (windowPrepareState s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · rw [windowPrepareState_frame _ w (window_address_outside_point w hw)]
    simp only [pointWrite,if_pos hw]
  · rw [pointWrite_frame _ _ w hw]
    unfold windowPrepareState signedAddressState tableXorState
    rw [pointWrite_frame P s 870 (by decide +kernel),pointWrite_frame P s 836 (by decide +kernel),pointWrite_frame P s w hw]

theorem windowPrepareState_involution (s : BasisState) : windowPrepareState (windowPrepareState s)=s :=
  signedAddressState_involution 836 870 windowBits (by decide) (by decide) s
theorem windowPrepareState_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (windowPrepareState s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨windowPrepareState_ready s hs,P,(windowPrepareState_coordinates s).trans hP⟩


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def rootFlip (s : BasisState) : BasisState := ECDSAAdd.writeBit s windowRoot (!s windowRoot)

theorem rootFlip_involution (s : BasisState) : rootFlip (rootFlip s) = s := by
  funext w
  by_cases hw : w = windowRoot <;> simp [rootFlip,ECDSAAdd.writeBit,hw]

theorem rootFlip_pointWrite (P : Point) (s : BasisState) :
    rootFlip (pointWrite P s) = pointWrite P (rootFlip s) := by
  have hr : windowRoot ∉ pointLogicalWires := windowScratch_point_disjoint _ (by simp [windowScratch])
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have hwr : w ≠ windowRoot := fun h => hr (h ▸ hw)
    simp [rootFlip,ECDSAAdd.writeBit,pointWrite,hw,hwr]
  · rw [pointWrite_frame P (rootFlip s) w hw]
    unfold rootFlip
    rw [pointWrite_frame P s windowRoot hr]
    by_cases hwr : w = windowRoot
    · subst w
      simp [ECDSAAdd.writeBit]
    · simp [ECDSAAdd.writeBit,hwr,pointWrite_frame P s w hw]

theorem oldValid_small_frame (s t : BasisState)
    (hf : ∀ w : Wire, w < 839 → t w = s w)
    (hs : Paper2607_13816.ChallengeMigration.BatchedWindowValid s) :
    Paper2607_13816.ChallengeMigration.BatchedWindowValid t := by
  have h := windowPointValid_core s t hf ⟨hs.1.1,hs.2⟩
  refine ⟨⟨h.1, ?_⟩, h.2⟩
  intro w hw
  simp [batchWorkspace] at hw

theorem rootFlip_live (s : BasisState) (hs : windowReady s) : liveReady (rootFlip s) := by
  have hroot : s windowRoot = false := hs.2 _ (by simp [windowScratch])
  have hnot (w : Wire) (hw : w ∈ streamLayout.work ++ windowPaths) : w ≠ windowRoot := by
    rcases List.mem_append.mp hw with hw | hw
    · have hl := streamWork_lower w hw
      dsimp only [Wire] at *
      simp only [windowRoot]
      omega
    · simp only [windowPaths,List.mem_range'_1] at hw
      dsimp only [Wire] at *
      simp only [windowRoot]
      omega
  refine ⟨oldValid_small_frame s _ ?_ hs.1, ?_, ?_⟩
  · intro w hw
    have hn : w ≠ windowRoot := by dsimp only [Wire] at *; unfold windowRoot; omega
    simp [rootFlip,ECDSAAdd.writeBit,hn]
  · intro w hw
    simpa [rootFlip,ECDSAAdd.writeBit,hnot w hw] using hs.2 w (List.mem_append_left _ hw)
  · simp [rootFlip,ECDSAAdd.writeBit,hroot]

theorem windowPrepare_live (s : BasisState) (hs : liveReady s) : liveReady (windowPrepareState s) := by
  refine ⟨windowPrepareState_valid s hs.1, ?_, ?_⟩
  · intro w hw
    have hl := windowScratch_lower w (List.mem_append_left _ hw)
    rw [windowPrepareState_frame s w (by
      simp only [windowBits,List.mem_range'_1]
      dsimp only [Wire] at *; omega)]
    exact hs.2.1 w hw
  · rw [windowPrepareState_frame s windowRoot (by decide +kernel)]
    exact hs.2.2

def prefixState (s : BasisState) : BasisState := windowPrepareState (rootFlip s)
def suffixState (s : BasisState) : BasisState := rootFlip (windowPrepareState s)

theorem outer_inverse (s : BasisState) : suffixState (prefixState s) = s := by
  rw [suffixState,prefixState,windowPrepareState_involution,rootFlip_involution]

theorem suffix_pointWrite (P : Point) (s : BasisState) :
    suffixState (pointWrite P s) = pointWrite P (suffixState s) := by
  rw [suffixState,windowPrepareState_pointWrite,rootFlip_pointWrite]
  rfl

theorem rootFlip_coherent (V : BasisState → Prop) :
    CoherentlyImplementsOn (literalSource ([.X windowRoot])) (Finsupp.lmapDomain ℂ ℂ rootFlip) V := by
  apply literal_coherent
  intro s hs m
  rfl

theorem prepare_coherent (V : BasisState → Prop) :
    CoherentlyImplementsOn (.unitary (signedAddressCircuit 836 870 windowBits) .done)
      (Finsupp.lmapDomain ℂ ℂ windowPrepareState) V := by
  apply (CoherentlyImplementsOn.unitary _ V).congrIdeal
  intro s hs
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,windowPrepareState] using
    signedAddressCircuit_ket 836 870 windowBits (by decide +kernel) (by decide +kernel) (by decide +kernel) s

def prefixSource : AdaptiveCircuit :=
  (literalSource ([.X windowRoot])).seq (.unitary (signedAddressCircuit 836 870 windowBits) .done)
def suffixSource : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 870 windowBits) .done).seq (literalSource ([.X windowRoot]))

theorem prefix_coherent : CoherentlyImplementsOn prefixSource (Finsupp.lmapDomain ℂ ℂ prefixState) windowReady := by
  exact composeCoherent (f := rootFlip) (g := windowPrepareState) (rootFlip_coherent windowReady) (prepare_coherent (fun _ => True)) (fun _ _ => trivial)

theorem suffix_coherent : CoherentlyImplementsOn suffixSource (Finsupp.lmapDomain ℂ ℂ suffixState) (fun _ => True) := by
  exact composeCoherent (f := windowPrepareState) (g := rootFlip) (prepare_coherent (fun _ => True)) (rootFlip_coherent (fun _ => True)) (fun _ _ => trivial)

def bodySource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (prefixSource.seq (middleSource coeffs Q)).seq suffixSource

def bodyState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  suffixState (middleState coeffs Q (prefixState s))

theorem bodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (bodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) windowReady := by
  have h := composeCoherent prefix_coherent (middle_coherent coeffs Q hQ hn)
    (fun s hs => windowPrepare_live _ (rootFlip_live s hs))
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h suffix_coherent (fun _ _ => trivial)

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

theorem rootFlip_coordinates (s : BasisState) (P : Point) (hs : Secp256k1ZeroAllowedInputValid s)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    pointStateCoordinates (rootFlip s) = fig14PointEncoding P := by
  have he : s = pointWrite P s := StreamPoint.state_eq s s P hs
    (StreamPoint.of_coordinates s P hs hP) (fun _ _ => rfl)
  calc
    pointStateCoordinates (rootFlip s) = pointStateCoordinates (rootFlip (pointWrite P s)) :=
      congrArg (fun t => pointStateCoordinates (rootFlip t)) he
    _ = fig14PointEncoding P := by rw [rootFlip_pointWrite,pointWrite_coordinates]

theorem rootFlip_digit (s : BasisState) : windowRawDigit 0 (rootFlip s) = windowRawDigit 0 s := by
  simp [windowRawDigit,windowAddressBits,windowBankStart,wireValues,rootFlip,windowRoot,ECDSAAdd.writeBit,
    List.range',boolWordToNat]

theorem tableAddress_word (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s = boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simpa only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] using congrArg (fun n => (s b).toNat+2*n) ih

theorem prefix_address (s : BasisState) (hq : s 836 = true) :
    tableAddressValue windowBits (prefixState s) = signedTableAddress 32768 (windowRawDigit 0 s) := by
  rw [tableAddress_word,prefixState]
  have h := Paper2607_13816.windowPrepareState_address 0 (rootFlip s)
    (by simpa [rootFlip,ECDSAAdd.writeBit,windowRoot] using hq)
  change boolWordToNat (wireValues windowBits (windowPrepareState (rootFlip s))) =
    signedTableAddress 32768 (windowRawDigit 0 (rootFlip s)) at h
  rw [rootFlip_digit] at h
  exact h

theorem bodyState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : windowReady s) (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    bodyState coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)) else 0) s := by
  have hp : pointStateCoordinates (prefixState s) = fig14PointEncoding P :=
    (windowPrepareState_coordinates (rootFlip s)).trans (rootFlip_coordinates s P hs.1.1.1.1 hP)
  have hsign : prefixState s 870 = s 870 := by
    rw [prefixState,windowPrepareState_frame _ _ (by decide +kernel)]
    simp [rootFlip,ECDSAAdd.writeBit,windowRoot]
  rw [bodyState,middleState_correct coeffs Q _ P hp,suffix_pointWrite,outer_inverse,
    hsign,prefix_address s (windowReady_active s hs)]
  simp only [windowReady_active s hs]
  simp only [if_pos True.intro]
  simp only [Single.Physical.tablePoint,Nat.mod_eq_of_lt
    (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] compile Bridge.translate codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount literalToffolis

theorem windowSign_counts : ECDSAAdd.toffoliCount windowSignProgram = 1022 ∧
    ECDSAAdd.measurementCount windowSignProgram = 1022 := by
  have widths := negateYLayout_widths streamLayout streamLayout_widths
  have c := negate_256_counts (negateYLayout streamLayout) streamLayout.core.generic ECDSAAdd.p
    SquareReduction.c widths.2 widths.1
  simp only [windowSignProgram, signedYProgram, ECDSAAdd.toffoliCount_append,
    ECDSAAdd.measurementCount_append, flagPrepare, flagClear, ECDSAAdd.toffoliCount,
    ECDSAAdd.measurementCount, Nat.zero_add, Nat.add_zero, c.1, c.2]
  exact ⟨True.intro,True.intro⟩

theorem rowAdd_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) = 2245006 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (rowAddCode_placed probeRows))
  have h := wrapper_record_ledger windowBits windowPaths windowRoot ([.X 838]) ([.X 838])
    (wFinite23 streamLayout probeRows) 1556899 21
    ((finite23_literal_counts streamLayout probeRows).2.trans
      (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).2)
    (traversals_finite23 streamLayout probeRows) layouts
  simp only [show ECDSAAdd.measurementCount ([.X 838]) = 0 by simp only [ECDSAAdd.measurementCount]] at h
  norm_num [windowBits] at h
  simpa only [rowAddCode, List.append_assoc, windowBits] using h

def literalFixed {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m) (start : Nat) : Straight n start (start+m) :=
  NaiveChallenge.castFinish (congrArg (fun k => start+k) hm) (Bridge.translate (literalT p) start)

def compilerFixed {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n) (m : Nat)
    (hm : codeRecords bits paths root code = m) (start : Nat) : Straight n start (start+m) :=
  NaiveChallenge.castFinish (congrArg (fun k => start+k) hm) (compile bits paths root code start)

theorem literalFixed_tCount {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((literalFixed p m hm start).instantiate read history).tCount = 7 * ECDSAAdd.toffoliCount p := by
  rw [literalFixed,NaiveChallenge.instantiate_castFinish]
  exact literal_program_tCount p start read history

theorem compilerFixed_tCount {n : Nat} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (root : Wire) (code : WCode n) (hl : LookupLayouts bits paths root code)
    (m : Nat) (hm : codeRecords bits paths root code = m)
    (htr : traversals code = 21) (hnodes : 2^bits.length-1 = 32767)
    (start : Nat) (history : Fin start → Bool) :
    ((compilerFixed bits paths root code m hm start).instantiate read history).tCount =
      7 * literalToffolis code + 4816749 := by
  rw [compilerFixed,NaiveChallenge.instantiate_castFinish,
    compile_tCount read bits paths root code hl start history,htr,hnodes]

theorem literalFixed_run {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((literalFixed p m hm start).instantiate read history).run = (literalSource p).run := by
  rw [literalFixed,NaiveChallenge.instantiate_castFinish,literal_run]

theorem compilerFixed_run {n : Nat} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (root : Wire) (code : WCode n) (m : Nat) (hm : codeRecords bits paths root code = m)
    (start : Nat) (history : Fin start → Bool) :
    ((compilerFixed bits paths root code m hm start).instantiate read history).run =
      (source read bits paths root code).run := by
  rw [compilerFixed,NaiveChallenge.instantiate_castFinish,compile_run]

theorem literalFixed_wellFormed {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m)
    (hp : ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i) (start : Nat) :
    (literalFixed p m hm start).WellFormed := by
  rw [literalFixed,NaiveChallenge.wellFormed_castFinish]
  apply Bridge.translate_wellFormed
  intro i hi
  rw [literalT] at hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact hp j hj

theorem compilerFixed_wellFormed {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (m : Nat) (hm : codeRecords bits paths root code = m) (hl : bits.length ≤ paths.length)
    (hp : ∀ i ∈ code, PlacedPair bits paths root i)
    (hv : ∀ p, WInstr.literal p ∈ code → ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i)
    (start : Nat) : (compilerFixed bits paths root code m hm start).WellFormed := by
  rw [compilerFixed,NaiveChallenge.wellFormed_castFinish]
  exact pair_compile_wellFormed bits paths root code hl hp hv start

theorem literalFixed_slots {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m) (start : Nat) :
    (literalFixed p m hm start).gateSlots = Bridge.tmplSlots (literalT (n := n) p) := by
  rw [literalFixed,NaiveChallenge.gateSlots_castFinish,Bridge.translate_gateSlots]

theorem compilerFixed_slots {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (m : Nat) (hm : codeRecords bits paths root code = m) (hl : LookupLayouts bits paths root code)
    (start : Nat) : (compilerFixed bits paths root code m hm start).gateSlots = codeSlots bits code := by
  rw [compilerFixed,NaiveChallenge.gateSlots_castFinish]
  exact compile_slots bits paths root code hl start

def nProgram (start : Nat) : Straight 32768 start (start+1022) :=
  literalFixed (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) 1022
    ((literal_meas (n := 32768) _).trans
      ((ECDSAAdd.Baselines.normalize_measurements windowSignProgram).trans windowSign_counts.2)) start

def addProgram (start : Nat) : Straight 32768 start (start+2245006) :=
  compilerFixed windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows)) 2245006 rowAdd_records start

def prefixProgram (start : Nat) : Straight 32768 start start :=
  (literalProgram ([.X windowRoot])).append (literalProgram (signedAddressCircuit 836 870 windowBits))

def suffixProgram (start : Nat) : Straight 32768 start start :=
  (literalProgram (signedAddressCircuit 836 870 windowBits)).append (literalProgram ([.X windowRoot]))

def bodyProgram (start : Nat) : Straight 32768 start (start+2247050) :=
  NaiveChallenge.castFinish (by omega)
    (((((prefixProgram start).append (nProgram start)).append (addProgram (start+1022))).append
      (nProgram (start+1022+2245006))).append (suffixProgram (start+1022+2245006+1022)))

theorem nProgram_run (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((nProgram start).instantiate read history).run = signSource.run :=
  literalFixed_run (n := 32768) _ _ _ start read history

theorem addProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (history : Fin start → Bool) :
    ((addProgram start).instantiate (readConstant coeffs Q) history).run = (rowAddSource coeffs Q).run :=
  compilerFixed_run (readConstant coeffs Q) windowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) 2245006 rowAdd_records start history

theorem prefixProgram_run (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((prefixProgram start).instantiate read history).run = prefixSource.run := by
  rw [prefixProgram,append_run_fixed _ _ _ _ _ (fun h => literalProgram_run _ read h),
    AdaptiveCircuit.run_seq,literalProgram_run,← AdaptiveCircuit.run_seq]
  rfl

theorem suffixProgram_run (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((suffixProgram start).instantiate read history).run = suffixSource.run := by
  rw [suffixProgram,append_run_fixed _ _ _ _ _ (fun h => literalProgram_run _ read h),
    AdaptiveCircuit.run_seq,literalProgram_run,← AdaptiveCircuit.run_seq]
  rfl

theorem bodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (history : Fin start → Bool) :
    ((bodyProgram start).instantiate (readConstant coeffs Q) history).run = (bodySource coeffs Q).run := by
  rw [bodyProgram,NaiveChallenge.instantiate_castFinish]
  rw [append_run_fixed _ _ _ _ _ (fun h => suffixProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => addProgram_run _ coeffs Q h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq,prefixProgram_run]
  simp only [← AdaptiveCircuit.run_seq,bodySource,middleSource,adaptive_seq_assoc]

end
end ShorECDLP.Entrant.WEX

/-! Complete WEX body and its Streaming certificate. Resource bounds cover every reader and history. -/


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

theorem rowAddLayouts : LookupLayouts windowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) :=
  pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    (by simp [windowBits,windowPaths])
    (pair_placed_normalize windowBits windowPaths windowRoot (rowAddCode probeRows) (rowAddCode_placed probeRows))

end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.RecordedQuantum
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
attribute [local irreducible] compile Bridge.translate codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount literalToffolis
  GatePhysical CompactRecoveryNegateLayout.program signedYProgram windowSignProgram

theorem signedY_physical (K : NegLayout) (sign flag p c : Nat)
    (hp : GatePhysical (K.program flag p c)) (hne : sign ≠ flag) :
    GatePhysical (signedYProgram K sign flag p c) := by
  simp only [signedYProgram,gatePhysical_append]
  refine ⟨⟨?_,hp⟩,?_⟩ <;>
    simp [flagPrepare,flagClear,GatePhysical,PhysicalInstr,ECDSAAdd.ProperGate,hne]

theorem windowSign_physical : GatePhysical windowSignProgram := by
  unfold windowSignProgram
  exact signedY_physical (negateYLayout streamLayout) 870 streamLayout.core.generic ECDSAAdd.p SquareReduction.c
    (negate_physical (negateYLayout streamLayout) streamLayout.core.generic ECDSAAdd.p SquareReduction.c
      (negateYLayout_nodup_generic streamLayout streamLayout_widths streamLayout_nodup)
      (negateYLayout_widths streamLayout streamLayout_widths).2) (by decide +kernel)

theorem nProgram_wellFormed (start : Nat) : (nProgram start).WellFormed :=
  literalFixed_wellFormed (n := 32768) _ _ _
    (ECDSAAdd.Baselines.normalize_physical windowSignProgram (by simpa only [GatePhysical] using windowSign_physical)) start

theorem addProgram_wellFormed (start : Nat) : (addProgram start).WellFormed :=
  compilerFixed_wellFormed windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    2245006 rowAdd_records (by simp [windowBits,windowPaths])
    (pair_placed_normalize windowBits windowPaths windowRoot (rowAddCode probeRows) (rowAddCode_placed probeRows))
    (normalized_literals_valid (rowAddCode probeRows) (rowAddCode_physical probeRows)) start

theorem prefixProgram_wellFormed (start : Nat) : (prefixProgram start).WellFormed := by
  rw [prefixProgram]
  apply straight_append_wellFormed
  · exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])
  · exact literalProgram_wellFormed _
      (signedAddressCircuit_wellFormed 836 870 windowBits (by decide +kernel) (by decide +kernel))

theorem suffixProgram_wellFormed (start : Nat) : (suffixProgram start).WellFormed := by
  rw [suffixProgram]
  apply straight_append_wellFormed
  · exact literalProgram_wellFormed _
      (signedAddressCircuit_wellFormed 836 870 windowBits (by decide +kernel) (by decide +kernel))
  · exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])

theorem bodyProgram_wellFormed (start : Nat) : (bodyProgram start).WellFormed := by
  rw [bodyProgram,NaiveChallenge.wellFormed_castFinish]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nProgram_wellFormed start)
      · exact addProgram_wellFormed _
    · exact nProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem nProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((nProgram start).instantiate read history).tCount =
      7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) :=
  literalFixed_tCount (n := 32768) _ _ _ start read history

theorem rowAdd_traversals : traversals (normalizeW (rowAddCode probeRows)) = 21 := by
  rw [traversals_normalize]
  simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]

theorem addProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((addProgram start).instantiate read history).tCount =
      7 * literalToffolis (normalizeW (rowAddCode probeRows)) + 4816749 :=
  compilerFixed_tCount read windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    rowAddLayouts 2245006 rowAdd_records rowAdd_traversals (by decide +kernel) start history

theorem prefixProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((prefixProgram start).instantiate read history).tCount = 0 := by
  rw [prefixProgram,append_tCount_fixed _ _ _ _ _
    (fun h => literalProgram_tCount _ read h),literalProgram_tCount,signedAddressCircuit_tCount]
  rfl

theorem suffixProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((suffixProgram start).instantiate read history).tCount = 0 := by
  rw [suffixProgram,append_tCount_fixed _ _ _ _ _
    (fun h => literalProgram_tCount _ read h),literalProgram_tCount,signedAddressCircuit_tCount]
  rfl

theorem append_count_eq {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (x y : Nat)
    (hp : ∀ h, (p.instantiate read h).tCount = x) (hq : ∀ h, (q.instantiate read h).tCount = y)
    (history : Fin a → Bool) : ((p.append q).instantiate read history).tCount = x+y := by
  have h := append_tCount_fixed p q read history y hq
  rw [hp history] at h
  exact h

theorem erase_count_zeros (x y : Nat) : 0+x+y+x+0 = x+y+x := by omega

theorem bodyProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((bodyProgram start).instantiate read history).tCount =
      7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      (7 * literalToffolis (normalizeW (rowAddCode probeRows)) + 4816749) +
      7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) := by
  let p1 := (prefixProgram start).append (nProgram start)
  let p2 := p1.append (addProgram (start+1022))
  let p3 := p2.append (nProgram (start+1022+2245006))
  have h1 := append_count_eq (prefixProgram start) (nProgram start) read 0
    (7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    (prefixProgram_tCount start read) (nProgram_tCount start read)
  have h2 := append_count_eq p1 (addProgram (start+1022)) read
    (0+7*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    (7*literalToffolis (normalizeW (rowAddCode probeRows))+4816749) h1 (addProgram_tCount (start+1022) read)
  have h3 := append_count_eq p2 (nProgram (start+1022+2245006)) read
    (0+7*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)+
      (7*literalToffolis (normalizeW (rowAddCode probeRows))+4816749))
    (7*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    h2 (nProgram_tCount (start+1022+2245006) read)
  have h4 := append_count_eq p3 (suffixProgram (start+1022+2245006+1022)) read
    (0+7*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)+
      (7*literalToffolis (normalizeW (rowAddCode probeRows))+4816749)+
      7*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    0 h3 (suffixProgram_tCount (start+1022+2245006+1022) read)
  have hm : start+1022+2245006+1022 = start+2247050 := by omega
  have hc := congrArg AdaptiveCircuit.tCount (NaiveChallenge.instantiate_castFinish hm
    (p3.append (suffixProgram (start+1022+2245006+1022))) read history)
  exact hc.trans ((h4 history).trans (erase_count_zeros _ _))

theorem bodyT_bound :
    7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      (7 * literalToffolis (normalizeW (rowAddCode probeRows)) + 4816749) +
      7 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) ≤ 19964056 := by
  have hn := ECDSAAdd.Baselines.normalize_toffoli windowSignProgram
  rw [windowSign_counts.1] at hn
  have ha := literalToffolis_normalize (rowAddCode probeRows)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (rowAddCode probeRows) = 2156628 := by
    simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
      Nat.zero_add,Nat.add_zero,hc]
  rw [hrow] at ha
  omega

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
attribute [local irreducible] ECDSAAdd.Challenge.gateSlots ECDSAAdd.run ECDSAAdd.regValue

def literalSlotSum {n : Nat} : WCode n → Nat
  | [] => 0
  | .literal p :: code => ECDSAAdd.Challenge.gateSlots p + literalSlotSum code
  | .lookup _ _ :: code => literalSlotSum code

def portTotal {n : Nat} : WCode n → Nat
  | [] => 0
  | .literal _ :: code => portTotal code
  | .lookup _ ports :: code => ports.length + portTotal code

theorem literalSlotSum_append' {n : Nat} (xs ys : WCode n) :
    literalSlotSum (xs ++ ys) = literalSlotSum xs + literalSlotSum ys := by
  induction xs with
  | nil => simp [literalSlotSum]
  | cons x xs ih => cases x <;> simp [literalSlotSum, ih, Nat.add_assoc]

theorem tight_pair_literal_slots {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) :
    literalSlotSum (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) =
      literalSlotSum (wPairEqualOpposite L t₁ t₂ fin xr r₁ r₂) := by
  have hz (c : Wire) (bs : List ZeroBit) :
      literalSlotSum (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂) c bs) =
        literalSlotSum (wZeroWith (wPairTailOpposite (yLow L) t₁ t₂ r₁ r₂) c bs) := by
    induction bs generalizing c with
    | nil => simp [wZeroWith, wPairTailOpposite, wPairTailBare, wLiteral, literalSlotSum]
    | cons b bs ih => simp [wZeroWith, literalSlotSum_append', ih]
  have h := hz L.control (pairPorts L)
  simpa [wPairEqualOpposite, wPairEqualTight, wPairXor, wPairXorParity, literalSlotSum_append',
    literalSlotSum] using h

theorem tight_finite_literal_slots {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    literalSlotSum (wFiniteTight L rows) = literalSlotSum (wFiniteOne L rows) := by
  have h₁ := tight_pair_literal_slots L L.doubleSelect L.genericSelect (wBit rows .infinity)
    (wFields rows .x) (wBit rows .y) (wBit rows .negY)
  have h₂ := tight_pair_literal_slots L L.infinitySelect L.core.equalNegY (wBit rows .infinity)
    (wFields rows .x) (wBit rows .y) (wBit rows .negY)
  simp only [wFiniteTight, wFiniteOne, literalSlotSum_append', h₁, h₂]


theorem portTotal_append' {n : Nat} (xs ys : WCode n) :
    portTotal (xs ++ ys) = portTotal xs + portTotal ys := by
  induction xs with
  | nil => simp [portTotal]
  | cons x xs ih => cases x <;> simp [portTotal, ih, Nat.add_assoc]

@[simp] theorem indexedPorts_length' {n : Nat} (ws : List Wire)
    (refs : Nat → Nat → CBit n) (v : Bool) : (indexedPorts ws refs v).length = ws.length := by
  have h := congrArg List.length (indexedPorts_targets ws refs v)
  simpa [portTargets] using h

theorem portTotal_zeroWith {n : Nat} (tail : Wire → WCode n) (k : Nat)
    (h : ∀ w, portTotal (tail w) = k) (c : Wire) (bs : List ZeroBit) :
    portTotal (wZeroWith tail c bs) = k := by
  induction bs generalizing c with
  | nil => exact h c
  | cons b bs ih => simp [wZeroWith, portTotal_append', wLiteral, portTotal, ih]


theorem pairShort_slots_ports {n : Nat} (L : ControlledPointLayout) (t₁ t₂ c t : Wire)
    (rows : Nat → Fin n) :
    literalSlotSum (wPairShortFused L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
      (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)))) =
    literalSlotSum (wPairEqualTight L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) ++ wShortNegEqual L c t rows) ∧
    portTotal (wPairShortFused L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
      (zeroControlled c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)))) =
    portTotal (wPairEqualTight L t₁ t₂ (wBit rows .infinity) (wFields rows .x)
      (wBit rows .y) (wBit rows .negY) ++ wShortNegEqual L c t rows) := by
  constructor
  · simp [wPairShortFused, wPairEqualTight, wPairXorParity, wShortNegEqual, wShortNegXor,
      wLiteral, literalSlotSum_append', literalSlotSum]
  · simp [wPairShortFused, wPairEqualTight, wPairXorParity, wShortNegEqual, wShortNegXor,
      pairParityPorts, shortNegPorts, wLiteral, portTotal_append', portTotal]
    omega

theorem finite23_slots_ports {n : Nat} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    literalSlotSum (wFinite23 L rows) = literalSlotSum (wFiniteTight L rows) ∧
    portTotal (wFinite23 L rows) = portTotal (wFiniteTight L rows) := by
  have h := pairShort_slots_ports L L.doubleSelect L.genericSelect L.core.equalX L.core.equalNegY rows
  constructor
  · simp only [wFinite23, wFiniteTight, literalSlotSum_append', h.1]
    omega
  · simp only [wFinite23, wFiniteTight, portTotal_append', h.2]
    omega

@[simp] theorem tight_pair_ports_exact {n : Nat} (L : ControlledPointLayout) (t₁ t₂ : Wire)
    (fin : Nat → CBit n) (xr : Nat → Nat → CBit n) (r₁ r₂ : Nat → CBit n) :
    portTotal (wPairEqualTight L t₁ t₂ fin xr r₁ r₂) = 2 * (L.point.x.length + 2) := by
  have hz : portTotal (wZeroWith (wPairTailBare (n := n) (yLow L) t₁ t₂)
      L.control (pairPorts L)) = 0 := portTotal_zeroWith _ 0 (fun _ => by simp [wPairTailBare, wLiteral, portTotal]) _ _
  simp [wPairEqualTight, wPairXorParity, portTotal_append', portTotal, hz]
  omega

theorem rowAdd_ports_exact : portTotal (rowAddCode probeRows) = 6676 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have ht : (streamLayout.point.y.take 1).length = 1 := by simp [List.length_take, hy]
  have hc (r : List Wire) : (streamLayout.recoveryConstant r).src.length = 256 := by
    change (streamLayout.dialogPool.take 256).length = 256
    decide +kernel
  simp [rowAddCode, portTotal_append', (finite23_slots_ports streamLayout probeRows).2, wFiniteTight, wShortNegEqual, wShortNegXor, wShortEqual, wShortXor,
    wGeneric, wRecovery, wConstAdd, wMask, wCornersOne, wPoint, wLiteral, portTotal_append',
    portTotal, tight_pair_ports_exact, hx, hy, ht, hc]
attribute [local irreducible] Straight.gateSlots compile Bridge.translate codeSlots literalSlotSum portTotal

theorem literal_slot_bound {n : Nat} (p : ECDSAAdd.Program) :
    Bridge.tmplSlots (literalT (n := n) p) ≤ 3 * ECDSAAdd.Challenge.gateSlots p := by
  induction p with
  | nil => exact Nat.zero_le _
  | cons i p ih =>
    cases i <;> simp only [literalT,List.map_cons,Bridge.tmplSlots,List.sum_cons,
      Bridge.TInstr.slots,ECDSAAdd.Baselines.gateSlots_cons,ECDSAAdd.Challenge.instructionSlots] at ih ⊢
    all_goals try simp only [Bridge.corrsSlots]
    all_goals omega

@[simp] theorem literalSlotSum_normalize {n : Nat} (code : WCode n) :
    literalSlotSum (normalizeW code) = literalSlotSum code := by
  induction code with
  | nil => rfl
  | cons i code ih => cases i <;>
      simp only [normalizeW,List.map_cons,normalizeWInstr,literalSlotSum,ECDSAAdd.Baselines.normalize_slots] at ih ⊢ <;> omega

theorem literalSlotSum_specialize {n : Nat} (read : ConstantBit n → Bool) (code : WCode n) (a : Nat) :
    literalSlotSum code ≤ ECDSAAdd.Challenge.gateSlots ((specialize code a).instantiate read) := by
  induction code with
  | nil =>
    rw [literalSlotSum]
    exact Nat.zero_le _
  | cons i code ih =>
    cases i with
    | literal p =>
      rw [literalSlotSum]
      change ECDSAAdd.Challenge.gateSlots p + literalSlotSum code ≤
        ECDSAAdd.Challenge.gateSlots ((Tmpl.lit p ++ specialize code a).instantiate read)
      rw [Tmpl.instantiate_append,Tmpl.instantiate_lit,ECDSAAdd.Challenge.gateSlots_append]
      omega
    | lookup c ports =>
      rw [literalSlotSum]
      change literalSlotSum code ≤ ECDSAAdd.Challenge.gateSlots
        ((portTemplate c ports a ++ specialize code a).instantiate read)
      rw [Tmpl.instantiate_append,ECDSAAdd.Challenge.gateSlots_append]
      omega

theorem codeSlots_bound {n : Nat} (bits : List Wire) (code : WCode n) :
    codeSlots bits code ≤ 3 * literalSlotSum code + 2 ^ bits.length * portTotal code +
      10 * traversals code * (2 ^ bits.length - 1) := by
  induction code with
  | nil => simp [codeSlots,literalSlotSum,portTotal,traversals]
  | cons i code ih =>
    cases i with
    | literal p =>
      have hp := literal_slot_bound (n := n) p
      simp only [codeSlots,literalSlotSum,portTotal,traversals]
      omega
    | lookup c ports =>
      simp only [codeSlots,literalSlotSum,portTotal,traversals]
      nlinarith

@[simp] theorem portTotal_normalize {n : Nat} (code : WCode n) :
    portTotal (normalizeW code) = portTotal code := by
  induction code with
  | nil => rfl
  | cons i code ih => cases i <;> simp only [normalizeW,List.map_cons,normalizeWInstr,portTotal] at ih ⊢ <;> omega

theorem negate_slots_general (K : NegLayout) (q p c : Nat)
    (hw : K.work.length = K.word.length) :
    ECDSAAdd.Challenge.gateSlots (K.program q p c) ≤ 53 * K.word.length + 2 := by
  have check := ECDSAAdd.Baselines.equalConstant_gateSlots_le q K.zero (zeroPorts K.word K.work) 0
  have flip := ECDSAAdd.Baselines.maskedConstant_gateSlots_le q K.word (2^K.word.length-1)
  have add1 := ECDSAAdd.Baselines.mappedConst_gateSlots_le (some q) K.word K.carries K.cin (p+1)
  have add2 := ECDSAAdd.Baselines.mappedConst_gateSlots_le (some K.zero) K.word K.carries K.cin c
  have len : (zeroPorts K.word K.work).length = K.word.length := by
    simpa only [List.length_map] using congrArg List.length (zeroPorts_maps K.word K.work hw.symm).1
  rw [len] at check
  simp only [CompactRecoveryNegateLayout.program,CompactRecoveryNegateLayout.checkZero,
    CompactRecoveryNegateLayout.complement,CompactRecoveryNegateLayout.add,ECDSAAdd.Challenge.gateSlots_append]
  omega

theorem negate_slots_bound (q : Nat) : ECDSAAdd.Challenge.gateSlots
    ((negateYLayout streamLayout).program q ECDSAAdd.p SquareReduction.c) ≤ 20000 := by
  have h := negate_slots_general (negateYLayout streamLayout) q ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2
  rw [(negateYLayout_widths streamLayout streamLayout_widths).1] at h
  omega

attribute [local irreducible] Arith.genericS Arith.padding ECDSAAdd.Frontier.arithS ECDSAAdd.Frontier.SquareOB5.program

set_option linter.unusedSimpArgs false in
theorem finiteOneS_slots_bound (C : ECDSAAdd.Secp256k1.Point) (cx cy : ECDSAAdd.Fp) :
    ECDSAAdd.Challenge.gateSlots (finiteOneS streamLayout C cx cy) ≤ 50000000 := by
  let L := streamLayout
  have hw := streamLayout_widths
  have hg := Arith.genericS_slots L hw streamLayout_nodup cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hm (c : ECDSAAdd.Wire) (P : ECDSAAdd.Secp256k1.Point) :
      ECDSAAdd.Challenge.gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := ECDSAAdd.Baselines.maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : ECDSAAdd.Challenge.gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [ECDSAAdd.Challenge.gateSlots,ECDSAAdd.Challenge.instructionSlots]
  have hh : ECDSAAdd.Challenge.gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable
    split <;> simp [ECDSAAdd.Challenge.gateSlots,ECDSAAdd.Challenge.instructionSlots]
  have hf : ECDSAAdd.Challenge.gateSlots (pointDialogGenericFlag L) = 5 := by
    simp [pointDialogGenericFlag,pointInPlaceGenericFlag,ECDSAAdd.Challenge.gateSlots,
      ECDSAAdd.Challenge.instructionSlots]
  have hz (t : ECDSAAdd.Wire) : ECDSAAdd.Challenge.gateSlots (zeroFlag L.point.finite L.control t) = 3 := by
    simp [zeroFlag,ECDSAAdd.Challenge.gateSlots,ECDSAAdd.Challenge.instructionSlots]
  have p1 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_gateSlots_le L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have s1 := shortEqual_gateSlots_le L hw L.core.equalX L.core.equalNegY (ECDSAAdd.Secp256k1.dialogExceptionPoint C)
  have s2 := shortEqual_gateSlots_le L hw L.core.double L.doubleSelect (C+C)
  have m1 := hm L.core.equalNegY (C+C)
  have m3 := hm L.doubleSelect C
  have m4 := hm L.doubleSelect (C+C)
  have m6 := hm L.core.equalNegY (-C)
  have neg := negate_slots_bound L.core.equalNegY
  have pad := Arith.padding_slots (L.core.poolWire 0) 51716
  change ECDSAAdd.Challenge.gateSlots (finiteOneS L C cx cy) ≤ _
  simp only [finiteOneS,finiteOneS_base,secondCorners,
    ECDSAAdd.Challenge.gateSlots_append,hf,hz,ECDSAAdd.Baselines.gateSlots_cons,
    ECDSAAdd.Baselines.gateSlots_nil,ECDSAAdd.Challenge.instructionSlots]
  dsimp only [L] at *
  omega

def rowAddReference (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ wFiniteOne streamLayout rows ++ wLiteral ([.X 838])

theorem referenceRow_literal_slots_bound : literalSlotSum (rowAddReference probeRows) ≤ 50000002 := by
  change literalSlotSum (wLiteral ([.X 838]) ++ wFiniteOne streamLayout probeRows ++ wLiteral ([.X 838])) ≤ 50000002
  let P : ECDSAAdd.Secp256k1.Point := Bridge.toB ShorECDLP.Secp256k1.G
  have hP : P ≠ 0 := ShorECDLP.Secp256k1.G_ne_zero
  have target : literalSlotSum (rowAddReference probeRows) ≤ ECDSAAdd.Challenge.gateSlots
      ((specialize (rowAddReference probeRows) 0).instantiate
        (fun ref => (fieldValue (toA P) ref.field).testBit ref.bit.val)) := literalSlotSum_specialize _ _ _
  cases hp : P with
  | zero => exact (hP hp).elim
  | @some cx cy hc =>
    have hk : toA (.some hc) = (1 : Nat) • ShorECDLP.Secp256k1.G := by rw [one_nsmul,← hp]; rfl
    have en := enables_of_multiple hc 1 hk
    have structural := double_triple_ne_zero (.some hc) 1 hk (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have ho : ShorECDLP.order • ((.some hc : ECDSAAdd.Secp256k1.Point)+.some hc) = 0 := by
      rw [← hp]
      change ShorECDLP.order • (ShorECDLP.Secp256k1.G+ShorECDLP.Secp256k1.G) = 0
      rw [nsmul_add,ShorECDLP.Secp256k1.generator_nsmul_eq_zero,zero_add]
    have inst := wFiniteOne_inst (fun ref => (fieldValue (toA P) ref.field).testBit ref.bit.val)
      streamLayout streamLayout_widths probeRows 0 hc (by intro f i; change (fieldValue (toA P) f).testBit i.val = _; rw [hp]) en.1 en.2 structural.1 ho
    simp only [rowAddReference,specialize_append,specialize_literal,Tmpl.instantiate_append,Tmpl.instantiate_lit] at target
    rw [inst] at target
    have bound := finiteOneS_slots_bound (.some hc) cx cy
    simp only [ECDSAAdd.Challenge.gateSlots_append,ECDSAAdd.Baselines.gateSlots_cons,
      ECDSAAdd.Baselines.gateSlots_nil,ECDSAAdd.Challenge.instructionSlots] at target
    omega


theorem rowAdd_literal_slots_bound : literalSlotSum (rowAddCode probeRows) ≤ 50000002 := by
  have h := referenceRow_literal_slots_bound
  simp only [rowAddReference, literalSlotSum_append'] at h
  simpa only [rowAddCode, literalSlotSum_append', (finite23_slots_ports streamLayout probeRows).1, tight_finite_literal_slots] using h

theorem rowAdd_portTotal : portTotal (rowAddCode probeRows) ≤ 20000 := by
  rw [rowAdd_ports_exact]
  decide +kernel

theorem addProgram_slots (start : Nat) : (addProgram start).gateSlots =
    codeSlots windowBits (normalizeW (rowAddCode probeRows)) :=
  compilerFixed_slots windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    2245006 rowAdd_records rowAddLayouts start

theorem nProgram_slots (start : Nat) : (nProgram start).gateSlots =
    Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)) :=
  literalFixed_slots (n := 32768) _ _ _ start

theorem rowAdd_slots_bound (start : Nat) : (addProgram start).gateSlots ≤ 1000000000 := by
  rw [addProgram_slots]
  have bound := codeSlots_bound windowBits (normalizeW (rowAddCode probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at bound
  have literal := rowAdd_literal_slots_bound
  have ports := rowAdd_portTotal
  have trav : traversals (rowAddCode probeRows) = 21 := by
    simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]
  rw [trav] at bound
  have hlen : windowBits.length = 15 := by simp [windowBits]
  rw [hlen] at bound
  norm_num at bound
  omega

theorem sign_slots_bound : ECDSAAdd.Challenge.gateSlots windowSignProgram ≤ 100000 := by
  have h := negate_slots_bound streamLayout.core.generic
  simp only [windowSignProgram,signedYProgram,ECDSAAdd.Challenge.gateSlots_append,flagPrepare,flagClear,
    ECDSAAdd.Baselines.gateSlots_cons,ECDSAAdd.Baselines.gateSlots_nil,ECDSAAdd.Challenge.instructionSlots]
  omega

theorem bodyProgram_slots_exact (start : Nat) : (bodyProgram start).gateSlots =
    2 * Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)) +
      codeSlots windowBits (normalizeW (rowAddCode probeRows)) + 62 := by
  rw [bodyProgram,NaiveChallenge.gateSlots_castFinish]
  simp only [Straight.gateSlots_append,nProgram_slots,addProgram_slots,prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  omega

theorem bodyProgram_slots_bound (start : Nat) : (bodyProgram start).gateSlots ≤ 1100000000 := by
  rw [bodyProgram_slots_exact]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := sign_slots_bound
  have row := rowAdd_slots_bound start
  rw [addProgram_slots] at row
  omega

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

def wireBound (w : Nat) : Prop := w < 839 ∨ (14111 ≤ w ∧ w < 16728) ∨ (19814 ≤ w ∧ w < 19817)
instance (w : Nat) : Decidable (wireBound w) := inferInstanceAs (Decidable (w < 839 ∨ (14111 ≤ w ∧ w < 16728) ∨ (19814 ≤ w ∧ w < 19817)))

def bodySupport : List Wire := completeBatchedSupport ++ List.range' 14111 2617 ++
  List.range' 19814 3 ++ windowPaths ++ [windowRoot]

theorem base_subset_support : completeBatchedSupport ⊆ bodySupport := by
  intro w hw
  simp only [bodySupport,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl hw)))

theorem wireBound_support (w : Wire) (hw : wireBound w) : w ∈ bodySupport := by
  rcases hw with hlo | hmid | hhi
  · have hb : w ∈ completeBatchedSupport := by
      simp only [completeBatchedSupport,resetWires,List.mem_cons,List.mem_append,List.mem_range,
        List.mem_range'_1]
      dsimp only [Wire] at *
      omega
    exact base_subset_support hb
  · have hm : w ∈ List.range' 14111 2617 := List.mem_range'_1.mpr hmid
    simp only [bodySupport,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
  · have hh : w ∈ List.range' 19814 3 := List.mem_range'_1.mpr hhi
    simp only [bodySupport,List.mem_append]
    exact Or.inl (Or.inl (Or.inr hh))

theorem used_wireBound : ∀ w ∈ streamLayout.dialogUsedWires, wireBound w := by decide +kernel

def lookupBounded {n : Nat} : WInstr n → Bool
  | .literal _ => true
  | .lookup ctl ports =>
      ctl.toList.all (fun w => decide (wireBound w)) &&
      (portTargets ports).all (fun w => decide (wireBound w))

theorem row_lookupBounded : (normalizeW (rowAddCode probeRows)).all lookupBounded = true := by
  decide +kernel

theorem lookupBounded_parts {n : Nat} (control : Option Wire) (ports : List (LookupPort n))
    (h : lookupBounded (WInstr.lookup control ports) = true) :
    (∀ q ∈ control, wireBound q) ∧ (∀ w ∈ portTargets ports, wireBound w) := by
  simpa [lookupBounded,List.all_eq_true] using h

theorem support_castFinish {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    ChallengeMigration.straightWires (NaiveChallenge.castFinish h p) = ChallengeMigration.straightWires p := by
  subst f
  rfl

theorem support_agrees {n s e : Nat} (p : Straight n s e) :
    ChallengeMigration.straightWires p = NaiveChallenge.straightWires p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp only [ChallengeMigration.straightWires,
      NaiveChallenge.straightWires,templateGateWires,NaiveChallenge.slotGate,ih]
  | recordGate r v g p ih => simp only [ChallengeMigration.straightWires,NaiveChallenge.straightWires,ih]
  | measure w p ih => simp only [ChallengeMigration.straightWires,NaiveChallenge.straightWires,ih]

theorem literal_translate_support {n : Nat} (p : ECDSAAdd.Program) (S : List Wire)
    (hp : ECDSAAdd.wires p ⊆ S.toFinset) (start : Nat) :
    ChallengeMigration.straightWires (Bridge.translate (literalT (n := n) p) start) ⊆ S := by
  rw [support_agrees]
  intro w hw
  have h := Bridge.portWires (n := n) (fun _ => false)
    (Bridge.portGated_lit (P := Bridge.PortGood S) p) (by simpa using hp)
  apply h w
  simpa only [literalT,ECDSAAdd.ShorPort.Tmpl.lit,List.map_map,Bridge.ofPort] using
    Bridge.translate_wires (literalT p) start w hw

theorem compile_support {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (S : List Wire) (hq : root ∈ S) (hb : bits ⊆ S) (hpaths : paths ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlookup : ∀ c ports, WInstr.lookup c ports ∈ code →
      (∀ q ∈ c, q ∈ S) ∧ portTargets ports ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (compile bits paths root code start) ⊆ S := by
  induction code generalizing start with
  | nil => simp [compile,ChallengeMigration.straightWires]
  | cons i code ih =>
    have ht (k : Nat) := ih
      (fun p hm => hlit p (List.mem_cons_of_mem _ hm))
      (fun c p hm => hlookup c p (List.mem_cons_of_mem _ hm)) k
    cases i with
    | literal p =>
      simp only [compile,support_castFinish,ChallengeMigration.straightWires_append]
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact literal_translate_support p S (hlit p (by simp)) start hw
      · exact ht _ hw
    | lookup c ports =>
      simp only [compile,support_castFinish,ChallengeMigration.straightWires_append]
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · have info := hlookup c ports (by simp)
        have hc : lookupRoot root c ∈ S := by cases c <;> simp_all [lookupRoot]
        have hn : w ∈ NaiveChallenge.straightWires (lookupProgram n (portOps ports bits paths (lookupRoot root c)) start) := by
          rw [← support_agrees]; exact hw
        exact portProgram_support ports bits paths _ _ S hc hb hpaths info.2 hn
      · exact ht _ hw

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000
attribute [local irreducible] compile Bridge.translate ECDSAAdd.wires

theorem literalFixed_support {n : Nat} (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n := n) p) = m) (S : List Wire)
    (hp : ECDSAAdd.wires p ⊆ S.toFinset) (start : Nat) :
    ChallengeMigration.straightWires (literalFixed p m hm start) ⊆ S := by
  rw [literalFixed,support_castFinish]
  exact literal_translate_support p S hp start

theorem compilerFixed_support {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (m : Nat) (hm : codeRecords bits paths root code = m) (S : List Wire)
    (hq : root ∈ S) (hb : bits ⊆ S) (hpaths : paths ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlookup : ∀ c ports, WInstr.lookup c ports ∈ code →
      (∀ q ∈ c, q ∈ S) ∧ portTargets ports ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (compilerFixed bits paths root code m hm start) ⊆ S := by
  rw [compilerFixed,support_castFinish]
  exact compile_support bits paths root code S hq hb hpaths hlit hlookup start

theorem rowAddProgram_support (start : Nat) : ChallengeMigration.straightWires (addProgram start) ⊆ bodySupport := by
  apply compilerFixed_support windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    2245006 rowAdd_records bodySupport (start := start)
  · simp [bodySupport]
  · intro w hw
    have hb : w ∈ completeBatchedSupport := by
      simp only [windowBits,List.mem_range'_1] at hw
      simp [completeBatchedSupport,resetWires,List.mem_range'_1]
      dsimp only [Wire] at *
      omega
    exact base_subset_support hb
  · intro w hw
    simp only [bodySupport,List.mem_append]
    exact Or.inl (Or.inr hw)
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q =>
      cases he
      rw [ECDSAAdd.Baselines.normalize_wires]
      intro w hw
      have used : w = 838 ∨ w ∈ streamLayout.dialogUsedWires := by
        simp only [rowAddCode,List.mem_append] at hj
        rcases hj with (hj | hj) | hj
        · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
          subst q
          exact Or.inl (by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw)
        · exact Or.inr (List.mem_toFinset.mp
            ((finiteOne_literal_facts streamLayout streamLayout_widths streamLayout_nodup probeRows q
              (tight_finite_literal_subset streamLayout probeRows q (finite23_literal_subset streamLayout probeRows q hj))).1 hw))
        · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
          subst q
          exact Or.inl (by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw)
      apply List.mem_toFinset.mpr
      rcases used with rfl | used
      · exact wireBound_support _ (Or.inl (by decide))
      · exact wireBound_support _ (used_wireBound w used)
    | lookup c ports => cases he
  · intro c ports hc
    have h := List.all_eq_true.mp row_lookupBounded _ hc
    have h := lookupBounded_parts c ports h
    exact ⟨fun q hq => wireBound_support q (h.1 q hq), fun w hw => wireBound_support w (h.2 w hw)⟩

theorem signedY_support (K : NegLayout) (sign flag p c : Nat)
    (hw : K.work.length = K.word.length) :
    ECDSAAdd.wires (signedYProgram K sign flag p c) ⊆ (sign :: K.wires flag).toFinset := by
  have hn := K.program_support flag p c hw
  simp only [signedYProgram,ECDSAAdd.wires_append,Finset.union_subset_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [flagPrepare,ECDSAAdd.wires,ECDSAAdd.Instr.wires,CompactRecoveryNegateLayout.wires]
  · exact hn.trans (fun w hw => List.mem_toFinset.mpr
      (List.mem_cons_of_mem sign (List.mem_toFinset.mp hw)))
  · simp [flagClear,ECDSAAdd.wires,ECDSAAdd.Instr.wires,CompactRecoveryNegateLayout.wires]

theorem nProgram_support (start : Nat) : ChallengeMigration.straightWires (nProgram start) ⊆ bodySupport := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) 1022
    ((literal_meas (n := 32768) _).trans
      ((ECDSAAdd.Baselines.normalize_measurements windowSignProgram).trans windowSign_counts.2))
    bodySupport (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := signedY_support (negateYLayout streamLayout) 870 streamLayout.core.generic
    ECDSAAdd.p SquareReduction.c (negateYLayout_widths streamLayout streamLayout_widths).2
  have cover : 870 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ bodySupport := by
    decide +kernel
  exact hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw)))

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

theorem prefixProgram_support (start : Nat) :
    ChallengeMigration.straightWires (prefixProgram start) ⊆ bodySupport := by
  rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
  decide +kernel

theorem suffixProgram_support (start : Nat) :
    ChallengeMigration.straightWires (suffixProgram start) ⊆ bodySupport := by
  rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
  decide +kernel

theorem bodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (bodyProgram start) ⊆ bodySupport := by
  rw [bodyProgram,support_castFinish]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨prefixProgram_support _,nProgram_support _⟩,rowAddProgram_support _⟩,
    nProgram_support _⟩,suffixProgram_support _⟩

end
end ShorECDLP.Entrant.WEX


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def body : Single.WindowBody where
  records := 2247050
  tBound := 19964056
  slotBound := 1100000000
  support := bodySupport
  reset := resetWires
  ready := windowReady
  active := windowReady_active
  ready_write := windowReady_write
  ready_address := windowReady_address
  ready_first := windowReady_first
  program := bodyProgram
  update := bodyState
  correct := fun coeffs Q _ _ s hs P hP => bodyState_correct coeffs Q s hs P hP
  coherent := by
    intro coeffs Q hQ hn start history
    obtain ⟨cs,aligned,mass⟩ := bodySource_coherent coeffs Q hQ hn
    refine ⟨cs,?_,mass⟩
    rw [bodyProgram_run]
    exact aligned.imp (fun _ _ hb s hs => hb s hs.1)
  wellFormed := bodyProgram_wellFormed
  slots := bodyProgram_slots_bound
  tCount := by
    intro coeffs Q start history
    rw [bodyProgram_tCount]
    exact bodyT_bound
  wires := bodyProgram_support
  reset_support := by
    intro w hw
    exact base_subset_support (List.mem_cons_of_mem 837 hw)
  skeleton_support := base_subset_support

/-! Compact WEX physical labels. The adapted public arithmetic uses a 1,602-site
native cover, plus sixteen bank ports and sixteen lookup path/root sites, for a
1,634-label body cover. The work permutation fixes point, control and bank ports.
Protected relabeling transports the full coherent body and its readiness invariant. -/

section CompactPhysicalLabels
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] compile Bridge.translate codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  ECDSAAdd.wires Arith.genericS Arith.padding ECDSAAdd.Entrant.pairEqual ECDSAAdd.Entrant.shortEqual ECDSAAdd.Arithmetic.maskedPointConstant
  ECDSAAdd.Arithmetic.pointDialogConstantAdd ECDSAAdd.Arithmetic.pointRecoveryReflection
  ECDSAAdd.Frontier.arithS ECDSAAdd.Frontier.SquareOB5.program

def oldWork (w : Nat) : Prop :=
  (10000 ≤ w ∧ w < 10016) ∨ (14111 ≤ w ∧ w < 14630) ∨
  (14832 ≤ w ∧ w < 14880) ∨ (14883 ≤ w ∧ w < 15144) ∨
  (15399 ≤ w ∧ w < 15656) ∨ (19814 ≤ w ∧ w < 19817)
instance (w : Nat) : Decidable (oldWork w) := inferInstanceAs (Decidable
  ((10000 ≤ w ∧ w < 10016) ∨ (14111 ≤ w ∧ w < 14630) ∨
  (14832 ≤ w ∧ w < 14880) ∨ (14883 ≤ w ∧ w < 15144) ∨
  (15399 ≤ w ∧ w < 15656) ∨ (19814 ≤ w ∧ w < 19817)))

def sourceSupport : List Wire := List.range' 263 256 ++ List.range' 580 257 ++ [838] ++
  List.range' 855 16 ++ List.range' 10000 16 ++ List.range' 14111 519 ++
  List.range' 14832 48 ++ List.range' 14883 261 ++ List.range' 15399 257 ++ List.range' 19814 3


def oldRank (w : Nat) : Nat := if w < 10016 then w-10000 else if w < 14630 then w-14095
  else if w < 14880 then w-14297 else if w < 15144 then w-14300
  else if w < 15656 then w-14555 else w-18713

def oldAt (i : Nat) : Nat := if i < 16 then i+10000 else if i < 535 then i+14095
  else if i < 583 then i+14297 else if i < 844 then i+14300
  else if i < 1101 then i+14555 else i+18713

def freeWork (w : Nat) : Prop := w < 263 ∨ (519 ≤ w ∧ w < 580) ∨ w = 837 ∨
  (839 ≤ w ∧ w < 855) ∨ (871 ≤ w ∧ w < 1634)
instance (w : Nat) : Decidable (freeWork w) := inferInstanceAs (Decidable
  (w < 263 ∨ (519 ≤ w ∧ w < 580) ∨ w = 837 ∨
  (839 ≤ w ∧ w < 855) ∨ (871 ≤ w ∧ w < 1634)))

def freeRank (w : Nat) : Nat := if w < 263 then w else if w < 580 then w-256
  else if w = 837 then 324 else if w < 855 then w-514 else w-530

def freeAt (i : Nat) : Nat := if i < 263 then i else if i < 324 then i+256
  else if i = 324 then 837 else if i < 341 then i+514 else i+530

theorem oldRank_lt (w : Nat) (h : oldWork w) : oldRank w < 1104 := by
  unfold oldWork oldRank at *; split_ifs <;> omega
theorem oldAt_mem (i : Nat) (h : i < 1104) : oldWork (oldAt i) := by
  unfold oldAt oldWork; split_ifs <;> omega
theorem oldAt_rank (w : Nat) (h : oldWork w) : oldAt (oldRank w) = w := by
  unfold oldWork oldRank oldAt at *; split_ifs <;> omega
theorem oldRank_at (i : Nat) (h : i < 1104) : oldRank (oldAt i) = i := by
  unfold oldRank oldAt; split_ifs <;> omega

theorem freeRank_lt (w : Nat) (h : freeWork w) : freeRank w < 1104 := by
  unfold freeWork freeRank at *; split_ifs <;> omega
theorem freeAt_mem (i : Nat) (h : i < 1104) : freeWork (freeAt i) := by
  unfold freeAt freeWork; split_ifs <;> omega
theorem freeAt_rank (w : Nat) (h : freeWork w) : freeAt (freeRank w) = w := by
  unfold freeWork freeRank freeAt at *; split_ifs <;> omega
theorem freeRank_at (i : Nat) (h : i < 1104) : freeRank (freeAt i) = i := by
  unfold freeRank freeAt; split_ifs <;> omega

theorem old_free_disjoint (w : Nat) (ho : oldWork w) : ¬ freeWork w := by
  unfold oldWork freeWork at *; omega

def compactWire (w : Nat) : Nat :=
  if oldWork w then freeAt (oldRank w) else if freeWork w then oldAt (freeRank w) else w

theorem compactWire_involutive : Function.Involutive compactWire := by
  intro w
  by_cases ho : oldWork w
  · have hf := freeAt_mem _ (oldRank_lt w ho)
    have hn : ¬oldWork (freeAt (oldRank w)) := fun h => old_free_disjoint _ h hf
    simp only [compactWire,if_pos ho,if_neg hn,if_pos hf]
    rw [freeRank_at _ (oldRank_lt w ho),oldAt_rank w ho]
  · by_cases hf : freeWork w
    · have hh := oldAt_mem _ (freeRank_lt w hf)
      simp only [compactWire,if_neg ho,if_pos hf,if_pos hh]
      rw [oldRank_at _ (freeRank_lt w hf),freeAt_rank w hf]
    · simp only [compactWire,if_neg ho,if_neg hf]

def compactPerm : Wire ≃ Wire :=
  ⟨compactWire,compactWire,compactWire_involutive,compactWire_involutive⟩

def fixedPort (w : Nat) : Prop := (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 837) ∨
  w = 838 ∨ (855 ≤ w ∧ w < 871)
instance (w : Nat) : Decidable (fixedPort w) := inferInstanceAs (Decidable
  ((263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 837) ∨ w = 838 ∨ (855 ≤ w ∧ w < 871)))

theorem compactPerm_fixed (w : Wire) (h : fixedPort w) : compactPerm w = w := by
  have ho : ¬oldWork w := by unfold oldWork fixedPort at *; omega
  have hf : ¬freeWork w := by unfold freeWork fixedPort at *; omega
  simp only [compactPerm,Equiv.coe_fn_mk,compactWire,if_neg ho,if_neg hf]

theorem sourceSupport_mem (w : Wire) : w ∈ sourceSupport ↔ fixedPort w ∨ oldWork w := by
  simp only [sourceSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1,
    fixedPort,oldWork,or_assoc]

theorem compactPerm_bound (w : Wire) (h : w ∈ sourceSupport) : compactPerm w < 1634 := by
  rcases (sourceSupport_mem w).mp h with hf | ho
  · rw [compactPerm_fixed w hf]; unfold fixedPort at hf; dsimp only [Wire] at *; omega
  · change compactWire w < 1634
    rw [compactWire,if_pos ho]
    have hh := freeAt_mem _ (oldRank_lt w ho)
    unfold freeWork at hh; omega

theorem source_of_bounds (xs : List Wire) (h : ∀ w ∈ xs, fixedPort w ∨ oldWork w) : xs ⊆ sourceSupport :=
  fun w hw => (sourceSupport_mem w).mpr (h w hw)

theorem streamPool_at (i : Nat) (hi : i < 5699) : streamLayout.core.poolWire i = i+14115 := by
  change ((List.range' 4115 5699).map streamWire).getD i 0 = i+14115
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range' hi]
  simp only [Nat.one_mul,Option.map_some,Option.getD_some]
  unfold streamWire
  split_ifs <;> omega

theorem basic_cover : streamLayout.recoveryStageSites ⊆ sourceSupport := by
  apply source_of_bounds; decide +kernel

theorem resident_cover (q : Wire)
    (h : q ∈ ECDSAAdd.Arithmetic.PointAddLayout.pointWires streamLayout.point ++
      [streamLayout.control] ++ streamLayout.inPlaceFlags) : q ∈ sourceSupport := by
  apply basic_cover
  simp only [recoveryStageSites,List.mem_append] at *
  tauto

theorem pool_cover (n : Nat) (hn : n ≤ 515) : streamLayout.dialogPool.take n ⊆ sourceSupport := by
  intro q hq
  have he : (streamLayout.dialogPool.take 515).take n = streamLayout.dialogPool.take n := by
    rw [List.take_take,Nat.min_eq_left hn]
  have hp : q ∈ streamLayout.dialogPool.take 515 := by
    rw [←he] at hq
    exact List.mem_of_mem_take hq
  exact basic_cover (List.mem_append_right _ hp)

theorem selected_source : ECDSAAdd.wires
    (ECDSAAdd.Frontier.SelGeneric5.program streamLayout 0 0) ⊆ sourceSupport.toFinset := by
  let L := streamLayout
  have hs := (ECDSAAdd.Frontier.SelGeneric5.program_sub L streamLayout_widths streamLayout_nodup 0 0).wires_sub.trans
    (ECDSAAdd.Frontier.OwnParityGeneric.program_support L streamLayout_widths streamLayout_nodup 0 0)
  have no765 := ECDSAAdd.Frontier.OwnGuardFinal.selected_free L streamLayout_widths streamLayout_nodup 0 0
  have no766 := ECDSAAdd.Frontier.OwnPlusFinal.selected_free L streamLayout_widths streamLayout_nodup 0 0
  have no767 := ECDSAAdd.Frontier.OwnMinusFinal.selected_free L streamLayout_widths streamLayout_nodup 0 0
  intro q hq
  have h := List.mem_toFinset.mp (hs hq)
  simp only [ECDSAAdd.Frontier.OwnParityPhysical.genericSites,List.mem_append,List.mem_singleton] at h
  apply List.mem_toFinset.mpr
  rcases h with (hp | hg) | hpool
  · exact resident_cover q (by simp [L,hp])
  · subst q
    exact resident_cover _ (by simp [L,inPlaceFlags])
  · obtain ⟨i,hi,rfl⟩ := ECDSAAdd.Frontier.OwnParityPhysical.pool_index L q hpool
    have h765 : i ≠ 765 := by intro he; subst i; exact no765 hq
    have h766 : i ≠ 766 := by intro he; subst i; exact no766 hq
    have h767 : i ≠ 767 := by intro he; subst i; exact no767 hq
    have hl : i < 5699 := by rcases hi with h | h | h <;> omega
    change streamLayout.core.poolWire i ∈ sourceSupport
    rw [streamPool_at i hl]
    apply (sourceSupport_mem _).mpr
    right
    unfold oldWork
    rcases hi with h | h | h <;> omega

theorem generic_source (cx cy : ECDSAAdd.Fp) :
    ECDSAAdd.wires (Arith.genericS streamLayout cx cy) ⊆ sourceSupport.toFinset := by
  let L := streamLayout
  have ar (b : Bool) := (Arith.arith_wires_selected L b).trans selected_source
  have sq := (Arith.square_wires_selected L).trans selected_source
  have ca (r : List ECDSAAdd.Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : ECDSAAdd.Fp) :
      ECDSAAdd.wires (pointDialogConstantAdd L r k) ⊆ sourceSupport.toFinset := by
    unfold ECDSAAdd.Arithmetic.pointDialogConstantAdd
    apply Finset.Subset.trans (pointRecoveryConstantAdd_support L streamLayout_widths r k)
    intro q hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with (rfl | hp) | hp
    · exact resident_cover _ (by simp [L,inPlaceFlags])
    · apply resident_cover
      rcases hr with rfl | rfl <;> simp [L,PointAddLayout.pointWires,hp]
    · exact pool_cover 515 (le_refl _) hp
  have re := (recoveryStageS_support L streamLayout_widths cx cy).trans
    (fun q hq => List.mem_toFinset.mpr (basic_cover (List.mem_toFinset.mp hq)))
  have z : ECDSAAdd.wires (ECDSAAdd.Frontier.zrep L) ⊆ sourceSupport.toFinset := by
    intro q hq
    apply List.mem_toFinset.mpr
    apply resident_cover
    rcases ECDSAAdd.Frontier.zrep_wires L q hq with rfl | hq <;>
      simp [L,PointAddLayout.pointWires,hq]
  simp only [Arith.genericS,Arith.core,ECDSAAdd.wires_append,Finset.union_subset_iff]
  exact ⟨⟨z,⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _,ca _ (Or.inr rfl) _⟩,ar false⟩,sq⟩,
    ca _ (Or.inl rfl) _⟩,ar true⟩,re⟩,z⟩


theorem padding_source : ECDSAAdd.wires (Arith.padding (streamLayout.core.poolWire 0) 51716) ⊆
    sourceSupport.toFinset := by
  apply Finset.Subset.trans (Arith.padding_support _ _)
  intro q hq
  have he : q = streamLayout.core.poolWire 0 := by simpa only [Finset.mem_singleton] using hq
  subst q
  apply List.mem_toFinset.mpr
  apply (sourceSupport_mem _).mpr
  right; decide +kernel

theorem streamFlagsPoint_source :
    streamLayout.inPlaceFlags ++ PointAddLayout.pointWires streamLayout.point ⊆ sourceSupport := by
  apply source_of_bounds
  decide +kernel

theorem singleRowCorners_source (C : ECDSAAdd.Secp256k1.Point) :
    ECDSAAdd.wires (singleRowCorners streamLayout C) ⊆ sourceSupport.toFinset := by
  let L := streamLayout
  have hw := streamLayout_widths
  have point (q : ECDSAAdd.Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sourceSupport :=
    resident_cover q (by simp [L,hq])
  have flag (q : ECDSAAdd.Wire) (hq : q ∈ L.inPlaceFlags) : q ∈ sourceSupport :=
    resident_cover q (by simp [L,hq])
  have kn := (negateYLayout L).program_support L.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths L hw).2
  have kc : (negateYLayout L).wires L.core.equalNegY ⊆ sourceSupport := by apply source_of_bounds; decide +kernel
  have km := kn.trans (fun w hw => List.mem_toFinset.mpr (kc (List.mem_toFinset.mp hw)))
  have mask (q : ECDSAAdd.Wire) (hq : q ∈ L.inPlaceFlags) (P : ECDSAAdd.Secp256k1.Point) :
      ECDSAAdd.wires (maskedPointConstant q L.point P) ⊆ sourceSupport.toFinset := by
    apply Finset.Subset.trans (maskedPointConstant_support q L.point P)
    intro w hw
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact flag _ hq
    · exact point w hw
  have cc : ECDSAAdd.wires ([.CX L.infinitySelect L.doubleSelect]) ⊆ sourceSupport.toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl <;> exact List.mem_toFinset.mpr (flag _ (by simp [inPlaceFlags]))
  have m1 := mask L.core.equalNegY (by simp [inPlaceFlags]) (C+C)
  have m2 := mask L.doubleSelect (by simp [inPlaceFlags]) C
  have m3 := mask L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have m4 := mask L.genericSelect (by simp [inPlaceFlags]) (-C)
  have m5 := mask L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  simp only [singleRowCorners,mergedInPlaceCorners,ECDSAAdd.wires_append,Finset.union_subset_iff]
  tauto

theorem secondCorners_support_of (L : ControlledPointLayout) (C : ECDSAAdd.Secp256k1.Point) (S : List Wire)
    (old : ECDSAAdd.wires (singleRowCorners L C) ⊆ S.toFinset)
    (pc : L.inPlaceFlags ⊆ S) : ECDSAAdd.wires (secondCorners L C) ⊆ S.toFinset := by
  simp only [singleRowCorners, mergedInPlaceCorners, ECDSAAdd.wires_append, Finset.union_subset_iff] at old
  have cx : ECDSAAdd.wires ([.CX L.genericSelect L.core.equalNegY]) ⊆ S.toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl <;> apply List.mem_toFinset.mpr <;>
      apply pc <;> simp [inPlaceFlags]
  simp only [secondCorners, ECDSAAdd.wires_append, Finset.union_subset_iff]
  tauto

theorem secondCorners_source (C : ECDSAAdd.Secp256k1.Point) :
    ECDSAAdd.wires (secondCorners streamLayout C) ⊆ sourceSupport.toFinset := by
  apply secondCorners_support_of streamLayout C sourceSupport (singleRowCorners_source C)
  intro q hq
  exact streamFlagsPoint_source (List.mem_append_left _ hq)

theorem finiteOneS_source (C : ECDSAAdd.Secp256k1.Point) (cx cy : ECDSAAdd.Fp) :
    ECDSAAdd.wires (finiteOneS streamLayout C cx cy) ⊆ sourceSupport.toFinset := by
  let L := streamLayout
  have hw := streamLayout_widths
  have point (q : ECDSAAdd.Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sourceSupport :=
    resident_cover q (by simp [L,hq])
  have flag (q : ECDSAAdd.Wire) (hq : q ∈ L.inPlaceFlags) : q ∈ sourceSupport :=
    resident_cover q (by simp [L,hq])
  have ctrl : L.control ∈ sourceSupport := resident_cover _ (by simp [L])
  have finite : L.point.finite ∈ sourceSupport := point _ (by simp [PointAddLayout.pointWires])
  have pair (t₁ t₂ : ECDSAAdd.Wire) (ht₁ : t₁ ∈ L.inPlaceFlags) (ht₂ : t₂ ∈ L.inPlaceFlags)
      (e₁ e₂ : Bool) (P Q : ECDSAAdd.Secp256k1.Point) :
      ECDSAAdd.wires (pairEqual L t₁ t₂ e₁ e₂ P Q) ⊆ sourceSupport.toFinset := by
    apply Finset.Subset.trans (pairEqual_wires L hw t₁ t₂ e₁ e₂ P Q)
    intro q hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | rfl | rfl | rfl | hp | hp
    · exact ctrl
    · exact point _ (by simp [PointAddLayout.pointWires,yLow_mem L hw])
    · exact flag _ ht₁
    · exact flag _ ht₂
    · exact point q (by simpa only [pairSrc,PointAddLayout.pointWires,List.mem_cons,List.mem_append] using
        (Or.inl hp : q ∈ pairSrc L ∨ q ∈ L.point.y))
    · exact pool_cover 257 (by decide) hp
  have short (c t : ECDSAAdd.Wire) (hc : c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
      (P : ECDSAAdd.Secp256k1.Point) : ECDSAAdd.wires (shortEqual L c t P) ⊆ sourceSupport.toFinset := by
    apply Finset.Subset.trans (shortEqual_wires_subset L hw c t P 0)
    rw [equalConstant_wires]
    intro q hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact flag _ hc
    · exact flag _ ht
    · have len : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
        have hx : L.point.x.length = 256 := hw.inputX
        have hy : L.point.y.length = 256 := hw.inputY
        simp [PointAddLayout.pointWires,hx,hy,dialogPool_length L hw]
      have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513) len).subset hq
      rcases List.mem_append.mp hp with hp | hp
      · exact point q hp
      · exact pool_cover 513 (by decide) hp
  have cx_source (t : ECDSAAdd.Wire) (ht : t ∈ L.inPlaceFlags) :
      ECDSAAdd.wires ([.CX L.control t]) ⊆ sourceSupport.toFinset := by
    intro q hq
    simp only [ECDSAAdd.wires,ECDSAAdd.Instr.wires,Finset.union_empty,Finset.mem_insert,Finset.mem_singleton] at hq
    apply List.mem_toFinset.mpr
    rcases hq with rfl | rfl
    · exact ctrl
    · exact flag _ ht
  have enD : ECDSAAdd.wires (pointInPlaceDoubleEnable L cy) ⊆ sourceSupport.toFinset := by
    unfold pointInPlaceDoubleEnable
    split
    · exact cx_source L.core.double (by simp [inPlaceFlags])
    · simpa only [ECDSAAdd.wires] using Finset.empty_subset sourceSupport.toFinset
  have enH : ECDSAAdd.wires (pointDialogExceptionEnable L C) ⊆ sourceSupport.toFinset := by
    unfold pointDialogExceptionEnable
    split
    · exact cx_source L.core.equalX (by simp [inPlaceFlags])
    · simpa only [ECDSAAdd.wires] using Finset.empty_subset sourceSupport.toFinset
  have zero (t : ECDSAAdd.Wire) (ht : t ∈ L.inPlaceFlags) :
      ECDSAAdd.wires (zeroFlag L.point.finite L.control t) ⊆ sourceSupport.toFinset := by
    rw [zeroFlag_wires]
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    apply List.mem_toFinset.mpr
    rcases hq with rfl | rfl | rfl
    · exact finite
    · exact ctrl
    · exact flag _ ht
  have gf : ECDSAAdd.wires (pointDialogGenericFlag L) ⊆ sourceSupport.toFinset := by
    have small : ECDSAAdd.wires (pointDialogGenericFlag L) ⊆
        (L.control :: L.point.finite :: L.inPlaceFlags).toFinset := by decide +kernel
    apply small.trans
    intro q hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact ctrl
    · exact finite
    · exact flag _ hq
  have p1 := pair L.doubleSelect L.genericSelect (by simp [inPlaceFlags]) (by simp [inPlaceFlags])
    (decide (cy ≠ -cy)) true C (-C)
  have p2 := pair L.infinitySelect L.core.equalNegY (by simp [inPlaceFlags]) (by simp [inPlaceFlags])
    true (exceptionBit C) C (-C)
  have s1 := short L.core.equalX L.core.equalNegY (by simp [inPlaceFlags]) (by simp [inPlaceFlags])
    (ECDSAAdd.Secp256k1.dialogExceptionPoint C)
  have s2 := short L.core.double L.doubleSelect (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (C+C)
  have z1 := zero L.infinitySelect (by simp [inPlaceFlags])
  have z2 := zero L.genericSelect (by simp [inPlaceFlags])
  have gen := generic_source cx cy
  have corner : ECDSAAdd.wires (secondCorners L C) ⊆ sourceSupport.toFinset :=
    secondCorners_source C

  have pad := padding_source
  change ECDSAAdd.wires (finiteOneS L C cx cy) ⊆ _
  simp only [finiteOneS,finiteOneS_base,ECDSAAdd.wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨enD,enH⟩,z1⟩,p1⟩,s1⟩,gf⟩,gen⟩,corner⟩,gf⟩,p2⟩,s2⟩,z2⟩,enH⟩,enD⟩,pad⟩


def sourceLookupOK {n : Nat} : WInstr n → Bool
  | .literal _ => true
  | .lookup ctl ports => ctl.toList.all (fun w => decide (fixedPort w ∨ oldWork w)) &&
      (portTargets ports).all (fun w => decide (fixedPort w ∨ oldWork w))
theorem row_sourceLookupOK : (normalizeW (rowAddCode probeRows)).all sourceLookupOK = true := by
  decide +kernel

open ECDSAAdd ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort

theorem finiteOne_literal_source {n : Nat} (rows : Nat → Fin n) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ wFiniteOne streamLayout rows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  let P : Point := Bridge.toB ShorECDLP.Secp256k1.G
  have hP : P ≠ 0 := ShorECDLP.Secp256k1.G_ne_zero
  cases hgen : P with
  | zero => exact (hP hgen).elim
  | @some cx cy hc =>
    let C : Point := .some hc
    let read : CBit n → Bool := fun ref => (fieldValue (toA C) ref.field).testBit ref.bit.val
    have hr : RowReads read (rows 0) C := fun _ _ => rfl
    have hk : toA C = (1 : Nat) • ShorECDLP.Secp256k1.G := by
      rw [one_nsmul]
      change toA (.some hc) = _
      rw [← hgen]
      rfl
    have en := enables_of_multiple hc 1 hk
    have structural := double_triple_ne_zero C 1 hk (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have ho : ShorECDLP.order • (C+C) = 0 := by
      change ShorECDLP.order • ((.some hc : Point)+.some hc) = 0
      rw [← hgen]
      change ShorECDLP.order • (ShorECDLP.Secp256k1.G+ShorECDLP.Secp256k1.G) = 0
      rw [nsmul_add, ShorECDLP.Secp256k1.generator_nsmul_eq_zero, zero_add]
    have inst := wFiniteOne_inst read streamLayout streamLayout_widths rows 0 hc hr en.1 en.2 structural.1 ho
    have used := finiteOneS_source C cx cy
    rw [← inst] at used
    exact (literal_wires_subset read _ 0 p hp).trans used

theorem addProgram_source (start : Nat) : ChallengeMigration.straightWires (addProgram start) ⊆ sourceSupport := by
  apply compilerFixed_support windowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    2245006 rowAdd_records sourceSupport (start := start)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q =>
      cases he
      rw [ECDSAAdd.Baselines.normalize_wires]
      simp only [rowAddCode,List.mem_append] at hj
      rcases hj with (hj | hj) | hj
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
      · exact finiteOne_literal_source probeRows q (tight_finite_literal_subset streamLayout probeRows q (finite23_literal_subset streamLayout probeRows q hj))
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
    | lookup c ports => cases he
  · intro c ports hc
    have h := List.all_eq_true.mp row_sourceLookupOK _ hc
    have h : (∀ q ∈ c, fixedPort q ∨ oldWork q) ∧
        (∀ w ∈ portTargets ports, fixedPort w ∨ oldWork w) := by
      simpa [sourceLookupOK,List.all_eq_true] using h
    exact ⟨fun q hq => (sourceSupport_mem q).mpr (h.1 q hq),
      fun w hw => (sourceSupport_mem w).mpr (h.2 w hw)⟩

theorem nProgram_source (start : Nat) : ChallengeMigration.straightWires (nProgram start) ⊆ sourceSupport := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) 1022
    ((literal_meas (n := 32768) _).trans
      ((ECDSAAdd.Baselines.normalize_measurements windowSignProgram).trans windowSign_counts.2))
    sourceSupport (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := signedY_support (negateYLayout streamLayout) 870 streamLayout.core.generic
    ECDSAAdd.p SquareReduction.c (negateYLayout_widths streamLayout streamLayout_widths).2
  have cover : 870 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ sourceSupport := by
    apply source_of_bounds; decide +kernel
  exact hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw)))

theorem bodyProgram_source (start : Nat) : ChallengeMigration.straightWires (bodyProgram start) ⊆ sourceSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (k : Nat) : ChallengeMigration.straightWires (suffixProgram k) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [bodyProgram,support_castFinish]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nProgram_source _⟩,addProgram_source _⟩,nProgram_source _⟩,hs _⟩

def compactProgram (start : Nat) : Straight 32768 start (start+2247050) :=
  relabelStraight compactPerm (bodyProgram start)

theorem compactProgram_support (start : Nat) : ChallengeMigration.straightWires (compactProgram start) ⊆ List.range 1634 := by
  rw [compactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (compactPerm_bound v (bodyProgram_source start hv))

theorem compactProgram_slots (start : Nat) :
    (compactProgram start).gateSlots = (bodyProgram start).gateSlots :=
  relabelStraight_slots compactPerm (bodyProgram start)

theorem compactProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((compactProgram start).instantiate read history).tCount =
      ((bodyProgram start).instantiate read history).tCount := by
  rw [compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]

theorem compactPerm_point (w : Wire) (h : w ∈ pointLogicalWires) : compactPerm w = w := by
  apply compactPerm_fixed
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
  unfold fixedPort; dsimp only [Wire] at *; omega

theorem compactPerm_address (w : Wire) (h : w ∈ streamAddress) : compactPerm w = w := by
  apply compactPerm_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def compactPull (s : BasisState) : BasisState := relabelBasis compactPerm.symm s

theorem compactPull_at (s : BasisState) (w : Wire) (h : fixedPort w) : compactPull s w = s w := by
  simp only [compactPull,relabelBasis,Equiv.symm_symm,compactPerm_fixed w h]

theorem compactPull_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    compactPull (pointWrite P s) = pointWrite P (compactPull s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := compactPerm_point w hw
    simp only [compactPull,relabelBasis,Equiv.symm_symm,pointWrite,he,if_pos hw]
  · have hn : compactPerm w ∉ pointLogicalWires := by
      intro hh
      have he := compactPerm_point _ hh
      have : compactPerm w = w := compactPerm.injective he
      exact hw (this ▸ hh)
    simp only [compactPull,relabelBasis,Equiv.symm_symm,pointWrite,if_neg hw,if_neg hn]

theorem compactPush_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis compactPerm (pointWrite P (compactPull s)) = pointWrite P s := by
  have h := congrArg (relabelBasis compactPerm) (compactPull_write P s)
  have hi (t : BasisState) : relabelBasis compactPerm (compactPull t) = t := by
    simpa only [compactPull,Equiv.symm_symm] using relabelBasis_symm compactPerm.symm t
  rw [hi] at h
  exact h.symm

theorem compactPull_coordinates (s : BasisState) :
    pointStateCoordinates (compactPull s) = pointStateCoordinates s := by
  have he (ws : List Wire) (hw : ∀ w ∈ ws, fixedPort w) :
      wireValues ws (compactPull s) = wireValues ws s := by
    apply List.map_congr_left
    intro w hm; exact compactPull_at s w (hw w hm)
  have hx := he (List.range' 263 256) (by
    intro w hw; exact Or.inl (List.mem_range'_1.mp hw))
  have hy := he (List.range' 580 256) (by
    intro w hw
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inl; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,compactPull_at s 838 (by decide +kernel)]

theorem compactPull_digit (s : BasisState) : windowRawDigit 0 (compactPull s) = windowRawDigit 0 s := by
  have he : wireValues (List.range' 855 15) (compactPull s) = wireValues (List.range' 855 15) s := by
    apply List.map_congr_left
    intro w hw
    apply compactPull_at
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inr; apply Or.inr; dsimp only [Wire] at *; omega
  simp only [windowRawDigit,windowAddressBits,windowBankStart,Nat.mul_zero,Nat.add_zero,he,
    compactPull_at s 870 (by decide +kernel)]

def compactReady (s : BasisState) : Prop := windowReady (compactPull s)

theorem compactReady_active (s : BasisState) (h : compactReady s) : s 836 = true := by
  simpa only [compactPull_at s 836 (by decide +kernel)] using windowReady_active (compactPull s) h

theorem compactReady_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (h : compactReady s) :
    compactReady (pointWrite P s) := by
  unfold compactReady
  rw [compactPull_write]
  exact windowReady_write P (compactPull s) h

theorem compactPull_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    compactPull (s[v ↦ b]) = (compactPull s)[v ↦ b] := by
  have hh : compactPerm.symm v = v := compactPerm_address v hv
  simp only [compactPull,relabelBasis_upd,hh]

theorem compactReady_address (s : BasisState) (h : compactReady s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : compactReady (s[v ↦ b]) := by
  unfold compactReady
  rw [compactPull_address s v hv b]
  exact windowReady_address (compactPull s) h v hv b

theorem compactPull_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (compactPull s) := by
  constructor
  · simpa only [compactPull_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (compactPerm w) = false
    apply h.2
    · intro hh
      have hfix : compactPerm 836 = 836 := compactPerm_fixed _ (by decide +kernel)
      exact hw (compactPerm.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := compactPerm_address _ hh
      have he : compactPerm w = w := compactPerm.injective hfix
      exact ha (he ▸ hh)

theorem compactReady_first (s : BasisState) (h : FirstWindowInput s) (P : ShorECDLP.Secp256k1.Point) :
    compactReady (pointWrite P s) := by
  unfold compactReady
  rw [compactPull_write]
  exact windowReady_first (compactPull s) (compactPull_first s h) P

def compactState (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  relabelBasis compactPerm (bodyState coeffs Q (compactPull s))

theorem compactState_correct (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : compactReady s) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    compactState coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold compactState
  rw [bodyState_correct coeffs Q (compactPull s) hs P ((compactPull_coordinates s).trans hP),compactPush_write]
  simp only [compactPull_at s 836 (by decide +kernel),compactPull_at s 870 (by decide +kernel),compactPull_digit]

theorem compactProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((compactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := (body.coherent coeffs Q hQ hn start history).relabel compactPerm
  have hr : CoherentlyImplementsOn
      (((bodyProgram start).instantiate (readConstant coeffs Q) history).relabel compactPerm)
      ((relabelState compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState compactPerm.symm)))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,hc,hm⟩ := h
    refine ⟨cs,hc.imp (fun _ _ hb s hs => hb s ?_),hm⟩
    exact ⟨hs.1,by obtain ⟨P,hP⟩ := hs.2; exact ⟨P,(compactPull_coordinates s).trans hP⟩⟩
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [compactProgram,relabelStraight_instantiate]
  exact he

theorem compact_base_support : completeBatchedSupport ⊆ List.range 1634 := by
  intro w hw
  simp only [completeBatchedSupport,resetWires,List.mem_cons,List.mem_append,
    List.mem_range,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  apply List.mem_range.mpr
  dsimp only [Wire] at *; omega

def compactBody : Single.WindowBody where
  records := 2247050
  tBound := 19964056
  slotBound := 1100000000
  support := List.range 1634
  reset := resetWires
  ready := compactReady
  active := compactReady_active
  ready_write := compactReady_write
  ready_address := compactReady_address
  ready_first := compactReady_first
  program := compactProgram
  update := compactState
  correct := fun coeffs Q _ _ s hs P hP => compactState_correct coeffs Q s hs P hP
  coherent := compactProgram_coherent
  wellFormed := fun start => (relabelStraight_wellFormed compactPerm (bodyProgram start)).mpr
    (bodyProgram_wellFormed start)
  slots := fun start => (compactProgram_slots start).trans_le (bodyProgram_slots_bound start)
  tCount := by
    intro coeffs Q start history
    rw [compactProgram_tCount,bodyProgram_tCount]
    exact bodyT_bound
  wires := compactProgram_support
  reset_support := fun _ hw => compact_base_support (List.mem_cons_of_mem 837 hw)
  skeleton_support := compact_base_support

end
end CompactPhysicalLabels

end
end ShorECDLP.Entrant.WEX

end

