#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/464c9d28395000a2a0128e07081e4956d50eced2/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
elan toolchain install "${toolchain}"

# Fetch Mathlib's prebuilt oleans unless the checkout already holds a build for exactly the
# pinned revision and toolchain. A cache restored via restore-keys can carry Mathlib for an
# older revision: Lake re-checks out the pinned revision by itself, but without `cache get`
# it would then rebuild Mathlib from source.
mathlib_dir=.lake/packages/mathlib
mathlib_rev="$(python3 -c 'import json; print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"] == "mathlib"))')"
if [[ ! -d "${mathlib_dir}/.lake/build" || ! -d "${mathlib_dir}/.git" ]] \
  || [[ "$(git -C "${mathlib_dir}" rev-parse HEAD 2>/dev/null)" != "${mathlib_rev}" ]] \
  || [[ "$(tr -d '[:space:]' < "${mathlib_dir}/lean-toolchain" 2>/dev/null)" != "${toolchain}" ]]; then
  lake exe cache get
fi

# Prebuild the protected mathematical, quantum framework, challenge, judge, and baseline targets.
# Never compile Submission/Entrant here; remove any stale entrant build outputs
# so the shared cache holds only trusted artifacts.
rm -rf .lake/build/lib/lean/ShorECDLP/Submission/Entrant .lake/build/ir/ShorECDLP/Submission/Entrant
# Mirror upstream CI: these independent heavy proof modules can exceed runner
# memory when cold-built together, so build them one at a time first.
for heavy in \
  'ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse' \
  'ShorECDLP.Submission.«2607_13816».EEA.EndIteration' \
  'ShorECDLP.Submission.«2607_13816».EEA.IndexedStep' \
  'ShorECDLP.Submission.«2607_13816».EEA.SchedulePrimitiveCounts' \
  'ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCompare' \
  'ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd'; do
  lake --wfail build "${heavy}"
done
lake --wfail build \
  ShorECDLP.Framework.InstructionSet \
  ShorECDLP.Framework.CostModel \
  ShorECDLP.Framework.BasisState \
  ShorECDLP.Framework.Classical.Semantics \
  ShorECDLP.Framework.Quantum.Adaptive \
  ShorECDLP.Framework.Quantum.CoherentRefinement \
  ShorECDLP.Framework.Quantum.MeasurementUncompute \
  ShorECDLP.Framework.Quantum.Measurement \
  ShorECDLP.Framework.Repetition \
  ShorECDLP.Math.All \
  ShorECDLP.Challenge.Official \
  ShorECDLP.Challenge.ExtendedContract \
  ShorECDLP.Challenge.PointFields \
  'ShorECDLP.Submission.«2607_13816».Challenge.CertificateAssembly' \
  'ShorECDLP.Submission.«2607_13816».Challenge.ExceptionalFields' \
  'ShorECDLP.Submission.«2607_13816».Challenge.FixedNetwork' \
  'ShorECDLP.Submission.«2607_13816».Challenge.EndpointLoad' \
  'ShorECDLP.Submission.«2607_13816».Challenge.MatchingPhysical' \
  'ShorECDLP.Submission.«2607_13816».Challenge.EndpointEncoding' \
  'ShorECDLP.Submission.«2607_13816».Challenge.EndpointQROM' \
  'ShorECDLP.Submission.«2607_13816».Challenge.EndpointSandwich' \
  'ShorECDLP.Submission.«2607_13816».Challenge.EndpointCoherent' \
  'ShorECDLP.Submission.«2607_13816».Challenge.Outer' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchedEndpoint' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchState' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement' \
  'ShorECDLP.Submission.«2607_13816».Challenge.CursorShift' \
  'ShorECDLP.Submission.«2607_13816».Challenge.WindowBody' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchQuery' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchCoherent' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchFrame' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchPhysical' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchCost' \
  'ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch' \
  'ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical' \
  'ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate' \
  'ShorECDLP.Submission.«2607_13816».Challenge.CoordinateConjugacy' \
  'ShorECDLP.Submission.«2607_13816».Challenge.AccumulatorEncoding' \
  'ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation' \
  'ShorECDLP.Submission.«2607_13816».Challenge.OuterResources' \
  ShorECDLP.Judge.Main \
  ShorECDLP.Submission.Naive.Challenge.NumericCertificate \
  ShorECDLP.Submission.Naive.Challenge.ExtendedCertificate
rm -rf .lake/build/lib/lean/ShorECDLP/Submission/Entrant .lake/build/ir/ShorECDLP/Submission/Entrant

# A cache restored via restore-keys can hold build outputs for modules that were since removed
# from source. Lake never deletes them, and leanchecker replays every olean under a prefix, so
# prune them to make the trusted tree and the manifest below identical to a cold build.
python3 - <<'PY'
from pathlib import Path

for build_root in (Path(".lake/build/lib/lean"), Path(".lake/build/ir")):
    tree = build_root / "ShorECDLP"
    if not tree.is_dir():
        continue
    for p in sorted(tree.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(build_root)
        source = rel.parent / (rel.name.split(".", 1)[0] + ".lean")
        if not source.is_file():
            p.unlink()
            print(f"Pruned orphaned build artifact: {p}")
PY

# Record the SHA-256 digest of all protected .olean artifacts so benchmark.sh
# can verify that building untrusted submission modules did not alter them.
python3 - <<'PY'
import hashlib
from pathlib import Path

build_lib = Path(".lake/build/lib/lean/ShorECDLP")
protected_dirs = [
    "Framework",
    "Math",
    "Challenge",
    "Judge",
    "Submission/Naive",
    "Submission/2607_13816",
]
entries = []
for sub in protected_dirs:
    d = build_lib / sub
    if not d.exists():
        continue
    for p in sorted(d.rglob("*.olean")):
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(f"{h}  {p.as_posix()}")

manifest = Path(".lake/trusted-oleans.sha256")
manifest.parent.mkdir(parents=True, exist_ok=True)
manifest.write_text("\n".join(entries) + "\n", encoding="utf-8")
print(f"Recorded {len(entries)} protected .olean digests in {manifest}")
PY
