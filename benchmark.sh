#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

score_path="scripts/score.json"
rm -f "${score_path}" "${score_path}.tmp"

if ! command -v lake >/dev/null 2>&1; then
  echo "benchmark.sh: lake not found; run ./setup.sh first" >&2
  exit 1
fi

if [[ ! -f .lake/trusted-oleans.sha256 ]]; then
  echo "benchmark.sh: missing .lake/trusted-oleans.sha256; run ./setup.sh first" >&2
  exit 1
fi

# 1. Source-hygiene check on editablePaths (ShorECDLP/Submission/Entrant) + prune orphaned build artifacts.
python3 - <<'PY'
import os
import re
import sys
from pathlib import Path

editable = Path("ShorECDLP/Submission/Entrant")
if not editable.is_dir() or editable.is_symlink():
    print("Editable root ShorECDLP/Submission/Entrant must be a regular directory", file=sys.stderr)
    sys.exit(1)

for dirpath, dirnames, filenames in os.walk(editable, followlinks=False):
    for name in [*dirnames, *filenames]:
        p = Path(dirpath) / name
        if p.is_symlink():
            print(f"Symlinks are forbidden in editablePaths: {p}", file=sys.stderr)
            sys.exit(1)


def strip_comments(source: str) -> str:
    """Remove nested block and line comments while retaining newlines and token gaps."""
    out = []
    i = depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)


FORBIDDEN = [
    r"@\[extern\b",
    r"@\[implemented_by\b",
    r"@\[csimp\b",
    r"@\[never_extract\b",
    r"\bunsafe\b",
    r"\bpartial\b",
    r"\bopaque\b",
    r"\baxiom\b",
    r"\bsorry\b",
    r"\badmit\b",
    r"\binitialize\b",
    r"\bbuiltin_initialize\b",
    r"\bIO\.Process\b",
    r"\bIO\.FS\b",
    r"\bSystem\.FilePath\b",
    r"\brun_tac\b",
    r"\brun_cmd\b",
    r"\bby_elab\b",
    r"#eval\b",
    r"\belab\b",
    r"\belab_rules\b",
    r"\bmacro\b",
    r"\bmacro_rules\b",
    r"\bsyntax\b",
    r"\bscoped\s+notation\b",
]

for p in sorted(editable.rglob("*.lean")):
    text = p.read_text(encoding="utf-8")
    clean = strip_comments(text)
    for pat in FORBIDDEN:
        m = re.search(pat, clean)
        if m:
            print(f"Forbidden token {m.group(0)!r} in {p}", file=sys.stderr)
            sys.exit(1)

# Delete all build outputs under ShorECDLP/Submission/Entrant so the submission is
# compiled from scratch on every run rather than relying on Lake staleness checks.
for sub_dir in (
    Path(".lake/build/lib/lean/ShorECDLP/Submission/Entrant"),
    Path(".lake/build/ir/ShorECDLP/Submission/Entrant"),
):
    if sub_dir.exists():
        import shutil
        shutil.rmtree(sub_dir)
PY

# 2. Enforce source policy and import layering across Math/Framework/Challenge/Judge/Submission.
python3 scripts/challenge/gate.py --root "$PWD" --source-only
python3 scripts/check-source.py

# 3. Snapshot .lake/trusted-oleans.sha256, judge.lean, Official.lean, Judge/Main.lean,
#    and all non-editable tracked files before build.
trusted_snapshot="$(mktemp)"
judge_snapshot="$(mktemp)"
official_snapshot="$(mktemp)"
judge_main_snapshot="$(mktemp)"
repo_snapshot="$(mktemp)"
judge_log="$(mktemp)"
overlay="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/shorecdlp-entrant.XXXXXX")"
trusted_lib="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/shorecdlp-trusted-lib.XXXXXX")"
cleanup() {
  chmod -R u+w "${overlay}" "${trusted_lib}" 2>/dev/null || true
  rm -rf "${trusted_snapshot}" "${judge_snapshot}" "${official_snapshot}" \
    "${judge_main_snapshot}" "${repo_snapshot}" "${judge_log}" "${overlay}" "${trusted_lib}"
}
trap cleanup EXIT

cp .lake/trusted-oleans.sha256 "${trusted_snapshot}"
cp scripts/challenge/judge.lean "${judge_snapshot}"
cp ShorECDLP/Challenge/Official.lean "${official_snapshot}"
cp ShorECDLP/Judge/Main.lean "${judge_main_snapshot}"

python3 - "${repo_snapshot}" <<'PY'
import hashlib
import subprocess
import sys
from pathlib import Path

out = Path(sys.argv[1])
files = subprocess.check_output(["git", "ls-files", "-z"]).split(b"\0")
entries = []
for raw in files:
    if not raw:
        continue
    rel = raw.decode("utf-8")
    if rel == "ShorECDLP/Submission/Entrant" or rel.startswith("ShorECDLP/Submission/Entrant/"):
        continue
    p = Path(rel)
    if p.is_file():
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(f"{h}  {rel}")
out.write_text("\n".join(entries) + "\n", encoding="utf-8")
PY

# 4. Build the protected challenge/judge targets and the entrant target with warnings as errors.
lake --wfail build \
  ShorECDLP.Challenge.Official \
  ShorECDLP.Judge.Main \
  ShorECDLP.Submission.Entrant.Main

# 5. Verify protected .olean integrity and non-editable tracked files against pre-build snapshots.
cmp -s scripts/challenge/judge.lean "${judge_snapshot}" || {
  echo "Protected file modified: scripts/challenge/judge.lean" >&2
  exit 1
}
cmp -s ShorECDLP/Challenge/Official.lean "${official_snapshot}" || {
  echo "Protected file modified: ShorECDLP/Challenge/Official.lean" >&2
  exit 1
}
cmp -s ShorECDLP/Judge/Main.lean "${judge_main_snapshot}" || {
  echo "Protected file modified: ShorECDLP/Judge/Main.lean" >&2
  exit 1
}

python3 - "${trusted_snapshot}" "${repo_snapshot}" <<'PY'
import hashlib
import sys
from pathlib import Path

for snap_arg, label in [(sys.argv[1], "Protected artifact"), (sys.argv[2], "Protected source")]:
    manifest = Path(snap_arg)
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, relpath = line.split("  ", 1)
        p = Path(relpath)
        if not p.is_file():
            print(f"{label} missing: {relpath}", file=sys.stderr)
            sys.exit(1)
        actual = hashlib.sha256(p.read_bytes()).hexdigest()
        if actual != expected:
            print(f"{label} modified: {relpath}", file=sys.stderr)
            sys.exit(1)
PY

# 6. Stage the entrant overlay into a temp dir.
#    Copy the verified "$PWD/.lake/build/lib/lean" tree to "$trusted_lib" outside "$PWD"
#    so scripts/challenge/stage-entrant.py can enforce its outside-candidate invariant.
cp -R "$PWD/.lake/build/lib/lean/." "${trusted_lib}/"
rm -rf "${trusted_lib}/ShorECDLP/Submission/Entrant"
python3 scripts/challenge/stage-entrant.py \
  --candidate "$PWD" \
  --overlay "$overlay" \
  --trusted-lib "${trusted_lib}"

# 7. Replay ShorECDLP.Challenge, ShorECDLP.Judge, and ShorECDLP.Submission.Entrant using gate.py.
export SHORECDLP_ROOT="$PWD"
unset LEAN_PATH LEAN_SRC_PATH
python3 scripts/challenge/gate.py --root "$PWD" --replay ShorECDLP.Challenge --artifact-path "$overlay"
python3 scripts/challenge/gate.py --root "$PWD" --replay ShorECDLP.Judge --artifact-path "$overlay"
python3 scripts/challenge/gate.py --root "$PWD" --replay ShorECDLP.Submission.Entrant --artifact-path "$overlay"

# 8. Run upstream's Expr-level kernel judge against the sealed entrant overlay.
lake env lean --run scripts/challenge/judge.lean "$overlay" > "${judge_log}" 2>&1 || {
  cat "${judge_log}" >&2
  exit 1
}
cat "${judge_log}"

# 9. Compute Option 1 spacetime score (score = qubits * score_tModel) and write scripts/score.json.
python3 - "${judge_log}" "${score_path}" <<'PY'
import json
import os
import sys
from pathlib import Path

log_lines = [
    line.strip()
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
    if line.strip().startswith("{") and line.strip().endswith("}")
]
if len(log_lines) != 1:
    print(f"Expected exactly one JSON report line from judge.lean, got {len(log_lines)}", file=sys.stderr)
    sys.exit(1)

report = json.loads(log_lines[0])
if report.get("accepted") is not True:
    print(f"Judge did not accept submission: {report}", file=sys.stderr)
    sys.exit(1)

t = int(report["score_tModel"])
qubits = int(report["qubits"])
measurements = int(report["measurements"])
toffoli = int(report["toffoli_derived_upper_bound"])
non_clifford = int(report["nonClifford_derived_upper_bound"])
slots = int(report["gateSlots_limit"])
rows = int(report["coefficientRows_limit"])
candidates = int(report["candidateChecks_limit"])

if t <= 0 or qubits <= 0:
    print(f"Invalid non-positive resource bounds: tModel={t}, qubits={qubits}", file=sys.stderr)
    sys.exit(1)

score = qubits * t
score_path = Path(sys.argv[2])
# benchmark.json opts into exactScores: the product exceeds 2^53, so Yukon ranks on the
# canonical decimal string scoreExact and requires score == Number(scoreExact).
payload = {
    "score": float(score),
    "scoreExact": str(score),
    "metrics": {
        "tCount": t,
        "tModel": t,
        "qubits": qubits,
        "toffoli": toffoli,
        "nonClifford": non_clifford,
        "measurements": measurements,
        "gateSlotsLimit": slots,
        "coefficientRowsLimit": rows,
        "candidateChecksLimit": candidates,
        "axioms": ["Classical.choice", "Quot.sound", "propext"],
    },
}
score_path.parent.mkdir(parents=True, exist_ok=True)
tmp_path = score_path.with_suffix(".json.tmp")
tmp_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
os.replace(tmp_path, score_path)
print(
    f"Verified score={score} "
    f"(qubits={qubits}, tModel={t}, toffoli={toffoli}, nonClifford={non_clifford}, measurements={measurements})"
)
PY
