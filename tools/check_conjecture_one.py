"""Independent kernel and axiom gate for the literal counting Conjecture 1.

The record is written only after the original target and its stronger ordinary
isomorphism equality statement both elaborate without any extra hypothesis.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from check_lean import ALLOWED, LEAN, ROOT, declarations, local_closure, run


def main():
    (ROOT / "verification/lean-logs").mkdir(parents=True, exist_ok=True)
    sources = local_closure("Wormald.ConjectureOneProof")
    decls = [item for source in sources for item in declarations(source)]
    names = [name for _, name in decls]
    if len(names) != len(set(names)):
        raise AssertionError("Duplicate exported declaration")
    audit = LEAN / "ConjectureOneAudit.lean"
    audit.write_text(
        "import Wormald.ConjectureOneProof\n\n"
        "example : Wormald.FiniteModel.conjectureOne := "
        "Wormald.FiniteModel.conjectureOne_proof\n\n"
        "example : Wormald.FiniteModel.uniqueClassConjectureOne := "
        "Wormald.FiniteModel.uniqueClassConjectureOne_proof\n\n"
        "example : Wormald.FiniteModel.RegularCycleAsymptotics := "
        "Wormald.FiniteModel.regularCycleAsymptotics\n\n"
        + "\n".join("#print axioms " + name for name in names) + "\n",
        encoding="utf-8",
    )
    version = run("conjecture-one-version", ["env", "lean", "--version"]).strip()
    build = run("conjecture-one-build", ["build", "Wormald.ConjectureOneProof"])
    axioms = run("conjecture-one-axioms", ["env", "lean", str(audit)])
    for name in names:
        if "'" + name + "'" not in axioms:
            raise AssertionError(("Missing axiom report", name))
    used = set()
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axioms, re.S):
        used.update(item.strip() for item in block.split(",") if item.strip())
    if not used <= ALLOWED:
        raise AssertionError(("Unexpected axioms", sorted(used - ALLOWED)))
    if "sorryAx" in axioms or re.search(r"\b(?:warning|error):", build + axioms):
        raise AssertionError("Lean emitted a proof warning/error")
    tracked = [*sources, audit, LEAN / "lean-toolchain", LEAN / "lakefile.toml",
               LEAN / "lake-manifest.json", Path(__file__), ROOT / "tools/check_lean.py"]
    record = {
        "result": "passed",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version,
        "entry_module": "Wormald.ConjectureOneProof",
        "verified_target": "Wormald.FiniteModel.conjectureOne",
        "verified_strengthening": "Wormald.FiniteModel.uniqueClassConjectureOne",
        "scope": "The original independent internal-block sample space and actual "
                 "Hamilton-cycle expectations; fixed odd base order followed by all "
                 "sufficiently large block orders; unique ordinary isomorphism class "
                 "of the actual carousel. All counting limits, nonregular decay, "
                 "spectral comparison and equality classification are proved.",
        "unproved_analytic_or_counting_hypotheses": False,
        "source_module_count": len(sources),
        "exported_theorem_count": sum(kind == "theorem" for kind, _ in decls),
        "exported_declaration_count": len(decls),
        "axioms_used": sorted(used),
        "custom_axioms_or_placeholders": False,
        "source_sha256": {
            str(path.relative_to(ROOT)).replace("\\", "/"):
                hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked
        },
    }
    (ROOT / "verification/conjecture-one-verification.json").write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: record[key] for key in
        ("result", "verified_target", "verified_strengthening", "source_module_count",
         "exported_theorem_count", "axioms_used")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
