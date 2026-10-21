"""Build and audit the complete dependency closure of the literal Conjecture 6.

This gate audits only Conjecture 6, independently of the counting-conjecture
development. The global coverage flags are maintained by check_lean.py.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from check_lean import ALLOWED, LEAN, ROOT, declarations, local_closure, run


def main():
    logdir = ROOT / "verification" / "lean-logs"
    logdir.mkdir(parents=True, exist_ok=True)
    sources = local_closure("Wormald.ConjectureSixProof")
    decls = [declaration for source in sources for declaration in declarations(source)]
    names = [name for _, name in decls]
    if len(names) != len(set(names)):
        raise AssertionError("Duplicate exported declaration")
    audit = LEAN / "ConjectureSixAudit.lean"
    audit.write_text(
        "import Wormald.ConjectureSixProof\n\n"
        "example : Wormald.ConjectureSix := Wormald.conjectureSix\n\n"
        "#check Wormald.originalAngularHessian_positive_rational_root\n\n"
        + "\n".join("#print axioms " + name for name in names) + "\n",
        encoding="utf-8",
    )
    version = run("conjecture-six-version", ["env", "lean", "--version"]).strip()
    build = run("conjecture-six-build", ["build", "Wormald.ConjectureSixProof"])
    axioms = run("conjecture-six-axioms", ["env", "lean", str(audit)])
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
        "entry_module": "Wormald.ConjectureSixProof",
        "verified_target": "Wormald.conjectureSix : Wormald.ConjectureSix",
        "scope": "Original determinant, explicit eliminated h, principal complex log, "
                 "actual real angular second Frechet derivatives, all regular tournaments; "
                 "nonzero Hessian determinant and a positive rational spectral square root.",
        "unproved_analytic_or_counting_hypotheses": False,
        "source_module_count": len(sources),
        "exported_theorem_count": sum(kind == "theorem" for kind, _ in decls),
        "exported_declaration_count": len(decls),
        "axioms_used": sorted(used),
        "custom_axioms_or_placeholders": False,
        "verified_conjectures": ["6"],
        "source_sha256": {
            str(path.relative_to(ROOT)).replace("\\", "/"):
                hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked
        },
    }
    target = ROOT / "verification/conjecture-six-verification.json"
    target.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: record[key] for key in
        ("result", "verified_target", "source_module_count", "exported_theorem_count",
         "axioms_used", "verified_conjectures")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
