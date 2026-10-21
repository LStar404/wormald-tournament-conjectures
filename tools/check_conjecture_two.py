"""Independent kernel and axiom gate for the original regular-model double limit.

Besides the named target, a literal statement expands both odd-order indices
and the original regular Hamilton-cycle expectation and normalization.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from check_lean import ALLOWED, LEAN, ROOT, declarations, local_closure, run


def main():
    (ROOT / "verification/lean-logs").mkdir(parents=True, exist_ok=True)
    sources = local_closure("Wormald.ConjectureTwoProof")
    decls = [item for source in sources for item in declarations(source)]
    names = [name for _, name in decls]
    if len(names) != len(set(names)):
        raise AssertionError("Duplicate exported declaration")
    audit = LEAN / "ConjectureTwoAudit.lean"
    literal = """import Wormald.ConjectureTwoProof

open Filter Topology

example : Wormald.FiniteModel.conjectureTwo :=
  Wormald.FiniteModel.conjectureTwo_proof

example : Wormald.FiniteModel.conjectureTwoWithModelLimits :=
  Wormald.FiniteModel.conjectureTwoWithModelLimits_proof

example : Wormald.FiniteModel.UniformRegularTorusMainTerm :=
  Wormald.FiniteModel.uniformRegularTorusMainTerm

example : ∃ r : ℕ → ℝ,
    (∀ j : ℕ, Tendsto (fun k : ℕ =>
      (Wormald.FiniteModel.expectedRegularCycles
        (Wormald.FiniteModel.carousel (2 * j + 3)) (2 * k + 1)
        ((Wormald.FiniteModel.legalRegularOrder_iff (2 * j + 3) (2 * k + 1)).mpr
          ⟨k, rfl⟩) : ℝ) /
        Wormald.FiniteModel.cycleNormalizer ((2 * j + 3) * (2 * k + 1)))
      atTop (𝓝 (r j))) ∧
    Tendsto r atTop (𝓝 (Real.cosh 1 / Real.cos 1)) := by
  obtain ⟨r, hinner, houter⟩ := Wormald.FiniteModel.conjectureTwo_proof
  refine ⟨r, ?_, houter⟩
  intro j
  change Tendsto (Wormald.FiniteModel.regularCarouselNormalized (2 * j + 3)) atTop (𝓝 (r j))
  exact hinner j

"""
    audit.write_text(literal + "\n".join("#print axioms " + name for name in names) + "\n",
                     encoding="utf-8")
    version = run("conjecture-two-version", ["env", "lean", "--version"]).strip()
    build = run("conjecture-two-build", ["build", "Wormald.ConjectureTwoProof"])
    axioms = run("conjecture-two-axioms", ["env", "lean", str(audit)])
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
        "entry_module": "Wormald.ConjectureTwoProof",
        "verified_target": "Wormald.FiniteModel.conjectureTwo",
        "verified_strengthening": "Wormald.FiniteModel.conjectureTwoWithModelLimits",
        "scope": "The actual uniform regular internal-block Hamilton-cycle expectation, "
                 "normalized by (N-1)!/2^N; inner odd block orders m=2*k+1 at every "
                 "fixed odd carousel order d=2*j+3, then outer odd base orders; "
                 "exact outer value cosh(1)/cos(1). The literal expectation statement "
                 "and the genuine uniform regular-containment integral estimate "
                 "are both checked without analytic or counting premises.",
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
    (ROOT / "verification/conjecture-two-verification.json").write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: record[key] for key in
        ("result", "verified_target", "source_module_count", "exported_theorem_count",
         "axioms_used")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
