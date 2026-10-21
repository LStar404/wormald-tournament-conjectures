"""Build the Lean extension and audit every imported local declaration.

This checks proof dependencies, not whether an unproved target has a proof.
Unimported work-in-progress modules are named explicitly in the report.
Literal conjecture proofs are checked when their final modules are imported.
Python 3.10+; no third-party Python packages are required.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
RECORD = ROOT / "verification" / "lean-verification.json"
LOGDIR = ROOT / "verification" / "lean-logs"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def without_comments_and_strings(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = len(text)
            out.extend(" " * (j - i))
            i = j
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.extend("  ")
                    i += 2
                elif text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise AssertionError("Unclosed Lean comment")
    return "".join(out)


def declarations(path):
    code = without_comments_and_strings(path.read_text(encoding="utf-8-sig"))
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)
    if forbidden:
        raise AssertionError((str(path), forbidden))
    scopes, result = [], []
    for line in code.splitlines():
        s = line.strip()
        s = re.sub(r"^(?:@\[[^\]]*\]\s*)+", "", s)
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            scopes.append(("namespace", m.group(1)))
            continue
        if re.match(r"(?:noncomputable\s+)?section(?:\s|$)", s):
            scopes.append(("section", ""))
            continue
        if re.match(r"end(?:\s|$)", s):
            scopes.pop()
            continue
        if re.match(r"private\s+", s):
            continue
        m = re.match(r"(?:(?:noncomputable|protected)\s+)*(theorem|def|abbrev)\s+(\S+)", s)
        if m:
            name = m.group(2).split("{")[0].split("(")[0]
            prefix = ".".join(v for kind, v in scopes if kind == "namespace")
            result.append((m.group(1), prefix + "." + name))
    if scopes:
        raise AssertionError((str(path), "Unclosed namespace/section"))
    return result


def lake(args):
    if os.name == "nt":
        shell = shutil.which("pwsh") or shutil.which("powershell")
        if not shell:
            raise RuntimeError("PowerShell is required for the Windows toolchain wrapper")
        return [shell, "-NoProfile", "-File", str(LEAN / "run-lean.ps1"), *args]
    return ["lake", *args]


def local_closure(module):
    result = {}

    def visit(name):
        path = LEAN / (name.replace(".", "/") + ".lean")
        if name in result:
            return
        if not path.is_file():
            raise AssertionError(("Missing local module", name))
        result[name] = path
        for dependency in re.findall(r"^import\s+(Wormald(?:\.[\w]+)*)\s*$",
                                     path.read_text(encoding="utf-8-sig"), re.M):
            visit(dependency)

    visit(module)
    return sorted(result.values())


def run(label, args):
    p = subprocess.run(lake(args), cwd=LEAN, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    output = p.stdout + p.stderr
    (LOGDIR / (label + ".txt")).write_text(output, encoding="utf-8")
    if p.returncode:
        raise RuntimeError(f"{label} failed with exit {p.returncode}; see verification/lean-logs")
    return output


def main():
    LOGDIR.mkdir(parents=True, exist_ok=True)
    sources = [path for path in local_closure("Wormald") if path != LEAN / "Wormald.lean"]
    pending = sorted(set((LEAN / "Wormald").glob("*.lean")) - set(sources))
    decls = [item for p in sources for item in declarations(p)]
    has_conjecture_one = any(p.stem == "ConjectureOneProof" for p in sources)
    has_conjecture_two = any(p.stem == "ConjectureTwoProof" for p in sources)
    names = [name for _, name in decls]
    if len(names) != len(set(names)):
        raise AssertionError("Duplicate exported declaration")
    audit = ("import Wormald\n\n"
             "example : Wormald.ConjectureSix := Wormald.conjectureSix\n\n"
             + ("example : Wormald.FiniteModel.conjectureOne := "
                "Wormald.FiniteModel.conjectureOne_proof\n\n"
                "example : Wormald.FiniteModel.uniqueClassConjectureOne := "
                "Wormald.FiniteModel.uniqueClassConjectureOne_proof\n\n"
                if has_conjecture_one else "")
             + ("example : Wormald.FiniteModel.conjectureTwo := "
                "Wormald.FiniteModel.conjectureTwo_proof\n\n"
                "example : Wormald.FiniteModel.conjectureTwoWithModelLimits := "
                "Wormald.FiniteModel.conjectureTwoWithModelLimits_proof\n\n"
                if has_conjecture_two else "")
             + "\n".join("#print axioms " + n for n in names) + "\n")
    (LEAN / "AxiomAudit.lean").write_text(audit, encoding="utf-8")
    version = run("version", ["env", "lean", "--version"]).strip()
    build = run("build", ["build"])
    axioms = run("axioms", ["env", "lean", "AxiomAudit.lean"])
    for name in names:
        if "'" + name + "'" not in axioms:
            raise AssertionError(("Missing axiom report", name))
    used = set()
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axioms, re.S):
        used.update(s.strip() for s in block.split(",") if s.strip())
    if not used <= ALLOWED:
        raise AssertionError(("Unexpected axiom dependencies", sorted(used - ALLOWED)))
    if "sorryAx" in axioms or re.search(r"\b(?:warning|error):", build + axioms):
        raise AssertionError("Lean emitted a proof warning/error")
    tracked = [*sources, LEAN / "Wormald.lean", LEAN / "AxiomAudit.lean",
               LEAN / "lean-toolchain", LEAN / "lakefile.toml", LEAN / "lake-manifest.json"]
    record = {
        "result": "passed",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version,
        "source_module_count": len(sources),
        "exported_declaration_count": len(decls),
        "exported_theorem_count": sum(kind == "theorem" for kind, _ in decls),
        "axioms_used": sorted(used),
        "custom_axioms_or_placeholders": False,
        "end_to_end_conjectures": {"1": has_conjecture_one, "2": has_conjecture_two, "6": True},
        "scope": "Every exported declaration in the local dependency closure of Wormald.lean. "
                 "Complete literal Conjecture 6; general carousel determinant and closed-form "
                 "limit; actual random-model definitions and finite comparison/counting lemmas. "
                 + ("The literal Conjecture 1 and its unique ordinary isomorphism class "
                    "strengthening are proved for all base tournaments. " if has_conjecture_one
                    else "Conjecture 1 has its finite spectral extremum and isomorphism "
                    "classification proved but still needs regular-base counting asymptotics. ")
                 + ("Conjecture 2 is proved for the actual regular-block expectation, "
                    "with both odd-order limits and the exact outer constant. "
                    if has_conjecture_two else
                    "Conjecture 2 still requires regular-block counting asymptotics."),
        "unimported_work_in_progress": [str(p.relative_to(ROOT)).replace(os.sep, "/")
                                       for p in pending],
        "source_sha256": {str(p.relative_to(ROOT)).replace(os.sep, "/"):
                          hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked},
    }
    RECORD.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: record[k] for k in
        ("result", "source_module_count", "exported_theorem_count", "axioms_used",
         "end_to_end_conjectures")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
