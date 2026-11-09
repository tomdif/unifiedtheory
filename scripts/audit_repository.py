#!/usr/bin/env python3
"""Audit repository sources without executing experiments or rewriting evidence.

--build asks Lake to check every library module, including modules omitted by
UnifiedTheory.lean. Historical numerical results are not rerun by this command.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]


def repository_files() -> list[Path]:
    raw = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT
    )
    return sorted({ROOT / p for p in raw.decode().split("\0") if p and (ROOT / p).is_file()})


def lean_code(source: str) -> str:
    """Mask nested comments and strings, preserving offsets and line numbers."""
    result = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i + 2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                result[i:i + 2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": result[i] = " "
                i += 1
        elif quoted:
            if source[i] == "\\" and i + 1 < len(source):
                result[i:i + 2] = "  "; i += 2
            else:
                quoted = source[i] != '"'
                if source[i] != "\n": result[i] = " "
                i += 1
        elif source.startswith("/-", i):
            result[i:i + 2] = "  "; depth = 1; i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1: end = len(source)
            result[i:end] = " " * (end - i); i = end
        elif source[i] == '"':
            result[i] = " "; quoted = True; i += 1
        else:
            i += 1
    return "".join(result)


def module_name(path: Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def local_links(path: Path, text: str) -> list[str]:
    # Math/code examples contain expressions such as [f](x), not Markdown links.
    text = re.sub(r"```.*?```|`[^`\n]*`|\$\$.*?\$\$|\$[^$\n]+\$", "", text, flags=re.S)
    links = re.findall(r"\[[^\]\n]+\]\(([^\s)]+)(?:\s+\"[^\"\n]*\")?\)", text)
    broken = []
    for link in links:
        target = unquote(link.strip("<>").split("#", 1)[0])
        if not target or re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", target):
            continue
        # Restrict to file-looking destinations, avoiding bare mathematical terms.
        if "/" not in target and not Path(target).suffix:
            continue
        if not (path.parent / target).exists():
            broken.append(link)
    return broken


def audit() -> dict:
    files = repository_files()
    library = [p for p in files if p.suffix == ".lean" and
               (p == ROOT / "UnifiedTheory.lean" or p.is_relative_to(ROOT / "UnifiedTheory"))]
    library_set = set(library)
    imports, forbidden, errors, broken, native_sites = {}, [], [], [], []
    counts = Counter()
    for path in files:
        rel = str(path.relative_to(ROOT))
        if path.suffix not in {".lean", ".py", ".json", ".md"}: continue
        text = path.read_text()
        counts[path.suffix] += 1
        try:
            if path.suffix == ".py":
                compile(text, rel, "exec", ast.PyCF_ONLY_AST)
            elif path.suffix == ".json":
                json.loads(text)
            elif path.suffix == ".md":
                broken.extend({"path": rel, "target": link} for link in local_links(path, text))
            elif path in library_set:
                code = lean_code(text)
                imports[module_name(path)] = [m for row in re.findall(r"^\s*import\s+([^\n]+)", code, re.M)
                                             for m in row.split()]
                for match in re.finditer(r"\b(?:sorry|admit|sorryAx)\b|^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\s", code, re.M):
                    forbidden.append({"path": rel, "line": code.count("\n", 0, match.start()) + 1,
                                      "token": match.group().strip()})
                for match in re.finditer(r"\b(?:native_decide|ofReduceBool|trustCompiler)\b", code):
                    native_sites.append({"path": rel, "line": code.count("\n", 0, match.start()) + 1,
                                         "token": match.group()})
        except (SyntaxError, ValueError) as exc:
            errors.append({"path": rel, "error": str(exc)})
    seen, pending = set(), ["UnifiedTheory"]
    while pending:
        name = pending.pop()
        if name in seen: continue
        seen.add(name)
        pending.extend(imports.get(name, []))
    missing = sorted({name for deps in imports.values() for name in deps
                      if name.startswith("UnifiedTheory.") and name not in imports})
    all_modules_in_default_build = bool(re.search(
        r'^globs\s*=\s*\[\s*"UnifiedTheory\.\*"\s*\]',
        (ROOT / "lakefile.toml").read_text(), re.M))
    return {
        "schema_version": 1,
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "configuration_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                                 for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")},
        "file_counts": dict(sorted(counts.items())),
        "library_modules": len(library),
        "root_reachable_library_modules": len(set(imports) & seen),
        "all_modules_in_default_build": all_modules_in_default_build,
        "outside_root_import_closure": sorted(set(imports) - seen),
        "missing_local_imports": missing,
        "lean_escape_hatches": forbidden,
        "native_computation_sites": native_sites,
        "syntax_or_json_errors": errors,
        "broken_local_file_links": broken,
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in files if p.suffix in {".lean", ".py"}},
        "scope": "Static source checks; no mathematical correctness, axiom-dependency, physical identification, or numerical replication claim.",
        "passed": all_modules_in_default_build and not (missing or forbidden or errors or broken),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true", help="Build every library module, not just root imports")
    args = parser.parse_args()
    report = audit()
    if args.build:
        if not report["all_modules_in_default_build"]:
            raise SystemExit('Full audit requires globs = ["UnifiedTheory.*"] in lakefile.toml')
        # Lake expands the glob; thousands of explicit names can exceed ARG_MAX.
        result = subprocess.run(["lake", "build", "UnifiedTheory"], cwd=ROOT)
        report["build"] = {"exit_code": result.returncode,
                           "requested_modules": report["library_modules"]}
        report["passed"] &= result.returncode == 0
    payload = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
        print(json.dumps({k: v for k, v in report.items() if k not in {
            "source_sha256", "outside_root_import_closure", "native_computation_sites"}}, indent=2))
    else:
        print(payload, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
