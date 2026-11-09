#!/usr/bin/env python3
"""Inspect transitive axioms of every declaration from local library modules.

Run after `lake build`. Native computation is recorded explicitly; it is not
misreported as a proof using only the three standard axioms.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

from audit_repository import ROOT, module_name, repository_files

CHECK = r'''
-- This finite traversal covers the complete imported declaration graph.
set_option maxHeartbeats 0
open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | none => names
    | some idx =>
      let mod := env.header.modules[idx]!.module.toString
      if mod == "UnifiedTheory" || mod.startsWith "UnifiedTheory." then
        names.push name
      else names
  if names.isEmpty then throwError "No local declarations were inspected"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed := ["propext", "Classical.choice", "Quot.sound", "Lean.ofReduceBool", "Lean.trustCompiler"]
  let axioms := (state.axioms.qsort Name.lt).map Name.toString
  let unexpected := axioms.filter fun name => !allowed.contains name
  let result := Json.mkObj [
    ("declarations_inspected", toJson names.size),
    ("transitive_axioms", toJson axioms),
    ("unexpected_axioms", toJson unexpected)]
  logInfo m!"REPOSITORY_AXIOMS {result.compress}"
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axiom dependencies"
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()
    modules = sorted(module_name(p) for p in repository_files() if p.suffix == ".lean" and
                     (p == ROOT / "UnifiedTheory.lean" or p.is_relative_to(ROOT / "UnifiedTheory")))
    with tempfile.TemporaryDirectory(prefix="unifiedtheory-axioms-") as directory:
        source = Path(directory) / "CheckAll.lean"
        source.write_text("import Lean.Util.CollectAxioms\n" +
                          "".join("import " + name + "\n" for name in modules) + CHECK)
        proc = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if args.log: args.log.write_text(proc.stdout)
    if proc.returncode:
        print(proc.stdout)
        return proc.returncode
    match = re.search(r"REPOSITORY_AXIOMS (\{[^\n]+\})", proc.stdout)
    if not match: raise RuntimeError("Missing axiom inspection result")
    report = json.loads(match.group(1))
    report.update(passed=not report["unexpected_axioms"], library_modules=len(modules),
                  scope="All declarations whose defining module is in the local UnifiedTheory library, including private declarations. Native computation dependencies are permitted and disclosed.")
    if args.output: args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
