import UnifiedTheory.Clay.YangMills.Twisted.TwistedNeutral
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTraceLaw
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSemiclassical
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCovarianceDecay
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlow
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalTail
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockStep
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBridge
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLimit

/-! Axiom audit of every theorem and definition in the nine modules added on 2026-10-31, found by walking
the environment rather than from a list of names. Prints a count per module and any declaration whose axioms
are not among propext, Classical.choice and Quot.sound. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := #["TwistedNeutral", "TwistedTraceLaw", "TwistedSemiclassical", "TwistedCovarianceDecay",
    "TwistedFlow", "TwistedLocalTail", "TwistedBlockStep", "TwistedBridge", "TwistedLimit"]
  let ok := #[``propext, ``Classical.choice, ``Quot.sound]
  for short in names do
    let mod := `UnifiedTheory.Clay.YangMills.Twisted ++ Name.mkSimple short
    let some idx := env.getModuleIdx? mod | logError m!"missing module {mod}"
    let mut total := 0
    let mut thms := 0
    let mut bad : Array (Name × Array Name) := #[]
    for (n, c) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n != some idx then continue
      if n.isInternal then continue
      total := total + 1
      if c matches .thmInfo _ then thms := thms + 1
      let ax ← liftCoreM (collectAxioms n)
      let off := ax.filter (fun a => !ok.contains a)
      if !off.isEmpty then bad := bad.push (n, off)
    logInfo m!"{short}: {total} declarations, {thms} theorems, {bad.size} with other axioms {bad.toList.take 5}"
