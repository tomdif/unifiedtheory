# TOE Swarm Execution

Status: active coordination note for parallel gap-closing work.

Date: 2026-08-21

This file coordinates bounded agent work against the TOE completion gates.  It
does not claim the gates are closed.  A result is integration-ready only when it
lands in one of the repo's standard buckets:

```text
proved finite theorem
conditional bridge
numerical evidence
physical conjecture
falsifiable prediction
```

## Operating Rules

- Do not run `lake build` while preserving Lean compiled data.
- Use direct Lean checks only, for example:

```text
lake env lean UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean
```

- After any direct Lean check touching the bridge file, probe artifacts:

```text
find .lake -name '*KFCausalCSpecBridgeDefectObservable*' -print
```

- Keep write scopes disjoint.  Prefer scratch notes or small theorem patches
  over broad rewrites.
- Do not stage unrelated cache, log, checkpoint, or generated data files.
- Every proposed theorem must name the target Lean file, existing dependencies,
  and whether it is unconditional or conditional.

## Active Swarm

```text
Gate 1 / Microscopic law
  Target: label-invariant, normalized, quantum-consistent causal-growth law.
  Output: strongest current candidate law, missing theorem statements, one
  smallest provable next theorem.

Gate 2 / Hauptvermutung distortion
  Target: component-level zero-set semantics for countWindow, curvatureBias,
  spectralLocality, and bridge defect.
  Output: missing zero-set theorem statements and target files.

Gate 3 / Dynamics closure
  Target: derive PhysicalHauptvermutungExactRecoveryCertificate from dynamics.
  Output: weakest remaining assumption in the certificate chain and one theorem
  that reduces assembly burden.

Gate 4 / Horizon-to-Einstein limit
  Target: finite recovered stages imply the infrared GR limit.
  Output: existing finite estimator theorems, open analytic assumptions, and one
  next bridge theorem.

Gate 5 / QFT and Standard Model IR limit
  Target: effective Hilbert/QFT/SM limit from the same recovered dynamics.
  Output: unconditional algebraic inventory, physical-identification assumptions,
  and one next interface theorem.

Predictions / Verification
  Target: freeze falsifiable predictions before comparison.
  Output: frozen-vs-open prediction table and preregistration checklist.
```

## Current Critical Path

The bridge/Hauptvermutung recovery side is now a conditional exact-recovery
pipeline:

```text
PhysicalHauptvermutungExactRecoveryCertificate
  -> exists N, every n >= N satisfies PhysicalHauptvermutungRecoveredStage
  -> exists N, every n >= N has all observable defects zero/canonical
```

The immediate critical path is therefore not another bridge-minimization
corollary.  The next high-value theorem should reduce one of these assumptions:

```text
stepFloor <= step_n
weightBase <= w_{n,i}
sourceBase <= -centered(S_n)_i
residualGap <= each nonzero count/curvature/spectral residual
total_n = physicalHauptvermutungTotalDistortion_n
descentRate_n = -linearResponse(S_n, D_n)
```

## Round 1 Results

Integrated proved finite theorems:

```text
physicalHauptvermutungBaseDistortion_eq_zero_iff
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor
```

The first theorem closes the algebraic zero set of the non-bridge base
distortion.  Under nonnegative channels, base distortion zero is exactly
componentwise zero of `countWindow`, `curvatureBias`, and `spectralLocality`.

The second theorem gives a shorter Gate 3 route.  A positive aggregate descent
floor

```text
rateBase*total_n <= descentRate_n
```

plus a positive update-step floor is enough for horizon-protected convergence.
Lean clips the effective rate by `1/stepFloor`, so no separate upper product
condition is needed.  This makes the pointwise centered-source floor a possible
derivation of the aggregate rate rather than the only logical gate.

## Round 1 Gate Findings

- Gate 1: the strongest scalar candidate remains
  `completeChiralCausalSetGrowthLaw`; support zero outside physical transitions
  is now integrated as
  `completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical`.
  Parent-isomorphism covariance, concrete projectivity, and concrete quantum
  consistency are now integrated as
  `completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic`,
  `completeChiralCausalSetGrowthLaw_gate1_projective`, and
  `completeChiralCausalSetGrowthLaw_gate1_quantum_consistent`.
- Gate 2: the bridge zero set is strong; the semantic gap is now the meaning of
  zero `countWindow`, `curvatureBias`, and `spectralLocality` residuals.
- Gate 3: avoid depending exclusively on a positive pointwise centered-source
  floor; normalized weights can make a uniform negative centered-source floor
  too strong.  Prefer deriving the direct aggregate rate when possible.
- Gate 4: recovered finite stages now bridge into the RSS/Poisson horizon-flux
  error budget through `KFCausalCSpecRecoveredStageGRLimit`; they also feed a
  bundled BDG assembler through `KFCausalCSpecRecoveredStageBDGInterface`.
  `KFCausalCSpecRecoveredStageBDGProfile` converts real high-density profile
  limits into the interface's sequence-level per-layer asymptotics.  The
  concrete reduced 4D operator theorem is now packaged by
  `KFCausalCSpecRecoveredStageBDG4DOperator`.  The remaining work is to derive
  `BDG4DOperatorProfileData` from the physical causal-growth law and recovered
  local charts; once supplied, `KFCausalCSpecRecoveredStageBDG4DRecovered`
  proves the combined zero-error and sampled-operator-limit result.
- Gate 5: exact recovered CSpec stages should next carry finite Hilbert fibers,
  local Born normalization, and local observable algebras before any continuum
  QFT claim.
- Predictions: the five-row formal preregistration ledger is canonical.  Older
  prediction-shaped claims need promotion with assumption tags or demotion.

## Integration Checklist

For each agent result:

```text
1. Identify whether it is a theorem patch, conditional bridge, numerical lead,
   physical conjecture, or prediction artifact.
2. Reject or rewrite any claim that outruns the formal result.
3. If it edits Lean, run the direct Lean file check only.
4. Probe `.lake` artifacts after the check.
5. Update README, STATUS, TOE_COMPLETION_PLAN, and capstone docs only when the
   theorem or artifact is actually integrated.
6. Commit only intended files and push to main.
```

## Next Integration Queue

```text
Gate 1:
  derive physical aggregate-rate and residual-gap hypotheses from
  completeChiralCausalSetGrowthLaw
  identify the microscopic selection principle for canonicalPairCoupling

Gate 2:
  finitePairConsistencyResidual_eq_zero_iff
  spectralLocalityOfPairConsistency_eq_zero_iff
  finiteCountWindowResidual_eq_zero_iff
  finiteCurvatureBiasResidual_eq_zero_iff

Gate 3:
  derive rateBase*total_n <= descentRate_n from the microscopic law

Gate 4:
  BDG4DOperatorProfileData

Gate 5:
  RecoveredCSpecHilbertFiber
  RecoveredCSpecHilbertFiber.transport_and_born

Gate 7:
  keep PREDICTIONS_PREREGISTRATION_LEDGER.json as the public comparison target
```
