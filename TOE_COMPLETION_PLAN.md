# Remaining research obligations

Current scope: **2026-11-09**. This replaces the accumulated checkpoint feed.
[STATUS.md](STATUS.md) records the current frontier; exact theorem hypotheses
remain in the Lean sources and dated audit reports. A physical TOE remains
unproved.

## Yang–Mills spectral and continuum control

Follow the [band program](UnifiedTheory/Clay/YangMills/GAP_BAND_STATEMENT.md)
and the [twelve-requirement ledger](data/yang_mills_requirements.json).
For the current flux-bootstrap route:

1. Prove (S), the sector-thermal estimate behind the transverse multiplicative
   step, for the actual finite-box transfer operators and all required shapes
   beyond `L0(beta)`.
2. Prove K-bar, the required uniform thermal-excess bound. The
   [thermal-excess reduction](UnifiedTheory/Clay/YangMills/Twisted/TwistedThermalExcess.lean)
   is conditional: supply trace identities, sector positivity, and the
   infinite-spectrum convergence needed for the spectral formulation.
   [SectorTraceMatrix](UnifiedTheory/Clay/YangMills/Twisted/SectorTraceMatrix.lean)
   now proves the finite matrix inequality, and
   [KernelDoubling](UnifiedTheory/Clay/YangMills/Twisted/KernelDoubling.lean)
   supplies an integral-kernel alternative at even time. For that alternative,
   identify the actual Wilson partition functions with the formal kernel traces
   and verify the symmetry, measurability, boundedness, and involution hypotheses.
3. Control both bounds and the onset scale along the renormalization trajectory.
4. Construct and identify one nontrivial continuum theory, its physical fields,
   quantum-field axioms, and positive finite excitation scale. Finite-volume
   operator inequalities and numerical fits are intermediate evidence.

The new [flux-basis identity](UnifiedTheory/Clay/YangMills/Twisted/TwistedFluxBasis.lean)
and [growing-constant iteration](UnifiedTheory/Clay/YangMills/Twisted/TwistedSubArea.lean)
offer a weaker sufficient route: establish `m_j <= A + B q^j`, `0 <= q < 4`,
and `u_0 > A/3 + B/(4-q)` for the physical model. This can replace bounded
scale constants, but still requires operator correspondence and control along
the renormalization trajectory. Arbitrary growth described only as `o(L^2)`
does not supply the stated geometric bound.
The [weighted-budget extension](UnifiedTheory/Clay/YangMills/Twisted/TwistedWeightedBudget.lean)
now permits the sharper sufficient envelope
`m_j <= 4^(j+1) B/((j+1)(j+2))` with `B<u_0`, while proving that a harmonic
normalized cost can diverge despite pointwise subarea growth. Establish the
weighted bound on the actual full interpolation path and along the physical
renormalization trajectory.

The registered thermal-excess tests are in
[scripts/yang_mills_thermal_excess.py](scripts/yang_mills_thermal_excess.py).
The [November 9 results](data/yang_mills_thermal_excess_2026_11_09.json)
miss (18)'s central-value threshold and fail (19)'s monotonicity requirement.
The [second batch](data/yang_mills_thermal_excess_2026_11_09b.json) misses
test (20)'s beta 2.6, L=12 threshold. The
[higher-statistics follow-up](data/yang_mills_thermal_excess_2026_11_09c.json)
also misses test (21)'s beta 2.6 threshold on its central value, by about
`0.7 sigma`; the beta 2.5 threshold holds.
Preserve these registrations and
record failures as well as successes. These
computations can test the proposed route; they cannot prove uniform estimates.
The [sector-slab test (22)](scripts/yang_mills_sector_slab.py) probes the
transverse interface cost and fails its registered subarea criterion at beta 2.4;
beta 2.3 remains undetermined by the noise.

## Microscopic causal dynamics and quantum response

The [audit sources](UnifiedTheory/Audit) contain model-specific constructions
and increasingly strong operator-domain and regularization results. The
[latest causal checkpoint](data/twenty_seven_checkpoint_complete_tier_one_synthesis_audit.json)
is a historical snapshot, with the current hash differences documented in
[STATUS.md](STATUS.md).

For each proposed physical consequence, specify the microscopic law, Hilbert
space, state class, operator domains, clock, and observable map. Establish the
required evolution and response statements for that same candidate, with
constants uniform in the parameters actually sent to a limit. A theorem for
one neutral/source sector or fixed regulator does not establish the statement
for unrestricted states or a continuum physical theory. Existing obstruction
and counterexample modules constrain which extensions can be claimed.

## Gauge, matter, and gravity identification

The [gauge and alpha gates](GAUGE_AND_ALPHA_GATES_2026-10-25.md) and
[metric assessment](EINSTEIN_MODEL_DECISION.md) identify separate obligations.
Finite algebraic identities, canonical metric coordinates, and conditional
Einstein implications must be connected to a controlled physical sector of
the original microscopic dynamics.

Supply physical fields and observables, their symmetries and constraints,
interaction dynamics, a common regulator/continuum limit, and an explicit
identification with the Standard Model and gravitational observables.
Parameter fits and legacy formula names do not replace those constructions.
The [current attack report](OPEN_OBLIGATIONS_ATTACK.md) supplies a finite heat-ODE
formalization, a complete finite chiral-phase diagnostic, and a requirement-by-
requirement account of the physical inputs still absent. The heat model's
linear response bound applies to initial scalar grid data; it does not supply
the four-dimensional differentiated gauge reconstruction or completed chiral
continuum-current matching required by the fermion comparison.
The fine-structure constant, mixing data, mass scales, and cosmological
observables are not established first-principles physical predictions merely
because a formula for them has been formalized.

## Empirical and publication criteria

The [Gate 4–7 attack ledger](TOE_GATE456_ATTACK_LEDGER.json) is a draft protocol
with five pending attacks and no freeze provenance. A physical verdict
requires fixed readouts, estimators, tolerances, provenance, and comparison
data. Numerical preregistrations in the Yang–Mills program are separate from
that ledger and retain their own recorded verdicts.

A new manuscript should cite the current definitions and hashes, separate
proved implications from assumed physical identifications, report negative
results, and state precisely which numerical tests were reproduced. The old
paper drafts have been removed because they do not describe the current
verification scope.

## Verification discipline

```sh
python3 scripts/audit_repository.py --build --output /tmp/unifiedtheory-audit.json
python3 scripts/check_repository_axioms.py --output /tmp/unifiedtheory-axioms.json
python3 scripts/check_yang_mills_requirements.py
python3 scripts/validate_toe_attack_ledger.py
```

Keep historical reports immutable. A new check needs its own report; a
changed source, root import, or missing temporary overlay invalidates reuse
of an older snapshot's verification claim. Static scanning, Lean compilation,
transitive axiom inspection, and numerical replication are distinct checks.
