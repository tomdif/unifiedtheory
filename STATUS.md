# Current research status

Reviewed **2026-11-09**, consolidating the research on
`paper3-inf-resolution` for publication on `main`. Historical verification
records retain their original source hashes and checkout scope.

**The physical TOE and the Clay Yang–Mills target remain open.** No theorem
count, algebraic parameter fit, finite-volume gap, or numerical scan closes
those targets on its own.

## Yang–Mills: current frontier

The [band program](UnifiedTheory/Clay/YangMills/GAP_BAND_STATEMENT.md) develops
a flux-bootstrap route using the sector thermal inequality **(S)** and a bound
**K-bar** on in-plane thermal excess above an onset length `L0(beta)`.
The recurrence results relax bounded scale constants to specified growth below the
area rate. The physical estimates and their control as `beta → infinity`
are still missing.

- [TwistedFluxInduction](UnifiedTheory/Clay/YangMills/Twisted/TwistedFluxInduction.lean)
  proves the stated conditional iteration and area-type decay implications.
- [TwistedThermalExcess](UnifiedTheory/Clay/YangMills/Twisted/TwistedThermalExcess.lean)
  proves the finite thermal sandwich, `K <= 2 Kper`, finite telescoping,
  signed-sum comparison, and conditional flux split. For eight sectors,
  the displayed assumptions bound `Kper` between `K0/8` and `64 K0`.
  The physical trace correspondence, positivity of the sector partition
  functions, infinite-spectrum limits, and uniform bound are not supplied
  by these elementary inequalities.
- [TwistedFluxBasis](UnifiedTheory/Clay/YangMills/Twisted/TwistedFluxBasis.lean)
  proves an algebraic transverse identity and conditional inequality in terms
  of `K0/Ke`. [TwistedSubArea](UnifiedTheory/Clay/YangMills/Twisted/TwistedSubArea.lean)
  proves a recurrence bound when `m_j <= A + B q^j`, `0 <= q < 4`.
  A positive area-decay margin requires `u_0 > A/3 + B/(4-q)`.
  These hypotheses must still be established for the lattice theory; the
  theorem does not cover every arbitrary `o(L^2)` growth law.
- [TwistedWeightedBudget](UnifiedTheory/Clay/YangMills/Twisted/TwistedWeightedBudget.lean)
  now gives the exact normalized-cost criterion for the saturated recurrence
  and a sufficient telescoping envelope of order `4^j/j^2`. A formal harmonic
  counterexample is pointwise subarea but has a divergent cost budget. These
  ten theorems sharpen the physical estimate still needed for the flux route.
- [TwistedSlabCriterion](UnifiedTheory/Clay/YangMills/Twisted/TwistedSlabCriterion.lean)
  specializes the recurrence to `q=2`. Its slab interpretation keeps the
  transverse dimensions fixed; the lattice-to-recurrence identification is
  not formalized there, and it does not establish the four-dimensional limit.
- The November 8 [transverse scan](data/yang_mills_twist_transverse_scan_2026_11_08.json)
  supports the registered test (16) at the sampled sizes; test (17) fails as
  written. It does not prove (S), address K-bar, or establish uniformity.
- The November 9 [thermal-excess probe](scripts/yang_mills_thermal_excess.py)
  now has [recorded results](data/yang_mills_thermal_excess_2026_11_09.json).
  Test (18) misses its central-value threshold: `1.25 ± 0.55` versus `< 1.0`,
  only `0.46 sigma` above it. Test (19) fails its monotonicity requirement:
  the beta 2.6 to 3.0 decrease is about `3.93 sigma`, assuming independent errors.
  The [second batch](data/yang_mills_thermal_excess_2026_11_09b.json) also misses
  test (20) as written: beta 2.6, L=12 gives `2.78 ± 1.02` versus `< 1.0`.
  The [higher-statistics follow-up](data/yang_mills_thermal_excess_2026_11_09c.json)
  misses test (21)'s beta 2.6 threshold on the central value: `1.40 ± 0.58`
  versus `< 1.0`, about `0.7 sigma`; its beta 2.5 threshold holds.
- The [sector-slab probe](scripts/yang_mills_sector_slab.py) records failure
  of test (22): at beta 2.4 the fitted exponent is `2.8 [1.7, 4.1]`, with
  approximately volume-like scaling. Beta 2.3 remains undetermined by the noise.
  See the [recorded data](data/yang_mills_sector_slab_2026_11_09.json).

All **twelve full-target requirements remain open** in the
[requirements ledger](data/yang_mills_requirements.json). The
[Yang–Mills overview](UnifiedTheory/Clay/YangMills/README.md) separates this
frontier from the earlier Wilson/OS and twisted finite-lattice work.

## Causal quantum dynamics and geometry

The new [chiral continuum comparison](CHIRAL_CONTINUUM_COMPARISON.md) tests the
actual mass-one overlap operator against continuum Weyl references. At temporal
holonomy `h=0.13`, the absolute log-weight error decreases from `0.0147553` at
`N=8` to `0.000200319` at `N=64`. A curved background has a nonzero imaginary
fifth-order response, with refinement toward the continuum cutoff calculation.
The comparison retains the complementary chirality required by the positive
continuum Weyl domain. Nine new algebraic Lean results build and pass a focused
three-standard-axiom inspection. The curved experiment uses the dynamical
current in a radial Kato frame; the completed cohomology phase and a uniform
continuum estimate remain separate, unresolved obligations.
The separate [completed-phase probe](data/chiral_completed_phase_response.json)
finds a roughly 13.5% fifth-current correction on its generic finite `2^4`
field. Its amplitude fits do not establish decay under continuum refinement.

New [gauge transport work](GAUGE_DISCRETE_CONTINUUM.md) gives a deterministic
square-grid reconstruction argument with explicit regularity assumptions.
[GaugeTransportStability](UnifiedTheory/LayerA/GaugeTransportStability.lean)
formalizes tree-gauge identities, ordered-product and unitary-path stability,
and axial-integral estimates. The note identifies the remaining gap between
these ingredients and a fully formalized discrete-to-continuum theorem.
It does not construct the physical quantum theory or a mass gap.

For the specific [Abelian curvature heat model](ABELIAN_CURVATURE_HEAT_LIMIT.md),
the [dynamics extension](UnifiedTheory/LayerA/AbelianCurvatureHeatDynamics.lean)
adds 15 formal results: the existing Poisson series solves the actual finite
grid ODE, obeys the semigroup law, conserves the sum, and is unique among global
differentiable solutions with the same initial value. Its initial-data
derivative is the heat operator, of norm at most one for nonnegative time.
The [cell-average continuation](UnifiedTheory/LayerA/AbelianCurvatureHeatCellAverage.lean)
now derives the Fourier coefficient bounds and consistency from integration,
proves normalized inversion on the centered frequency window, and identifies
the reconstructed data with the exact cell averages. The actual grid heat
therefore converges uniformly over nodes at each fixed positive time for
bounded measurable real data. The
[PDE extension](UnifiedTheory/LayerA/AbelianCurvatureHeatPDE.lean) justifies
termwise differentiation and proves the limiting heat equation.
The L² initial trace and continuum uniqueness, quantitative rates uniform over
positive time intervals, and final gauge-transport assembly still require
formalization. The
[attack report](OPEN_OBLIGATIONS_ATTACK.md) records how this restricted model
relates to the broader open physical requirements.

The current sources contain extensive operator-domain, resolvent, response,
finite-order, and geometric constructions. The latest causal checkpoint
record is the [twenty-seven-checkpoint synthesis](data/twenty_seven_checkpoint_complete_tier_one_synthesis_audit.json).
Its stated scope includes wide-strip residual/full-Hamiltonian output
regularization and conditional synthesis results; it is not a TOE certificate.

That historical report contains 3,906 source/script hashes. Two no longer match
this checkout: `KFCausalNeutralHermiteDomain.lean` and
`KFCausalNeutralHermiteBasis.lean`. Its root-import hash also differs.
The old overlay verifier additionally requires the original temporary build
artifacts. It must not be advertised as a fresh verification of today's tree.
The repository audit records current checks separately, without changing the
historical report to make it pass.

Some older modules use `native_decide`, which introduces Lean's native
computation trust dependency. The whole repository must not be described as
using only the three standard axioms on the strength of a selected theorem
audit. The source audit lists these sites; the Twisted and q-series axiom
checks have their own explicit declaration scope.

The remaining physical work includes selecting the microscopic dynamics and
states, recovering clocks and observables with the required domain control,
proving controlled continuum/regulator limits, and identifying the same
candidate with physical SM/GR fields. Consult the
[research plan](TOE_COMPLETION_PLAN.md) for acceptance criteria. Dated notes and
negative experiments remain evidence about their specified models, even when
the overall research direction has advanced.

## Repository audit and cleanup

The [audit record](data/repository_audit_2026_11_09.json) gives check outcomes
and limitations. Before cleanup, the checkout contained 3,181 tracked files
and 5,102 untracked files. There were 5,418 library Lean modules, with 251
outside the default root import graph. The Lake configuration now builds every
library module; the audit command independently inventories those modules and
verifies the complete library with `--build`.

Two previously omitted modules failed when compiled independently:
`LayerB/FiberSections.lean` and `LayerB/PartitionFunction.lean`. Missing imports,
a malformed standalone docstring, noncomputability, and a missing nonempty-index
instance were repaired without changing theorem statements. Their explanatory
comments now describe the results actually established.

The README, this status, the completion plan, and both Yang–Mills overviews
replace accumulated progress-feed summaries. Superseded paper drafts, old
global completion/handoff plans, and generated bytecode were removed with
an external working-tree backup and a [deletion manifest](data/repository_cleanup_2026_11_09.json).
Formal research and experiment evidence remain available. Historical
checkpoint reports are retained with their original hashes.

The completed cleanup audit is a snapshot predating the chiral comparison
above. Its final local verification included the research additions that
arrived during that audit:

| Check | Result |
|---|---|
| Complete library build | Passed for all **5,422** modules, including modules outside the umbrella graph. Incremental Lake verification; unchanged artifacts may be replayed. |
| Complete-library axiom inspection | **149,442 declarations** inspected, including private declarations; no unexpected axioms. Dependencies are `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, and `Lean.trustCompiler`. |
| Focused theorem axiom checks | **231** Twisted and **51** q-series/occupation declarations passed with only the three standard axioms. |
| Source and documentation checks | Imports, proof-escape scan, Python syntax, JSON, local links, and section links passed; **44** native-computation source sites are disclosed. |
| Research ledgers | Both validators passed; twelve Yang–Mills full-target obligations remain open and five TOE attacks remain draft/no-result. |
| Dependency and backup integrity | All ten dependency checkouts match their pinned revisions; all **8,283** pre-cleanup backup files match their recorded hashes. |

The cleanup removed **108** obsolete or unrelated files. The audit record
contains compressed logs and source/configuration hashes. Docker was not
available; the image and remote GitHub Actions were not run. Historical and
GPU experiments were not comprehensively rerun. That audit preceded publication;
concurrent research updates were preserved.

The Lean/Mathlib version remains the pinned v4.28.0 baseline. Dependency
upgrades require a separate compatibility migration; this audit does not
change mathematical foundations to obtain newer package numbers.
