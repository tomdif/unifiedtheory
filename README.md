# UnifiedTheory

Lean 4 formalization and numerical research on causal-order models, quantum
dynamics, geometry, and Yang–Mills theory.

**A physical theory of everything, a nontrivial continuum Yang–Mills theory,
and a physical Yang–Mills mass gap remain unproved.** Formal results establish
consequences of their definitions and hypotheses; names such as “capstone”,
“Standard Model”, or “complete synthesis” do not certify those physical targets.

Current review: **2026-11-09**. The research was published on `main` in
[PR #1](https://github.com/tomdif/unifiedtheory/pull/1). See [status](STATUS.md) and the
[remaining research obligations](TOE_COMPLETION_PLAN.md).

## Current work

| Area | Current result and boundary | Evidence |
|---|---|---|
| Yang–Mills flux bootstrap | Conditional transverse/in-plane iteration and thermal-excess reductions. Uniform spectral and renormalization estimates remain open. | [Program](UnifiedTheory/Clay/YangMills/README.md), [twisted route](UnifiedTheory/Clay/YangMills/Twisted/README.md), [band tests](UnifiedTheory/Clay/YangMills/GAP_BAND_STATEMENT.md) |
| Abelian curvature heat | Exact cell averages converge uniformly over grid nodes at each fixed positive time to a field satisfying the heat PDE. L² initial trace, continuum uniqueness, rates, and transport assembly remain open formal tasks. | [Model and formal scope](ABELIAN_CURVATURE_HEAT_LIMIT.md) |
| Quantum operator domains and response | Explicit operator, resolvent, regularization, and response theorems for specified causal models. Their hypotheses and domains must be retained. | [Lean audit modules](UnifiedTheory/Audit), [latest causal checkpoint record](data/twenty_seven_checkpoint_complete_tier_one_synthesis_audit.json) |
| Chiral continuum comparison | Flat-holonomy refinement and a nonzero curved fifth-order phase response. Completed-measure phase matching and uniform continuum control remain open. | [Comparison and reproduction](CHIRAL_CONTINUUM_COMPARISON.md) |
| Order, gauge, and geometry | Finite algebraic constructions, obstruction results, and conditional continuum bridges. Physical SM/GR identification remains open. | [Gauge and alpha gates](GAUGE_AND_ALPHA_GATES_2026-10-25.md), [metric assessment](EINSTEIN_MODEL_DECISION.md), [causal holonomy](MONOPOLE_CAUSAL.md) |
| Empirical accountability | Separate proof obligations, numerical tests, and observational claims. The Gate 4–7 ledger contains five pending draft attacks. | [Attack ledger](TOE_GATE456_ATTACK_LEDGER.json), [Yang–Mills requirements](data/yang_mills_requirements.json) |

The thermal-excess reduction in
[`TwistedThermalExcess.lean`](UnifiedTheory/Clay/YangMills/Twisted/TwistedThermalExcess.lean)
establishes finite thermal-excess inequalities, a finite telescoping identity, and a
conditional flux-sector bound reducing `Kper` to the zero-flux ratio within
factors `1/8` and `64`. The lattice trace identification, sector positivity,
and required uniform boundedness are additional obligations.

Work in [TwistedFluxBasis](UnifiedTheory/Clay/YangMills/Twisted/TwistedFluxBasis.lean)
expresses the transverse step through sector interface ratios.
[TwistedSubArea](UnifiedTheory/Clay/YangMills/Twisted/TwistedSubArea.lean)
allows scale-dependent log constants bounded by `A + B q^j`, `q < 4`, with
a sufficient initial margin. Establishing those estimates for physical
transfer operators remains open.
[TwistedSlabCriterion](UnifiedTheory/Clay/YangMills/Twisted/TwistedSlabCriterion.lean)
specializes the recurrence to a slab with fixed transverse dimensions.
The [weighted-budget criterion](UnifiedTheory/Clay/YangMills/Twisted/TwistedWeightedBudget.lean)
also permits a summable normalized cost of order `1/j²`.
[Matrix sector traces](UnifiedTheory/Clay/YangMills/Twisted/SectorTraceMatrix.lean)
and [probability-space kernels](UnifiedTheory/Clay/YangMills/Twisted/KernelDoubling.lean)
now supply doubling inequalities for their specified models. Identifying the
actual Wilson partition functions with those kernel traces remains a separate step.
The [Z₂ torus result](UnifiedTheory/Clay/YangMills/Twisted/Z2Torus.lean)
proves a finite-lattice rectangular-loop bound in its explicit strong-coupling
regime; it does not establish the SU(2) continuum target.
The concurrent [gauge reconstruction study](GAUGE_DISCRETE_CONTINUUM.md)
separates an analytic square-grid argument from its formalized transport
stability ingredients.
The [Abelian heat model](ABELIAN_CURVATURE_HEAT_LIMIT.md) derives the needed
positive-time bounds from specified diffusion dynamics. Its
[new formal extension](UnifiedTheory/LayerA/AbelianCurvatureHeatDynamics.lean)
identifies the actual heat series with the discrete ODE and proves its
semigroup law, uniqueness, conserved sum, and uniform initial-data response.
The [cell-average continuation](UnifiedTheory/LayerA/AbelianCurvatureHeatCellAverage.lean)
proves convergence of the actual grid heat initialized by exact cell averages
of bounded measurable real data. Convergence is uniform over grid nodes at
each fixed positive time. The coefficient bounds, consistency, and finite
reconstruction are derived from cell integration, and the limiting Fourier
series satisfies the [heat PDE](UnifiedTheory/LayerA/AbelianCurvatureHeatPDE.lean).
The L² initial trace and continuum uniqueness, quantitative estimates over
time intervals, and final gauge-transport assembly remain open formal tasks.

The [chiral comparison](CHIRAL_CONTINUUM_COMPARISON.md), motivated by
[Hsu's continuum-Weyl construction](https://arxiv.org/abs/2610.29019v2),
fixes the complementary-chirality convention and supplies an actual complex
response benchmark. Its nine new Lean results establish supporting algebra;
the numerical refinement is not a theorem about the completed measure.
The [open-obligation attack](OPEN_OBLIGATIONS_ATTACK.md) records the completed
phase test, a sharper Yang–Mills weighted-cost criterion, and the remaining
physical inputs across the canonical requirement ledgers.

## Build and audit

The project pins Lean and Mathlib to **v4.28.0**, with the companion dependency
pinned in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).
Install Elan, then run from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/audit_repository.py --build --output /tmp/unifiedtheory-audit.json
python3 scripts/check_repository_axioms.py --output /tmp/unifiedtheory-axioms.json
python3 scripts/check_yang_mills_requirements.py
python3 scripts/validate_toe_attack_ledger.py
```

`lake build` now checks every library module under `UnifiedTheory/`, including
independent research modules outside the umbrella import graph. The audit
command independently enumerates those modules and checks Python syntax, JSON,
local file links, imports, and Lean proof escape hatches. It does not run
simulations or independently establish the physical meaning of a theorem.
`python3 scripts/check_twisted_axioms.py` verifies the explicitly listed
twisted-program theorem dependencies, including the November thermal reductions.
The complete-library axiom check also reports native computation dependencies
used by older modules; it does not claim the whole library uses only three axioms.

Recorded checkpoint reports are historical snapshots. Their hashes and old
build logs must match before their verification claims can be reused for a
new checkout. The [initial cleanup audit](data/repository_audit_2026_11_09.json)
retains its original scope. The [published verification checkpoint](STATUS.md)
covers all 5,440 library modules and 150,121 local declarations; the
[post-merge cleanup record](data/post_merge_cleanup_2026_11_09.json)
records subsequent documentation and temporary-file changes.

## Repository layout

- `UnifiedTheory/`: formal sources; `Audit/` contains causal-model research and
  `Clay/YangMills/` contains the Yang–Mills program.
- `scripts/`, root Python files, and `experiments/`: verification and numerical
  experiments. Runtime dependencies vary by experiment; GPU/hardware scripts
  require their own environment.
- `data/`, `results/`: recorded evidence, including failed tests and obstructions.
- Topic notes: dated research context; use `STATUS.md` for the current overview.

Superseded paper drafts and global completion claims have been removed from
this checkout. There is no manuscript presented here as a current account of
the whole program. The [cleanup manifest](data/repository_cleanup_2026_11_09.json)
records removals and reasons; Git history and a separate local backup preserve
the prior material.

Companion foundations: [causal-algebraic-geometry-lean](https://github.com/tomdif/causal-algebraic-geometry-lean).
License: [Apache 2.0](LICENSE).
