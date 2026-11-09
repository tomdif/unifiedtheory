# Open obligations and verified reductions

The November 9 attack closes a finite heat-dynamics formalization gap, weakens
the sufficient Yang–Mills scale-cost hypothesis, and measures a previously
omitted chiral phase contribution. The physical Yang–Mills and TOE obligations
remain open. The [attack record](data/open_obligations_attack_2026_11_09.json)
maps the twelve Yang–Mills requirements and five registered TOE attacks to
their remaining inputs without changing their acceptance rules.

## Abelian curvature heat dynamics

[AbelianCurvatureHeatDynamics](UnifiedTheory/LayerA/AbelianCurvatureHeatDynamics.lean)
extends the user-identified
[AbelianCurvatureHeat](UnifiedTheory/LayerA/AbelianCurvatureHeat.lean).
For a finite additive grid, let `P` be the actual four-neighbor averaging
operator. The new proof identifies the existing Poisson series with

```text
H(s) = exp(-s) exp(s P).
```

It derives `dH(s)f/ds = (P-I)H(s)f`, the semigroup law, conservation of the
finite sum, and uniqueness among global differentiable solutions with the
same initial data. With `s=4n²t`, the actual `gridHeat` solves the specified
discrete Laplacian equation for every nonzero grid size. The derivative with
respect to initial data is exactly `H(s)`, with operator norm at most one for
`s>=0`, uniformly in the finite grid size.

The [Fourier continuation](UnifiedTheory/LayerA/AbelianCurvatureHeatGridLimit.lean)
now connects the actual dynamics to a positive-time continuum Fourier limit.
It proves diagonalization for every finite datum, exact lattice-character
eigenvalues, polynomially weighted Gaussian summability, and spatially uniform
convergence for reconstructed data with uniformly bounded Fourier coefficients
that converge at each frequency. Vanishing initialization errors preserve
this limit. The [follow-up verification record](data/abelian_curvature_heat_fourier_verification.json)
is separate from the earlier 25-theorem attack checkpoint.

The [cell-average continuation](UnifiedTheory/LayerA/AbelianCurvatureHeatCellAverage.lean)
discharges the coefficient hypotheses for the specified initialization.
It proves that the modular cells restricted to the unit square are the usual
half-open rectangles of area `1/(n+1)²`, derives bounded and consistent Fourier
coefficients from their integrals, and reconstructs the exact cell averages.
Consequently the actual grid heat has the stated spatially uniform limit at
each fixed positive time for bounded measurable real data. The
[PDE proof](UnifiedTheory/LayerA/AbelianCurvatureHeatPDE.lean) justifies
differentiating the infinite series and verifies the limiting heat equation.
The [new verification record](data/abelian_curvature_heat_cell_average_verification.json)
covers this extension separately from the earlier Fourier checkpoint.

The L² initial trace and continuum uniqueness, quantitative estimates uniform
over positive time intervals, and assembly of the continuum transport bounds
in the [analytic model proof](ABELIAN_CURVATURE_HEAT_LIMIT.md) still require formalization.
This model supplies deterministic Abelian
diffusion and open-square gauge reconstruction. It does not provide a
four-dimensional quantum gauge measure, relativistic dynamics, or the
non-Abelian reconstruction required for the full physical program.

## Yang–Mills weighted scale budget

For the conditional recurrence `u(k+1) >= 4u(k)-m(k)`, define

```text
B(k) = Σ(j<k) m(j)/4^(j+1).
```

[TwistedWeightedBudget](UnifiedTheory/Clay/YangMills/Twisted/TwistedWeightedBudget.lean)
proves that `B(k)<=B<u(0)` yields a positive area-decay margin. For the
saturated recurrence this condition, with the corresponding margin, is exact.
The new telescoping sufficient envelope is

```text
m(j) <= 4^(j+1) B / ((j+1)(j+2)),    B>=0.
```

Its normalized costs sum to at most `B`. At `L=2^j L0`, it permits growth of
order `L²/(log L)²`, closer to area growth than the previous geometric
envelopes with exponent strictly below two. Constants and the initial margin
still matter.

The same module proves that `m(j)=4^(j+1)/(j+1)` is pointwise subarea while its
normalized budget diverges. Thus arbitrary `o(L²)` control cannot justify this
recurrence argument. The uncut sector-slab observable in test (22) also does
not bound the whole split/join interpolation. A physical estimate must control
that path, the scale sum, and the renormalization trajectory.

## Completed chiral phase

The [continuum comparison](CHIRAL_CONTINUUM_COMPARISON.md) reaches a 26.2%
curved-current discrepancy at its finest `N=12` grid against continuum cutoff
32. Its dynamical-current refinement excludes the cohomology phase.

The new [completed-phase calculation](data/chiral_completed_phase_response.json)
uses a separate generic `2^4` field and the actual finite cohomology completion.
Odd-amplitude fits give `[t^5] C(tA) ≈ -2.68775e-8` for one charge-one fermion.
The positive-chirality current coefficient changes from approximately
`-9.94557e-7 i` to `-1.12894e-6 i`, a 13.5% change in magnitude. Varying the fit
range gives consistent coefficients. This finite-volume calculation establishes
that discarding the correction is numerically consequential; its decay under
physical lattice refinement is still unproved. It is a different field from
the curved continuum-refinement test, so the two percentages cannot be combined.

## Physical requirements still requiring a common candidate

| Requirements | Attack outcome and remaining input |
|---|---|
| YM01 | The heat model is Abelian. A construction for every compact simple gauge group is still required. |
| YM02, YM12 | A nonflat classical heat limit does not supply a nontrivial quantum continuum state or a finite nonzero excitation scale. These must hold for the same renormalized candidate. |
| YM03 | Classical curvature and transport control advance identification at the deterministic level. Renormalized quantum observables and operator mixing remain missing. |
| YM04 | Existing conditional OS constructions require a common invariant domain for the physical local fields. The new finite heat evolution does not instantiate that domain. |
| YM05, YM06 | Diffusion time is not a physical Poincaré time generator. Covariance, spatial generators, and the joint forward-cone spectrum remain required. |
| YM07, YM08, YM09 | Vacuum uniqueness and cyclicity, spacelike locality, and the complete axiom package must be attached to the same nontrivial continuum theory. Finite nets and separate conditional interfaces do not supply it. |
| YM10 | A controlled ultraviolet trajectory and physical short-distance identification remain required; fixed external-field fermion tests do not supply them. |
| YM11 | The weighted-budget theorem weakens the sufficient input. Actual sector-transfer estimates and a uniform positive physical gap remain open. |
| Gate 4 | A nonzero BDG target and a Lorentzian field/chart target from the same recovered causal kernel remain required. |
| Gate 5 | The finite net needs its physical correlated state, explicit incidence-equivariance supplier, and a nondegenerate continuum construction. |
| Gate 6 | The existing `N=1` examples fail the stated `N>=100000` viability prerequisite. A derived viable readout and the selected scrambling, recovery, and gravitational inputs remain required. |
| Gate 7 | The five protocols remain draft, with no freeze provenance or external results. Historical preregistration cannot be created retrospectively. |
| Shared Gates 4–6 | The formal joint-law construction needs a common numerical event table and fixed readouts before the advertised numerical marginal test can receive a verdict. |

Microscopic action selection and gravitational constraints are additional
physical obligations. The existing action-family witness in
[the locality assessment](UNIFORM_REFERENCE_LOCALITY.md) leaves dynamics
underdetermined, and the [metric assessment](EINSTEIN_MODEL_DECISION.md) explains
why a regular coordinate change cannot repair missing physical modes or
constraints. No existing negative test is relabeled as a success here.

## Reproduction

```sh
lake build UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
lake env lean scripts/CheckAbelianCurvatureHeatDynamics.lean
lake build UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
lake env lean scripts/CheckAbelianCurvatureHeatFourier.lean
lake build UnifiedTheory.LayerA.AbelianCurvatureHeatCellAverage
lake env lean scripts/CheckAbelianCurvatureHeatCellAverage.lean
lake build UnifiedTheory.Clay.YangMills.Twisted.TwistedWeightedBudget
lake env lean scripts/CheckTwistedWeightedBudget.lean
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/chiral_completed_phase_response.py --check-quadrature
python3 scripts/check_yang_mills_requirements.py
python3 scripts/validate_toe_attack_ledger.py
```

The initial dynamics and weighted-budget modules contain 15 and 10 supporting
theorem declarations, respectively. Their focused build and axiom results are recorded separately
from the earlier whole-library cleanup snapshot. The numerical phase fits are
floating-point diagnostics, without an interval or continuum error certificate.
