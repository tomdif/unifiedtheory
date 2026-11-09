# Chiral continuum comparison

The mass-one overlap operator now has reproducible comparisons with continuum
Weyl fermions on a physical four-torus of side `2π`, with antiperiodic fermions
in the fourth direction. The flat-holonomy weight and current approach the
continuum values under refinement. A separate curved-field experiment resolves
a nonzero fifth-order imaginary response. Its overlap values approach the
finite-cutoff continuum reference over the finer sampled grids, but the
completed cohomology measure phase and a uniform continuum estimate remain open.

The comparison follows the chirality distinction and weak-field matching target
in [Hsu, arXiv:2610.29019v2, Appendix D](https://arxiv.org/html/2610.29019v2#A4).
That paper's matching statement specifies a particular measure current and
common normalization. It cannot be transferred to this repository merely
because both constructions use overlap fermions.

## Chirality and normalization

The repository uses `D = 1 + γ5 ε`, with `ε = sign(H)` and Wilson mass one.
Consequently `γ̂5 = γ5(1-D) = -ε`: its projector `(1+ε)/2` is the **negative**
deformed-chirality domain. The positive continuum Weyl map instead corresponds
to domain `(1-ε)/2` and constant codomain `(1-γ5)/2`.

Both determinants are normalized at the same flat reference. With conjugate
measure conventions, changing to the complementary domain conjugates the
complete normalized weight, including its phase. The finite curved-background
control independently constructs both chiral blocks and checks this relation;
it uses direct-rotation frames and is separate from the completed measure.

[Nine Lean results](UnifiedTheory/Audit/KFCausalChiralContinuumComparison.lean)
prove the projector dictionary, complementary intertwining, an exact
noncommutative resolvent subtraction identity, the degree-four polynomial
coefficient statement below, and three supplied-charge identities.
The [axiom inspection](data/chiral_continuum_comparison_axioms.json) finds only
`propext`, `Classical.choice`, and `Quot.sound` among their dependencies.
These are algebraic results; no analytic continuum convergence is formalized.

## Flat temporal holonomy

Set `A3 = h`, `|h| < 1/2`, with other components zero. Charge is absorbed into
`h`. Curvature vanishes, but the temporal holonomy is nontrivial. In the
canonical flat phase convention, the vacuum-normalized weight is real and
positive, and field-dependent local curvature counterterms vanish.

The continuum temporal product can be evaluated before the spatial sum. Writing
`r = |n|`, `e = exp(-2πr)`, and `θ = 2πh`, the one-Weyl logarithm and current are

```text
R(h) = Σ(n∈Z³) log(1 + 2e(cos θ - 1)/(1+e)²)
J(h) = Σ(n∈Z³) -4πe sin θ / (1 + 2e cos θ + e²).
```

The omitted spatial shells have cardinality `24k²+2` and radius at least `k`.
Summing their geometric bounds gives truncation errors below `3.75e-16` for
`R` and `1.18e-15` for `J` at cutoff six. These bound truncation, not floating
point rounding. The lattice computation sums the exact free overlap dispersion
and checks it independently against the full position-space operator at `N=2,4`.

At `h=0.13`, the reference values are `R=-0.179867881828154` and
`J=-2.838351806179743`:

| Lattice side N | Absolute log-weight error | Absolute current error |
|---|---:|---:|
| 8 | 0.0147553 | 0.214593 |
| 16 | 0.00366125 | 0.0532107 |
| 32 | 0.000824037 | 0.0119752 |
| 64 | 0.000200319 | 0.00291106 |

The [record](data/chiral_continuum_comparison.json) also contains `h=0.05,0.24`.
The finer-grid errors are consistent with quadratic spacing dependence on these
samples. This does not supply a uniform estimate over curved backgrounds.

## Curved field and fifth-order phase

Fix the following real, smooth, charge-one external potential, independent of
`x2,x3`:

```text
A0 = 0.10 sin(x0) + 0.04 cos(x0+x1)
A1 = 0.07 sin(x1) + 0.03 cos(2x0-x1)
A2 = 0.09 cos(x0) + 0.06 sin(x0+x1)
A3 = 0.08 cos(x1) + 0.05 sin(2x0-x1).
```

The link phases are exact line integrals over the oriented links ending at each
site. The field has nonzero curvature. Fourier decomposition in its two
invariant directions reduces the actual four-dimensional overlap operator to
matrices on `N²` sites, retaining all Wilson and sign-function contributions.
An independent full position-space calculation checks that reduction.

The measured coefficient is

```text
β = [t⁴] d/dt log W₊(tA) = 5 [t⁵] log W₊(tA).
```

For the continuum free inverse, put `K=(D0⁺)⁻¹V⁺`, where
`D0⁺(p)=i(p0σ1+p1σ2+p2σ3)-p3 I` and
`V⁺=-i(A0σ1+A1σ2+A2σ3)+A3 I`. Then `β=Tr(K⁵)`.
The Galerkin implementation uses nonwrapping Fourier multiplication, spatial
integer modes `-Kmax,…,Kmax`, and temporal half-integers
`-Kmax-1/2,…,Kmax+1/2`. The fifth-order operator is trace class on this smooth
four-dimensional background. The reported finite-cutoff differences are
convergence diagnostics, without a certified remainder bound.

The lattice coefficient is extracted by a Cauchy sum in complex amplitude.
Backward and forward link factors remain reciprocal under this continuation;
replacing the inverse by complex conjugation would invalidate the extraction.
The calculation differentiates the sign function by its divided differences,
including all link contact terms through the exact operator. Its current is
`Tr[Pminus (dD) D⁻¹]`, the dynamical current in a radial Kato frame.

A polynomial subtraction in amplitude of degree at most four has zero fifth
coefficient. Thus this experiment tests a phase-sensitive term beyond those
subtractions. It does not fix an arbitrary higher-order measure-phase freedom.
For the supplied one-generation hypercharges and multiplicities,

```text
Σ multiplicity × q   = 0
Σ multiplicity × q³  = 0
Σ multiplicity × q⁵  = 4320.
```

The charge-one fifth response therefore scales by 4320 in that supplied
anomaly-free sum. A positive-real replacement of the determinant erases the
imaginary response, while using the opposite chirality reverses it. These
are Taylor coefficients at zero amplitude, not an evaluation of the complete
charged multiplet at unit amplitude. The charge identities do not derive the
representation content from the theory.

The continuum imaginary current coefficient is `9.3176131e-6` at cutoff 32;
its real part is at rounding scale. Selected cutoff values are:

| Continuum cutoff | Imaginary part of β |
|---|---:|
| 8 | 9.0774996e-6 |
| 16 | 9.2693568e-6 |
| 24 | 9.3051203e-6 |
| 32 | 9.3176131e-6 |

The cutoff 24 to 32 change is `1.2493e-8`, about 0.13% of the last value.
The [recorded lattice refinement](data/chiral_curved_response_refinement.json)
gives:

| Lattice side N | Imaginary part of β | Difference from cutoff 32 |
|---|---:|---:|
| 4 | 1.8815783e-5 | 101.9% |
| 6 | 1.8874640e-5 | 102.6% |
| 8 | 1.4852854e-5 | 59.4% |
| 10 | 1.2889865e-5 | 38.3% |
| 12 | 1.1758135e-5 | 26.2% |

The finer grids move toward the reference, but the remaining 26.2% discrepancy
is too large to claim quantitative matching. No extrapolated intercept is
treated as a measured continuum result. The
[comparison figure](results/chiral_continuum_comparison.svg) displays both tests.

The full position-space/reduced-operator current discrepancy is `1.53e-16`
or less at the checked `N=2` field. At `N=4`, changing the Cauchy sum from
12 to 16 angles changes the coefficient by about `7.74e-14`; changing radius
from 1 to 0.7 at 16 angles changes it by less than `4e-16`. These controls
separate extraction error from the much larger discretization effects.

## Remaining measure comparison

The curved refinement computes the **bare dynamical current**, not the completed
cohomology measure of [the finite phase audit](SECOND_COHOMOLOGY_COMPLETION.md).
If the original negative-chirality completed weight is
`Wminus,Kato exp(-i C_a)`, its positive comparator is
`Wplus,Kato exp(+i C_a)`. The fifth current coefficient therefore receives
`5i [t⁵] C_a(tA)`. That contribution must be evaluated or bounded; anomaly
cancellation alone does not set it to zero.

The subsequent [finite completed-phase probe](data/chiral_completed_phase_response.json)
evaluates it on a separate generic `2^4` field. Its fitted correction changes
the fifth imaginary current by approximately 13.5%, with agreement across
amplitude ranges. This confirms the importance of retaining the correction
in the finite calculation. It neither measures the correction on the
two-coordinate refinement field above nor bounds its continuum scaling.

The full matching target is a uniform bound, on a specified invertible smooth
weak-field family and its tangent directions, for the difference of completed
logarithmic derivatives after the permitted local subtractions. A common
reference value and bounded connecting path lengths then control the normalized
log weights by integrating that derivative bound. This requires control of the
measure correction, spectral inverses, and lattice refinement together.
The existing two-dimensional reconstruction note does not establish the
four-dimensional differentiated reconstruction estimates required for a further
comparison through reconstructed gauge fields.

## Reproduction

Run from the repository root with NumPy and SciPy available:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/chiral_continuum_comparison.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/chiral_curved_response.py
lake build UnifiedTheory.Audit.KFCausalChiralContinuumComparison
lake env lean scripts/CheckChiralContinuumComparison.lean
```

The default curved run uses `N=4,6,8` and continuum cutoffs `4,8,12,16`.
Use `--lengths 10 12 --cutoffs 24 32 --jobs 6 --output /tmp/chiral-refinement.json`
for the larger, slower refinements. Independent Cauchy checks use
`--lengths 4 --cutoffs --angles 16 --radius 0.7` with a distinct output path.
The worker option distributes independent Cauchy angles; a serial/parallel
control agrees within `7e-17` at `N=4`.
The refinement record identifies each row's original run and preserves compressed
source snapshots and logs in
[the evidence directory](data/chiral_continuum_comparison_evidence).
Run `python3 scripts/plot_chiral_continuum_comparison.py` to regenerate the figure.
