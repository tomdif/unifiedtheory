# Repo-Wide Breakthrough Search Audit

**Date:** 2026-07-19
**Lean companions:**
`UnifiedTheory/Audit/ThreeDTopologicalBenchmark.lean` and
`UnifiedTheory/Audit/ObservableSeparation.lean` and
`UnifiedTheory/Audit/OrderSensitiveObservables.lean` and
`UnifiedTheory/Audit/KFSpectralCoarseGraining.lean` and
`UnifiedTheory/Audit/KFHigherRank.lean` and
`UnifiedTheory/Audit/KFMultirankCoarseGraining.lean` and
`UnifiedTheory/Audit/KFOrientationDefect.lean` and
`UnifiedTheory/Audit/KFOrientationPathObstruction.lean` and
`UnifiedTheory/Audit/KFOrientationCountertermRigidity.lean` and
`UnifiedTheory/Audit/KFOrientationCouplingFlow.lean` and
`UnifiedTheory/Audit/KFOrientationFiberLaw.lean` and
`UnifiedTheory/Audit/KFOrientationRankTwoFiberLaw.lean` and
`UnifiedTheory/Audit/KFOrientationRankTwoConsequences.lean` and
`UnifiedTheory/Audit/KFOrientationQuantumConsequences.lean` and
`UnifiedTheory/Audit/KFOrientationQuantumZeroMode.lean` and
`UnifiedTheory/Audit/KFOrientationQuantumProjectors.lean` and
`UnifiedTheory/Audit/KFOrientationSpinOne.lean` and
`UnifiedTheory/Audit/KFOrientationSpinOneRelational.lean` and
`UnifiedTheory/Audit/KFOrientationSpinOneGram.lean` and
`UnifiedTheory/Audit/KFOrientationSpinOneHeisenberg.lean` and
`UnifiedTheory/Audit/KFOrientationSpinOneEvolution.lean` and
`UnifiedTheory/Audit/KFOrientationDynamicsCoarseGraining.lean` and
`UnifiedTheory/Audit/KFOrientationCPChannel.lean` and
`UnifiedTheory/Audit/KFOrientationCPChannelComposition.lean`
and `UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`

## Verdict

The search found several constructive connections and repo-wide obstructions that
are stronger than another atomic-number identity:

1. **Constructive:** three-dimensional gravity can have zero local TT modes while a
   flat torus connection retains two distinct, nontrivial, gauge-invariant global
   holonomies.
2. **Obstruction:** several current recovery maps erase the input they are meant to
   probe. The same pattern occurs independently for causal order, continuum scale,
   coupling, and the chamber Poincare action.
3. **Constructive repair:** an order-derived finite signature separates four
   non-isomorphic causal orders and is invariant under every carrier relabeling.
4. **Spectral/coarse repair:** a generic determinant-defined `K_F` now exists on
   arbitrary finite posets, and exact finite order quotients generate nonconstant
   normalized spectral recovery witnesses.
5. **Higher-rank gain and obstruction:** rank two adds signed determinant and shape
   information, but the full symmetrized `K_F` operator is invariant under reversal
   of every causal arrow at every rank, so it cannot recover time orientation.
6. **Operator generation:** joint blocking of the symmetric rank profile and skew
   orientation channel generates a new long-range skew operator not contained in the
   original determinant ansatz.
7. **Covariant memory law:** the generated orientation defect is skew,
   relabeling-covariant, equivalent to failure of closure, and obeys an exact affine
   cocycle law under successive partial blocks.
8. **Fixed-UV path obstruction:** two certified quotient paths with shared endpoints
   transport the same UV orientation operator with strengths `3` and `4`; every
   common nonzero normalization excludes one shared closing IR counterterm.
9. **Semantic rigidity:** preserving the orientation channel's exact forward and
   backward determinant reconstruction forces every additive counterterm to vanish,
   so the generated long-range residual is an independent effective operator.
10. **Fiber-sensitive coupling recurrence:** a uniform two-step chain quotient closes
    exactly with factors `4`, `2`, and composite `8`, whereas a nonuniform `(1,2,3)`
    quotient produces pair couplings `(2,3,6)` that no scalar normalization closes.
11. **Rank-dependent closure:** rank-one transport obeys a general fiber-product law
    and closes on three blocks exactly for uniform fibers, yet the uniform rank-two
    lift generates a new long-range coupling and cannot close under any scalar.
12. **Three-channel completion and tomography:** the general rank-two law splits
    uniquely into native, long-range, and outer-imbalance skew channels that close
    under commutators. Uniform blocking has an exact Mobius composition coordinate;
    cross-rank ratios reconstruct positive fiber profiles, while the characteristic
    polynomial cannot distinguish a profile from its unequal outer reflection.
13. **Conditional quantum closure:** multiplying the skew push by `i` gives an exact
    Hermitian three-level matrix. Uniform scale has a closed beta interpolation, its
    commutator orbit spans all three channels, and every characteristic-polynomial
    functional remains blind to distinct outer-reflected Hamiltonians.
14. **Zero-mode recovery:** the missing reflection information lives in the protected
    zero-mode direction. Reflected Hamiltonians can be isospectral while having
    different kernels; the Casimir is reflection-even and all polynomial dynamics
    reduce to a quadratic representative.
15. **Exact finite unitary evolution:** explicit zero and `±rho` projectors resolve
    the identity and generate a closed propagator satisfying identity, composition,
    unitarity, and exact preservation of the protected zero mode.
16. **Exact spin-one field geometry:** normalized Hermitian generators obey the
    `su(2)` commutators and Casimir `2I`; every profile Hamiltonian is an effective
    field dotted into them, reflection flips one field component, and the
    conditional evolution recurs after `2*pi/rho`.
17. **Relational chirality threshold:** pairwise Hamiltonian traces recover the
    effective-field Gram matrix and remain blind to simultaneous outer reflection,
    while a cubic commutator trace recovers oriented volume, reverses sign, and has
    an explicit nonzero `8i` profile witness.
18. **Exact orientation-bit classification:** commutator strength measures
    cross-product area, cubic chirality squared equals minus four times the Gram
    determinant, and equal pairwise data leave only a `Z2` orientation sign rather
    than any further continuous ambiguity.
19. **Exact Heisenberg mode split:** the Hamiltonian direction is the unique
    conserved linear observable for positive profiles, every transverse observable
    has harmonic generator square `-rho²`, and the full adjoint action closes as
    `L³=-rho²L`.
20. **Exact Rodrigues adjoint flow:** the cubic closure exponentiates to a finite
    trigonometric polynomial with identity, composition, inverse, longitudinal
    conservation, transverse rotation, and exact trace-Gram preservation.
21. **Dynamics/blocking separation:** the globally half-normalized diamond push
    changes orientation trace strength from `4` to `6`; because the Rodrigues
    flow preserves that invariant, the blocking step lies outside every positive-
    profile fixed-Hamiltonian Heisenberg orbit.
22. **Quantum-channel boundary refinement:** per-fiber normalized compression is
    a unital one-Kraus CP channel whose Schwarz defect is exactly a discarded-space
    leakage Gram kernel. The orientation Hamiltonian has zero defect despite
    failing the native coarse ansatz, while a collapsed-chamber coupling has zero
    retained image and nonzero defect. Thus ansatz nonclosure and discarded
    covariance are provably different, and the latter is not recoverable from the
    retained image.
23. **Delayed covariance generation:** a second normalized compression obeys the
    exact channel-defect cocycle. The orientation Hamiltonian has zero first-stage
    defect but nonzero two-stage defect, so multiplicative-domain membership at one
    resolution does not guarantee losslessness at the next. Its full delayed defect
    is the Gram square of one explicit nonzero noise row.
24. **Fallback-free chiral causal dynamics:** the multiplicative quarter-turn
    character has a certified finite zero, but the interacting law
    `lambda^(omega(omega-1)) (±i)^m` is Bell-causal and zero-free on every finite
    parent at the canonical base-two Liouville coupling. It defines a directly
    normalized projective strongly-positive law and recovers the same finite
    orientation endpoint without totalization.
25. **Rank-amplified coupling flow:** the exact effective-pair law multiplies an
    added-ancestor sector by `g^omega`. Exhaustive unlabeled tests through rank six
    and higher-rank random/structured tests show fixed `g>1` concentrating on timid
    growth and fixed `0<=g<1` concentrating on sparse growth. Nontrivial scaling
    requires `g_n -> 1` at logarithmic rate `O(1/n)`, where interference control
    becomes the new obstruction.
26. **Generic zero-freeness survives critical running:** every n-parent
    partition polynomial has degree at most `n(n-1)` and coefficient height at
    most `2^n`; every exact all-rank cancellation coupling lies in a countable
    algebraic exceptional locus. The explicit Liouville-affine schedule remains
    all-parent zero-free while `g_n -> 1` and
    `(n+1)(g_n-1) -> 2(L-1)`.
27. **Transcendence is unnecessary and critical zero-freeness is effective:**
    constant coefficient one forces every rational root of every parent
    polynomial into `[-1,1]`. Hence
    `lambda_n=(n+2)/(n+1)>1` is simultaneously zero-free for every n-parent and
    defines one genuinely rank-dependent projective growth law with
    `g_n -> 1` and `(n+1)(g_n-1) -> 2`. Denominator clearing gives the explicit
    all-parent bounds `|Z_C(lambda_n)| >= (n+1)^(-n(n-1))` and
    `condition(C,lambda_n) <= 2^n (n+2)^(n(n-1))`.
28. **The critical scaling coefficient is a rational modulus, not a prediction:**
    every positive rational `c=a/b` defines a zero-free schedule
    `lambda_n=1+c/(n+1)` with `(n+1)(g_n-1) -> 2a/b`, an effective all-parent
    margin, and a normalized projective strongly-positive cylinder law.
    Kinematics alone therefore leaves `kappa` undetermined.
29. **Coefficient positivity cannot repair the stability bound:** the
    two-antichain parent has real polynomial coefficients `P_0=1` and `P_2=-1`.
    Thus no universal nonnegative-coefficient theorem is possible; finite
    exhaustive data also finds absolute-coefficient nonunimodality by rank six.
30. **Precursor multiplicity changes the critical window:** on an
    `(n+1)`-antichain, the labeled-slot one-missing/timid Born-mass ratio is
    `(n+1)/g_(n+1)^(2n)`, but coherent aggregation to the unlabeled child squares
    the multiplicity and gives `(n+1)^2/g_(n+1)^(2n)`. Every trajectory with finite
    `n log g_(n+1) -> kappa` makes both ratios diverge. Physical unlabeled balance
    therefore needs `2n log g_(n+1)=2log(n+1)+O(1)`.
31. **The corrected window has an explicit zero-free quantum law:** the rational
    harmonic schedule `lambda_n=1+H_n/(2(n-1))` for `n>=2` stays above one,
    converges to one, and is zero-free for every finite parent. Its coherent
    unlabeled antichain ratio converges exactly to `exp(-2gamma)`, and its normalized
    projective infinite-cylinder decoherence functional is strongly positive.
32. **The harmonic closed form is selected by a local refinement law:**
    exchangeability and unit normalization force weight `1/n` on every
    nonempty spectator slot. For the rescaled charge
    `Q_n=2(n-1)(lambda_n-1)`, the rank-local update classifies every trajectory
    as `Q_n=H_n+Q_2-H_2`. Every nonnegative seed has coherent infrared ratio
    `exp(-2(gamma+Q_2-H_2))`, so matching `exp(-2gamma)` selects the unique seed
    `Q_2=H_2=3/2`. The selected law's exact offset is `H_n-log n`, whose limit
    is Euler's constant.
33. **A vacuum-normalized microscopic action removes the seed freedom:** on
    complete unlabeled sequential-growth paths, full event-slot exchangeability
    under every finite permutation (stronger than order covariance) plus unit
    normalization forces the
    newborn contribution `1/(n+1)`. Summing from the empty causet proves
    `Q_n=H_n` on every history, including `Q_2=3/2`, and reconstructs the same
    all-parent zero-free, projective, strongly-positive chiral law with coherent
    limit `exp(-2gamma)`.
34. **One geometric bridge replaces an ad hoc critical schedule:** writing
    causal-set volume as `V_n=n v`, every physical one-element birth adds one
    nonzero cell `v`, and its fraction of the post-birth cosmological-volume
    action is exactly `1/(n+1)`. Identifying the coupling increment with this
    fractional volume increment is an explicit bridge postulate, not an
    arithmetic derivation. Conditional on it, the cell scale, sprinkling density,
    and every nonzero cosmological coupling cancel, selecting one distinguished
    member of the admissible critical family. A complementary no-go proves that
    genuine order-isomorphism covariance allows normalized nonuniform event
    profiles, while a trace-free curvature correction preserves normalization
    and is harmonic exactly when it vanishes pointwise. Finite averaging is the
    unique total-preserving invariant volume projector, and the two-chain
    residual `(-1/6,+1/6)` is reflection odd.
35. **The volume residual extends canonically, but pure chirality does not come
    from it:** at every rank, normalized inclusive-past volume splits uniquely
    into a dual-even shape profile and a dual-odd trace-free orientation profile.
    This is uniqueness relative to the selected geometric profile, not uniqueness
    of the full odd sector: independent inner and outer reflection-odd modes
    already exist at rank four. Reflexivity forces every local geometric
    orientation parameter into `|y|<1/2`, so its balanced kernel genuinely needs
    latent rank two and never reaches a pure chiral endpoint. Balanced unit birth
    dynamics separately forces the quantum lift to `+i` or `-i`; combined order
    and chirality reflection is exact, and reflection-symmetric data cannot choose
    the absolute sign.
36. **Large rank strengthens rather than erases the mixed/pure separation:** an
    `n`-chain has exact profile `y_i=(2i+1-n)/(n(n+1))`, so its extremal event
    tends to zero, and every antichain is exactly centered. More generally every
    event of every finite causet obeys the dynamics-independent bound `|y|<1/4`.
    A one-top causet has `y=n/(2(2n+1)) -> 1/4`, proving the constant optimal but
    leaving a uniform quarter-gap from `+/-1/2`. Every separately normalized
    nonnegative sampling distribution inherits the same mean bound. The critical
    cylinder quantum measure is nonadditive, so defining a unique "typical y"
    still requires an additional sampling or conditioning rule; no such rule can
    violate the pointwise quarter bound.
37. **Geometry has a universal orientation-entropy floor:** the sharp quarter
    band forces both eigenweights of every finite geometric orientation kernel
    into `(1/4,3/4)`. Consequently the best chirality prediction is below `3/4`,
    `det D_y > 3/16`, `Tr(D_y^2) < 5/8`, the latent two-component residual is
    above `3/8`, and the spectral condition number is below `3`. Its binary
    spectral entropy is strictly above `binEntropy(1/4)/log 2`, approximately
    `0.811278` bits. Every scalar-amplitude history kernel has determinant zero,
    so the determinant floor is a basis-invariant uniform separation from the
    entire rank-one class, not merely from the two chiral endpoints. These are
    finite model-internal no-purification results, not a thermodynamic or
    continuum entropy claim.
38. **The missing finite chirality source is the cubic relational
    pseudoscalar:** let `Xi=Im Tr(H1[H2,H3])/8`. For every `Xi != 0`, the
    selector `b=-i sign(Xi)` fixes one of the two dynamically allowed quarter
    turns, the endpoint `y=-sign(Xi)/2`, and the unique admissible minimum of
    `E_Xi(y)=Xi*y`. The selected kernel agrees exactly with the independently
    defined cubic-chirality projector, and inserting its sector into the
    harmonic causal-growth law preserves the proved strongly-positive infinite
    cylinder functional. Reflection sends `Xi` to `-Xi`, conjugates `b`, and
    swaps the endpoint; at `Xi=0`, the energy vanishes for every `y`, proving
    exact nonselection. This closes the finite algebraic sign bridge conditional
    on a nonzero relational triple. It does not yet show that sequential growth
    generates such a triple or transports its sign under refinement.

The second result is the more consequential breakthrough. It gives a single technical
reason why many formally correct “emergence” theorems do not yet recover physics:

> Invariance after erasing the input is not reconstruction. Convergence of a constant
> family is not coarse graining. A trivial symmetry representation is not evidence
> that the correct spacetime representation has emerged.

## Search scope and standard

The repository contains 875 Lean files (874 below `UnifiedTheory/`). The search
indexed the full source inventory and targeted:

- root and capstone claims;
- definitions carrying order, density, coupling, scale, and symmetry inputs;
- `Target`, `open`, `negative`, `vacuous`, and `placeholder` markers;
- the dimension, causal-set, continuum, Wilson, Wightman, topology, and quantum-error-
  correction chains;
- existing discovery and falsification files, to avoid renaming an old identity as a
  new result.

“Breakthrough” here means a new cross-module theorem or a falsifiable consequence of
existing definitions. It does not mean external literature priority, and it excludes
equalities obtained only by unfolding chosen constants.

## Breakthrough 1: local-zero/global-nonzero gravity

`ThreeDTopologicalBenchmark.lean` connects:

- `GravitationalPlaneWaves.ttModeCount 3 = 0`;
- discrete flatness, holonomy, and gauge conjugation from
  `DiscreteBundles` / `DiscreteAmbroseSinger`;
- the two global torus cycles recorded by the finite `ToricCode` combinatorics.

On the one-vertex presentation

```text
pi_1(T^2) = <a, b | a b a^-1 b^-1 = 1>,
```

the new model has identity plaquette holonomy but two independent cycle holonomies in
`Multiplicative (Z x Z)`. Because the group is abelian, the cycle values survive every
vertex gauge transformation.

### Consequence for the dimension argument

The result does not refute four-dimensional spacetime. It does refute the inference
that “zero local graviton polarizations” means “no gravitational content.” Therefore
the graviton lower bound in `DimensionDerived` is a requirement for **local propagating
waves**, not a consequence of requiring gravity in general. The gauge-tracelessness
route to `d = 4` is logically separate and survives this correction.

### Honest limit

This is finite kinematics. It does not construct a physical Hilbert space, quantum
dynamics, a full gauge quotient, or refinement invariance. The toric-code matrix-level
stabilizer, dimension, and distance propositions are still explicit `True` targets;
only their finite combinatorial skeleton is presently proved.

## Breakthrough 2: the input-erasure theorem

The Lean theorem `current_recovery_maps_erase_input` combines three independent
no-go results.

### A. The advertised poset signature does not separate orders

The audit constructs:

- a two-element chain;
- a two-element antichain.

They are proved different because totality holds for the chain and fails for the
antichain. Nevertheless `advertisedPosetSignature` gives them exactly the same value.
In the current `NoBackgroundSpace` definitions:

- `volumeRatio P := P.n` ignores `P.rel`;
- the K/P dimensions use only `P.n`;
- the spectral ratio, weak mixing value, and generation count are constants.

Thus `advertisedPosetSignature_not_injective` is a proved finite counterexample to the
claim that this particular package reconstructs geometry from order.

This does **not** say every operator in the repository is order-blind. In particular,
the `K_F` research branch reports order-dependent spectra.

### A repaired order-sensitive benchmark

`OrderSensitiveObservables.lean` now closes the finite separation gate using only
data computed from `FinPoset.rel`. On four equal-cardinality orders, its signature

```text
(event count, strict pairs, links, open-interval mass, height, width)
```

evaluates exactly to:

| Order | Signature |
|---|---|
| Antichain | `(4, 0, 0, 0, 1, 4)` |
| Two disjoint 2-chains | `(4, 2, 2, 0, 2, 2)` |
| Causal diamond | `(4, 5, 4, 2, 3, 2)` |
| Total chain | `(4, 6, 3, 4, 4, 1)` |

Lean proves all six pairs distinct. More importantly, it proves
`orderSignature_relabel` for **every** finite poset and every permutation of its
carrier. The proof transports pairs, intervals, chain subsets, and antichain subsets
through explicit equivalences; it is not a finite enumeration of labels.

This is a genuine repair of the exact chain/antichain counterexample, but it is not
yet a continuum reconstruction.

### Generic `K_F`, an exact spectral gate, and its limitation

`LayerB/KFFinitePoset.lean` now closes the missing API problem. For every finite poset
and chamber rank it defines the chamber carrier, the zeta block, and the full
determinant expression

```text
K_F(A,B) = det zeta[A,B] + det zeta[B,A] - delta(A,B).
```

Its rank-one specialization yields the exact normalized second moment
`Tr(K_F^2)/n^2`. On the four preregistered orders the values are:

| Order | `Tr(K_F^2)/n^2` |
|---|---:|
| Antichain | `1/4` |
| Two disjoint 2-chains | `1/2` |
| Causal diamond | `7/8` |
| Total chain | `1` |

Thus one spectral coordinate separates all six benchmark pairs, and Lean proves it
is invariant under arbitrary relabelings of every finite carrier.

The same formalization proves a stronger generic no-go theorem. Under order duality,
each zeta block becomes the transpose of the oppositely ordered block. Determinants
are transpose-invariant and the definition adds the two directions, so

```text
K_F^(r)(dual P) = K_F^(r)(P)
```

for every finite poset and every chamber rank. The diamond and its dual disagree on
an oriented causal question while having exactly the same full operator at all ranks.
Higher rank alone therefore cannot recover causal orientation. The formalization now
supplies the minimal algebraic repair rather than merely naming it: the complementary

```text
A_F^(r)(A,B) = det zeta[A,B] - det zeta[B,A]
```

is skew-symmetric and changes sign under order duality. Moreover, `K_F`, the diagonal
correction, and `A_F` reconstruct each directed determinant exactly by half-sum and
half-difference. On two explicit diamond chambers, `A_F` changes from `1` to `-1`
after order reversal. The loss of orientation is therefore localized precisely to
discarding this antisymmetric channel.

### Exact rank-two result: new shape information

`Audit/KFHigherRank.lean` enumerates the six two-event chambers and derives the full
`6 x 6` determinant matrices directly from the generic API. The normalized moments
are:

| Order | Rank one | Rank two |
|---|---:|---:|
| Antichain | `1/4` | `1/6` |
| Two disjoint 2-chains | `1/2` | `4/9` |
| Causal diamond | `7/8` | `13/18` |
| Total chain | `1` | `2/3` |

Rank two again separates all six pairs, but it is not a rescaled version of rank one.
The diamond matrix contains exact `-1` entries from determinant interference, and the
diamond/total-chain ordering reverses: the chain is larger at rank one, while the
diamond is larger at rank two. This proves that higher chambers add genuine order-
shape information even though the symmetrization erases orientation at every rank.

### First nonconstant finite coarse-graining witness

`KFSpectralCoarseGraining.lean` defines certified order quotients. A four-event
diamond with moment `7/8` and a five-event layered order with moment `21/25` are
microscopically distinct, yet each quotients exactly to the same three-event chain
with moment `1`. Their scale-zero/positive-scale flows are nonconstant and converge
to that common value.

This closes the repository's minimal `IRObservableFlow.IsNontrivialRecoveryWitness`
gate with a state that actually changes. It is still only a one-step finite quotient:
the samples are hand-built layered orders, not formalized Poisson draws, and the
result is not an RG fixed point, ensemble universality, or a continuum theorem.

### Joint multirank/orientation blocking generates a new operator

`Audit/KFMultirankCoarseGraining.lean` tracks both repaired sectors through the exact
diamond-to-three-chain quotient. The symmetric profile changes as

```text
(M_1, M_2): (7/8, 13/18) -> (1, 7/9)
```

The exact increment is `(1/8, 1/18)`. Equivalently, rank one would require a
multiplicative factor `8/7`, while rank two would require `14/13`. Lean therefore
proves that the symmetric profile does not close on one common multiplicative
coupling. It becomes constant at the coarse value after the blocking step.

For the skew sector, fine two-event chambers are mapped to coarse chambers when their
event images remain distinct; the collapsed chamber is discarded. Summing the full
fine skew matrix over these fibers gives

```text
push(A_fine) = 2 A_coarse + A_generated,
```

where the surviving chamber fibers have nonuniform sizes `(2,1,2)`. The factor two
is fixed by matching the adjacent coarse entries, and

```text
A_generated = [[0,0, 2],
               [0,0, 0],
               [-2,0,0]].
```

After that normalization, a unit long-range coupling remains between coarse chambers
`01` and `12`. Lean proves this residual is nonzero and therefore proves that the
single skew determinant ansatz is not closed under this blocking rule.

This is the most RG-like result presently available in the branch: the symmetric
ranks run differently, and coarse graining generates a skew operator that was absent
from the starting basis. It is still a finite one-step theorem. Calling it an RG flow
requires concrete compatible quotient sequences and determining whether the enlarged
couplings approach fixed data.

### The orientation defect is a covariant coarse-graining cocycle

`Audit/KFOrientationDefect.lean` abstracts the generated residual. For a partial
block map `f`, normalization `α`, fine orientation matrix `A₀`, and recomputed coarse
matrix `A₁`, define

```text
Ω(f; α; A₀, A₁) = α push_f(A₀) - A₁.
```

Lean proves four structural facts. `Ω` is skew whenever both endpoint orientation
operators are skew. It vanishes exactly when normalized transport closes on the
recomputed coarse ansatz. It transforms by matrix reindexing under arbitrary changes
of fine and coarse chamber labels, so nonvanishing is coordinate-independent. Most
importantly, successive partial blocks satisfy the exact affine cocycle law

```text
Ω(g ∘ f; αβ; A₀, A₂)
  = β push_g(Ω(f; α; A₀, A₁)) + Ω(g; β; A₁, A₂).
```

Thus the extra orientation term has a compositional coarse-graining law. The diamond
calculation is an exact nonzero instance, with `Ω` equal to the unit long-range skew
operator. This alone is not a nontrivial cohomology class: unrestricted counterterms
can choose the negative native operator at every object and erase the entire sector.
A meaningful obstruction requires a normalization condition or a restricted
counterterm class.

### Fixed UV data produce an exact two-path obstruction

`Audit/KFOrientationPathObstruction.lean` supplies the missing path comparison. It
constructs two certified total-order quotient paths

```text
chain₄ -> chain₃ -> chain₂
```

with composite endpoint fiber sizes `(1,3)` and `(2,2)`. At rank one, the same fixed
UV orientation matrix pushes forward to `3 A₂` along the first path and `4 A₂` along
the second. For a common normalization `w`, their endpoint defects are

```text
Ω₁₃(w) = (3w - 1) A₂,
Ω₂₂(w) = (4w - 1) A₂.
```

Their difference is `-w A₂`, so Lean proves it is nonzero for every `w ≠ 0`. A single
IR counterterm subtracts the same matrix from both defects and therefore cannot make
both vanish. This proves path-dependent effective orientation at fixed microscopic
normalization. It does not prove obstruction against arbitrary UV redefinitions;
the same module proves that unrestricted endpoint counterterms trivialize every
defect by erasing both native operators.

### Directed reconstruction rigidly fixes the orientation channel

`Audit/KFOrientationCountertermRigidity.lean` supplies a nontrivial admissibility
condition. A counterterm `C` is reconstruction-preserving when replacing the native
orientation matrix `A` by `A + C`, while leaving symmetric `K_F` unchanged, still
reconstructs both directed zeta determinants exactly. Lean proves

```text
preserves directed reconstruction(C)  <->  C = 0.
```

The proof is algebraic rigidity: the native symmetric/orientation pair already fixes
each forward determinant, so any added matrix entry would change it by `C/2` and the
backward determinant by `-C/2`. The unit long-range diamond residual is nonzero and
therefore fails this admissibility condition. It cannot be absorbed into the native
orientation channel without redefining the directed observable itself.

This turns operator generation into a sharper statement: within the repo's exact
determinant-reconstruction semantics, the residual is an independent effective
operator rather than a renormalization convention. The conclusion would no longer
apply if the coarse theory were allowed to redefine `K_F` or the target directed
determinants simultaneously.

### Uniform fibers close; nonuniform fibers split the coupling

`Audit/KFOrientationCouplingFlow.lean` gives the first exact coupling recurrence
across two successive certified quotient steps. For the rank-one orientation matrix
on a six-event total chain, the block with three fibers of size two satisfies

```text
push₆→₃(A₆) = 4 A₃.
```

The next certified block has fiber sizes `(1,2)` and satisfies

```text
push₃→₂(A₃) = 2 A₂,
push₆→₂(A₆) = 8 A₂.
```

Thus the normalized defects vanish at weights `1/4`, `1/2`, and `1/8`; the
composite normalization is exactly the product of the step normalizations. This is
a genuine two-step recurrence, not merely two unrelated endpoint calculations.

The same six-chain also admits a certified quotient with fiber profile `(1,2,3)`.
Its pushed orientation matrix has upper-triangular pair couplings `(2,3,6)`. The
first two entries alone would require simultaneously `2w = 1` and `3w = 1`, so Lean
proves the orientation defect is nonzero for every rational scalar `w`.

`Audit/KFOrientationFiberLaw.lean` now promotes this clue to a general rank-one
theorem. For any finite total-order carriers and any block map whose lower fibers
precede its higher fibers,

```text
push(A)(a,b) = |f⁻¹(a)| |f⁻¹(b)| A_coarse(a,b).
```

For every surjective quotient onto three coarse blocks, Lean proves an exact iff:
some scalar normalization closes the orientation matrix precisely when all three
fiber cardinalities are equal. The result covers arbitrary fine cardinality and
arbitrary ordered three-block profiles, rather than just the six-event examples.

The same theorem certifies a three-arrow path

```text
chain₁₂ -> chain₆ -> chain₃ -> chain₂
```

with step factors `4`, `4`, and `2`, composite factor `32`, and vanishing composite
defect at normalization `1/32`.

### Rank-one closure does not lift to rank two

The rank-two calculation in `Audit/KFOrientationFiberLaw.lean` supplies the sharper
surprise. Lift the uniform `(2,2,2)` six-to-three event quotient to the fifteen
two-event chambers. Three within-fiber chambers collapse and each surviving coarse
chamber has four preimages. Despite that perfect chamber-fiber uniformity, exact
determinant transport gives

```text
push(A₂) = 12 A₂,coarse + [[0,0, 4],
                           [0,0, 0],
                           [-4,0,0]].
```

The native adjacent entries fix a would-be normalization to `1/12`, while the
coarse long-range entry is zero and the pushed one is `4`. Lean therefore proves
that no rational scalar closes the rank-two channel.

This separates two mechanisms that the earlier benchmark could not distinguish.
Fiber inhomogeneity causes coupling splitting already at rank one, but determinant
interlacing causes operator generation at rank two even with homogeneous fibers.
Consequently a closed event-level flow is not evidence that the multirank theory is
closed.

`Audit/KFOrientationRankTwoFiberLaw.lean` now turns the rank-two example into a
parametric theorem. For three consecutive event fibers of positive sizes `(p,q,r)`,
the exact upper chamber couplings `(01→02, 01→12, 02→12)` are

```text
(p q r (p+1)/2,  p q r (q-1)/2,  p q r (r+1)/2).
```

The adjacent entries count weakly ordered pairs in the shared outer fibers. The
generated long-range entry counts strictly ordered pairs erased inside the middle
fiber. The file proves this directly from the native two-by-two determinant and
checks that `(p,q,r)=(2,2,2)` reproduces the independent fifteen-chamber matrix
above.

This gives two exact classifications. Rank-two scalar closure holds iff the middle
fiber is a singleton and the outer fibers agree (`q=1`, `p=r`). Rank-one closure
holds iff all three fibers agree. Even allowing an independent normalization at
each rank, both conditions hold only for `(1,1,1)`. Thus no genuine ordered
three-block quotient is closed on the simultaneous rank-one/rank-two orientation
ansatz. For uniform size `s`, the generated-to-adjacent ratio is exactly
`1 - 2/(s+1)`, so the extra operator approaches equal strength rather than being
suppressed at large fiber size. Enlarged-basis recurrence beyond rank two remains
an open target.

### Consequences: closed channel algebra, tomography, and a spectral blind spot

`Audit/KFOrientationRankTwoConsequences.lean` decomposes every parametric push as

```text
P(p,q,r) = α A + β B + γ C,
α = pqr(p+r+2)/4,
β = pqr(q-1)/2,
γ = pqr(p-r)/4,
```

where `A` is the native adjacent channel, `B` the generated long-range channel,
and `C` the outer-fiber imbalance channel. Their matrix commutators close exactly:
`[A,B]=C`, `[B,C]=A`, and `[C,A]=2B`. The coordinates are unique. For every uniform
fiber size `s>1`, the native matrix and the pushed matrix recover `B`; their
commutator recovers `C`. Thus the smallest commutator-closed rational matrix space
seen by a nontrivial uniform rank-two push is already the full three-dimensional
skew channel space. This is an operator-algebra statement, not an identification
of a physical gauge group.

The uniform generated/native ratio has the exact coordinate
`u_s=(s-1)/(s+1)`. Multiplication of fiber sizes becomes Mobius addition,
`u_(st)=(u_s+u_t)/(1+u_s u_t)`, while `(1+u_s)/(1-u_s)=s`; over the reals its
rapidity is `log(s)/2`. This supplies an exact semigroup coordinate for uniform
finite blocking, but does not by itself supply a dynamical RG trajectory.

The multirank data are also tomographic. Dividing each rank-two coupling by the
rank-one coupling on the complementary edge gives
`p(p+1)/2`, `q(q-1)/2`, and `r(r+1)/2`. Lean proves this signature injective on
positive triples and proves the corresponding odd-square certificates
`(2p+1)^2`, `(2q-1)^2`, `(2r+1)^2`. Thus the combined ranks recover information
that either normalized scalar summary can discard.

There is a complementary limit: a three-by-three skew matrix with upper couplings
`(x,y,z)` has characteristic polynomial
`X^3 + (x^2+y^2+z^2)X`. Swapping the outer fibers sends `γ` to `-γ`, so unequal
profiles `(p,q,r)` and `(r,q,p)` are distinct orientation matrices with identical
characteristic polynomials. Spectrum-only coarse observables therefore lose a
certified reflection-sensitive channel even after the operator basis is enlarged.

### Conditional quantum lift: exact closure without overclaiming dynamics

`Audit/KFOrientationQuantumConsequences.lean` proves that the finite matrix
`H(p,q,r)=iP(p,q,r)` is Hermitian. Its characteristic polynomial has the form
`X³-rho²X`, hence the exact roots `0,+rho,-rho`. For uniform size `s`,

```text
rho² = s⁶(3s²+2s+3)/4.
```

After normalizing by the adjacent coupling, the radius is `rho_norm²=2+u_s²`.
The natural real interpolation
`u(ell)=(exp(ell)-1)/(exp(ell)+1)` recovers `u_s` at `ell=log(s)`, satisfies
`du/dell=(1-u²)/2`, and tends to `1`. This is an exact interpolation of the finite
uniform semigroup, not evidence that a physical RG equation has been derived.

There is nevertheless a genuine operator-closure result. For every `s>1`, start
with the native channel `A` and commute repeatedly with the pushed matrix `P_s`.
The three matrices `A`, `[P_s,A]`, and `[P_s,[P_s,A]]` span every rational
three-by-three skew channel. Thus a commutator-based dynamics using this generator
cannot consistently retain only the original one- or two-channel ansatz, although
the enlarged three-channel truncation is exactly closed in this finite sector.

The spectral obstruction also survives quantization. Lean quantifies over every
function `F : Polynomial ℂ → X` and proves that `F(charpoly H)` assigns the same
value to outer-reflected profiles. When the outer fibers differ, the Hamiltonian
matrices themselves are proved unequal. Therefore no characteristic-polynomial-only
action, amplitude, or summary can reconstruct this orientation channel. A physical
interpretation would still require a causal-order state space, inner product or
quantum measure, constraint algebra, and continuum dynamics; none is supplied here.

### The spectral blind spot is stored in the protected zero mode

`Audit/KFOrientationQuantumZeroMode.lean` gives the exact zero eigenvector of the
generic three-channel Hamiltonian:

```text
v₀(x,y,z) = (z, -y, x),        H(x,y,z) v₀ = 0.
```

For a fiber profile this becomes `(right coupling, -long coupling, left coupling)`.
Its endpoint asymmetry is

```text
v₀[2] - v₀[0] = left - right = 2 gamma,
```

where `gamma` is the outer-imbalance coordinate. For positive profiles it is nonzero
exactly when `p ≠ r`. Thus the sign erased by the characteristic polynomial is not
lost from the operator: it is encoded in the direction of the protected zero mode.

This distinction is basis-independent at the kernel level. If `p ≠ r`, Lean proves
that the zero mode of `H(p,q,r)` is not annihilated by `H(r,q,p)`, and consequently
the two kernel sets are unequal even though their characteristic polynomials agree.
The minimal repair for a spectrum-only observable is therefore an eigenspace- or
projector-sensitive observable.

The same file proves `H³=rho²H` and
`trace(H²)/2=rho²`. The latter Casimir remains invariant under outer reflection,
precisely matching the information retained by the spectrum. Every polynomial
observable `f(H)` has an exactly equal representative of degree below three, so this
finite Hamiltonian algebra does not proliferate indefinitely. The zero eigenvalue is
an algebraic consequence of this odd-dimensional skew sector, not evidence for a
continuum graviton.

### Exact spectral resolution and conditional unitary dynamics

`Audit/KFOrientationQuantumProjectors.lean` upgrades the three characteristic roots
to three explicit spectral projectors. For every positive fiber profile, the
projectors `P₀`, `P₊`, and `P₋` are Hermitian and idempotent, all mixed products
vanish, and

```text
P₀ + P₊ + P₋ = 1,
H P₀ = 0,     H P₊ = rho P₊,     H P₋ = -rho P₋.
```

The zero projector is the stationary sector identified by the previous kernel
theorem. The positive and negative projectors resolve the two gapped levels. This
is a full finite spectral decomposition rather than a statement that three numbers
are roots of the characteristic polynomial.

The same algebra yields the closed propagator

```text
U(t) = P₀ + cos(rho t) Q - i sin(rho t) J,
```

where `Q=P₊+P₋` and `J=P₊-P₋`. Lean proves

```text
U(0)=1,
U(t+u)=U(t)U(u),
U(t)ᴴU(t)=1,
U(t)v₀=v₀.
```

Thus the enlarged three-channel sector supports an exact finite unitary one-parameter
evolution and a protected stationary state once `H=iP` is selected as generator.
The selection remains conditional: the repository still has no quantum measure over
causal orders, Hamiltonian constraint, gauge reduction, or continuum recovery theorem.

### Exact spin-one representation and effective-field geometry

`Audit/KFOrientationSpinOne.lean` proves that the enlarged three-channel sector is
not merely a generic three-level Hermitian matrix. Its normalized generators obey

```text
[J₁,J₂]=iJ₃,   [J₂,J₃]=iJ₁,   [J₃,J₁]=iJ₂,
J₁²+J₂²+J₃²=2I.
```

The Casimir value `2=1(1+1)` identifies the exact three-dimensional spin-one
representation. Every fiber profile has the decomposition

```text
H(p,q,r) = B₁J₁ + B₂J₂ + B₃J₃,
B = (sqrt(2) alpha, beta, sqrt(2) gamma),   |B|²=rho².
```

This gives a geometric interpretation of the earlier spectral result: the two
gapped eigenvalues are the signed field magnitude and the protected zero mode is
the longitudinally neutral level of this representation. Outer-fiber reflection
acts as `B₃ -> -B₃` while preserving `|B|`; thus the charpoly blind spot is exactly
a field-axis reflection, not an accidental polynomial coincidence. Uniform profiles
lie in the plane `B₃=0` with direction `(sqrt(2),u_s,0)`.

For positive fibers, Lean also proves the exact recurrence

```text
U(t + 2*pi/rho) = U(t).
```

This is a useful representation-theoretic compression of the finite sector. It
does not identify the matrices with physical particle spin, a graviton polarization,
spatial rotations, or the gauge group of a continuum quantum-gravity theory.

### Pairwise Gram data are blind; cubic chirality detects orientation

`Audit/KFOrientationSpinOneRelational.lean` turns the effective field into
basis-independent relational matrix observables. For three fields `A`, `B`, and `C`,
Lean proves

```text
trace(H_A H_B)       = 2 A·B,
trace(H_A[H_B,H_C])  = 2i A·(B×C).
```

The first identity says that pairwise trace measurements reconstruct the Gram data:
field lengths and mutual inner products. But Gram data determine a configuration
only up to an orthogonal transformation, so they cannot distinguish a configuration
from its mirror. The repo now proves this obstruction directly: simultaneous
outer-fiber reflection preserves every pairwise overlap.

The second identity supplies exactly the missing orientation datum. The scalar
triple product is a pseudoscalar, and the corresponding cubic trace changes sign
under the same reflection. In channel coordinates it is

```text
trace(H_A[H_B,H_C]) = 4i det[(alpha,beta,gamma)_A;
                             (alpha,beta,gamma)_B;
                             (alpha,beta,gamma)_C].
```

This is not only a symbolic possibility. The three profiles
`(1,1,1)`, `(2,2,2)`, and `(2,1,1)` have cubic trace `8i`; their simultaneous
reflection has `-8i`, while all six pairwise Gram entries are unchanged. Conversely,
every triple confined to the uniform profile family has zero chirality because its
fields remain in the plane `B3=0`.

The novel finite conclusion is precise: pairwise relational geometry recovers shape
but not handedness; a three-operator commutator observable suffices to recover the
missing orientation. No theorem yet promotes this finite pseudoscalar to a continuum
volume form, parity-violating interaction, or quantum-gravity observable.

### The missing relational datum is exactly one orientation bit

`Audit/KFOrientationSpinOneGram.lean` proves that the preceding hierarchy is not
only qualitative. The commutator norm is the effective-field area invariant:

```text
trace([H_A,H_B]²) = -2 |A×B|²
                      = -2 (|A|²|B|²-(A·B)²).
```

Thus two linear observables commute exactly when their cross-product area vanishes.
Noncommutativity in this closed spin-one sector has a precise relational geometric
meaning: it measures failure of the two effective directions to be collinear.

For three fields, Lean proves the Gram identity

```text
[A·(B×C)]² = det Gram(A,B,C),
trace(H_A[H_B,H_C])² = -4 det Gram(A,B,C).
```

The determinant is built entirely from the six pairwise dot products. Hence the
complete pairwise trace data determine the absolute magnitude of cubic chirality.
A general theorem proves that any two triples with identical pairwise Gram data
have cubic scalar values that are either equal or negatives of one another. For a
nondegenerate triple the unresolved datum is therefore exactly a `Z2` orientation
choice. Simultaneous outer reflection realizes the opposite choice.

The existing profile witness has Gram determinant `16`, chirality `±8i`, and
chirality square `-64`. Every all-uniform triple has zero Gram determinant, so its
orientation bit collapses at the coplanar locus. This distinguishes a discrete
orientation sector from the continuous metric data without introducing background
coordinates. A continuum metric, area/volume spectrum, or dynamical parity sector
is still not derived.

### The Heisenberg sector is one stationary mode plus one oscillator plane

`Audit/KFOrientationSpinOneHeisenberg.lean` converts the cross-product algebra into
an exact statement about conditional quantum dynamics. With

```text
L_H(X) = i[H,X],
```

the double commutator and vector triple-product identity give

```text
L_H²(X) = -|B|² X + (B·X) H.
```

The second term is the longitudinal projection. If `X` is transverse to the
effective field, it vanishes and

```text
L_H²(X) = -rho² X.
```

Thus the transverse linear observable plane has an exact harmonic generator with
frequency `rho`. The longitudinal Hamiltonian direction is stationary. For every
positive fiber profile, Lean proves the converse as well: a linear spin-one
observable commutes with `H` if and only if its field coordinates are a scalar
multiple of `B`. There are no additional conserved linear directions.

Without imposing transversality, the entire linear sector satisfies

```text
L_H³ = -rho² L_H.
```

This is the adjoint analogue of the earlier Hamiltonian cubic relation and is the
algebraic mechanism behind the exact trigonometric recurrence: the finite sector
splits into one zero-frequency longitudinal mode and one two-dimensional oscillator
plane. It still does not establish that this chosen generator is the Hamiltonian of
quantum spacetime or connect its parameter to physical proper time.

### Exact time evolution cannot absorb the generated coarse operator

`Audit/KFOrientationSpinOneEvolution.lean` exponentiates the cubic adjoint closure
without an infinite series:

```text
R_t(X) = X + sin(rho t)/rho L_H(X)
           + (1-cos(rho t))/rho² L_H²(X).
```

Lean proves the exact group and inverse laws, fixes the Hamiltonian direction,
reduces transverse motion to a cosine-sine rotation, and proves

```text
trace(R_t(X) R_t(Y)) = trace(XY).
```

`Audit/KFOrientationDynamicsCoarseGraining.lean` applies this invariant to the
diamond quotient. The native recomputed chain channel Hermitianizes to the field
`(sqrt(2),0,0)` and has `trace(H²)=4`. Normalized blocking generates the long-range
edge, giving field `(sqrt(2),1,0)` and `trace(H²)=6`. Hence, for every positive
profile and time, the latter cannot be the Heisenberg evolution of the former.

This proves a structural distinction inside the finite model: reversible dynamics
moves along a fixed trace-Gram orbit, whereas coarse graining changes the orbit by
generating a new operator. It does not yet prove an iterated RG semigroup or a
continuum fixed point.

The normalization and comparison class matter. The `4 -> 6` theorem concerns the
globally half-normalized push compared with the independently recomputed native
coarse operator. It is not, by itself, a Kadison–Schwarz defect statement.

### The unital channel separates ansatz nonclosure from discarded covariance

`Audit/KFOrientationCPChannel.lean` replaces global normalization with normalized
fiber-indicator columns `V` and defines the observable compression

```text
Phi(A) = V† A V,                 V† V = I.
```

Lean certifies its one-Kraus form, unitality, star preservation, and positivity.
Writing `Q=I-VV†` and `L(A)=QAV`, it proves the exact operator identity

```text
D(A,B) = Phi(A†B) - Phi(A)† Phi(B) = L(A)† L(B).
```

Therefore `D(A,A)` is positive semidefinite, and for Hermitian `A` the equality
`D(A,A)=0` is exactly multiplicative-domain membership. Membership is not merely a
label: Lean derives `Phi(AB)=Phi(A)Phi(B)` and `Phi(BA)=Phi(B)Phi(A)` for every `B`.
The stronger finite-family theorem is also proved: for arbitrary retained operator
coefficients `C_i`,

```text
sum_ij C_i† D(A_i,A_j) C_j
  = (sum_i L(A_i) C_i)† (sum_i L(A_i) C_i) >= 0.
```

This is the complete-positive-definite operator-kernel condition, not just diagonal
positivity.

The diamond orientation Hamiltonian lies exactly on this boundary. Its leakage and
defect vanish, but `Phi(H)` differs from both the native coarse ansatz and the global
half-push. The generated ansatz residual therefore cannot be identified with the CP
covariance defect. Conversely, the Hermitian coupling between a surviving chamber
and the collapsed chamber obeys

```text
Phi(C) = 0,                      D(C,C) = diag(0,1,0) != 0.
```

Thus `0` and `C` have the same retained image and different defects. This is the
precise relative-independence result: discarded covariance is new data relative to
the retained algebra, not an absolutely new degree of freedom in a Stinespring
dilation. The audit packages ansatz closure and multiplicative-domain membership as
two gates and proves logical independence in both directions with these witnesses.
It further proves that no function from retained matrices to coarse matrices can
return `D(A,A)` for every fine `A`. No environment state, physical causal-set
channel, iterated RG flow, or continuum limit is supplied here.

### Schwarz covariance has an exact two-scale cocycle

`Audit/KFOrientationCPChannelComposition.lean` adds a second normalized block
channel `Psi : M_3(C) → M_2(C)` and proves

```text
D_(Psi∘Phi)(A,B) = Psi(D_Phi(A,B)) + D_Psi(Phi(A),Phi(B)).
```

The two summands have distinct meanings: covariance already discarded at the first
scale is transported forward, while the second term is newly generated by the next
projection. For the diamond orientation Hamiltonian the first term vanishes, but
the second-stage defect has `(0,0)` entry exactly `2`. Hence the composed defect is
nonzero. More sharply, Lean computes

```text
D_2 = [[2, 1-sqrt(2)],
       [1-sqrt(2), (3-2sqrt(2))/2]] = R†R
```

for one explicit nonzero `1×2` row `R`. The delayed covariance is therefore a
single discarded noise mode in this benchmark. Passing the multiplicative-domain
gate is local to a chosen channel and scale; it is not hereditary under arbitrary
further unital CP compressions. This is a chosen two-step finite block, not a
derived RG trajectory.

### Arbitrary finite towers expose a protected sector and binary path holonomy

`Audit/KFOrientationCPChannelTower.lean` packages every normalized column
isometry as a unital one-Kraus compression and allows matrix size to vary along
an arbitrary finite path. Its main telescoping theorem identifies the total
Schwarz defect with the recursively transported covariance generated at each
stage. The all-scale protected predicate requires multiplicative-domain
membership of every successive retained image; the concrete orientation
Hamiltonian passes this predicate for the first block and fails it for the
two-block path.

For two paths with common endpoints, the file defines defect curvature and proves
its antisymmetry, triangle identity, and postcomposition law. The pre-existing
rational chain-four quotient paths then supply a separate exact finite witness:
their defects differ by `-A_2`, one native orientation unit. Multiplication by
`i` produces

```text
H_curv = [[0, -i],
          [i,  0]],
```

exactly Pauli Y. Lean proves `H_curv²=I`, `trace(H_curv)=0`, and constructs two
complementary orthogonal trace-one projectors with eigenvalues `+1` and `-1`.
This is new finite evidence that path-dependent loss can organize into a binary
orientation sector. It does not identify a physical qubit, fermion chirality,
gauge field, or continuum holonomy: the rational quotient pushes are not the CP
channels, and no physical path-selection or refinement measure is supplied.

### The path holonomy closes to a finite spinor sector

`Audit/KFOrientationPathQuantum.lean` tests the strongest quantum interpretation
that follows from the two-path matrix alone. The two quotient routes become an
orthonormal basis, while the `+/-` curvature eigenvectors are
`(1,+i)/sqrt(2)` and `(1,-i)/sqrt(2)`. The bases are mutually unbiased: either
definite route gives probability `1/2` for both orientation signs, while either
orientation eigenstate is deterministic in its own basis.

The novel discriminator is not a path probability. Both orientation projectors
have the same real decoherence kernel and hence the same real quantum measure for
every subset of the two histories. Their only difference is the sign of the
imaginary off-diagonal entry. Route dephasing therefore sends both to `I/2` and
destroys orientation. Any microscopic promotion must retain complex inter-history
coherence; a classical stochastic growth law or diagonal history measure cannot
encode this finite sign by itself.

The operator algebra closes completely. Route is Pauli `Z`, curvature is Pauli
`Y`, their commutator generates Pauli `X`, and every complex `2x2` operator has an
explicit decomposition in this basis. The half-scaled generators satisfy `su(2)`
with Casimir `3/4 I`. Curvature-generated transport is an exact one-parameter
unitary group. In spin-half parameterization a `2*pi` rotation negates every ket
but fixes every density matrix, and `4*pi` returns the ket. The independently
derived cubic relational chirality selects the positive projector on the explicit
witness and the negative projector after reflection.

`Audit/KFOrientationHistoryRigidity.lean` then performs the proposed rigidity
test. The kinematic axioms do not force `+/-i/2`. Every strongly positive balanced
normalized kernel has one unique coordinate

```text
D_y = [[1/2,  i y],
       [-i y, 1/2]],       |y| <= 1/2,
```

and equals `(1/2-y)P_+ + (1/2+y)P_-`. Reflection sends `y` to `-y`. The midpoint
`y=0` is an explicit admissible counterexample to phase uniqueness. However, Lean
proves that the complete interval has identical real route-event (`Z`-sector)
measures and dephases
to `I/2`. It
also proves the exact selection theorem: purity, convex extremality, deterministic
curvature outcome, and endpoint saturation are equivalent, and the independent cubic chirality
witnesses select those two endpoints. The finite kinematics therefore determines
the allowed interval and its geometrically distinguished extremes, while leaving
the actual extremal selection to microdynamics or refinement covariance.

`Audit/KFOrientationHistoryRefinement.lean` isolates the structural law
`y⋆z=2yz`. `Audit/KFOrientationHistoryRefinementChannel.lean` now realizes it
with a four-Kraus CPTP measure-and-prepare map and proves exactly
`Phi(D_y ⊗ D_z)=D_(2yz)`. The map is associative and reflection-equivariant on
balanced inputs. More strongly, any complex-linear map with the same four pure
endpoint parity outputs must agree on the entire balanced product sector. Every
nonzero interior `y` therefore contracts strictly under self-refinement, and
`(1/2)(2y)^n` converges to zero; only `y=+/-1/2` has stable nonzero magnitude.

This is now a physical finite quantum channel rather than a bare composition
postulate. It is still not a causal-set refinement theorem: the remaining task is
to derive this channel (or a symmetry-equivalent one) from unlabeled causal growth
and a strongly positive microscopic decoherence functional.

This is a finite algebraic spinor sector, not a derivation of a particle. The
remaining promotion contract is explicit: construct quantum causal histories,
derive their complex amplitudes from microscopic dynamics, select a physical
time/refinement parameter, prove refinement stability, derive rather than label
the chirality coupling, and identify a continuum observable.

### B. The chamber Poincare action is not faithful

`Clay_W1_ContinuousPoincare.discretePoincareChamber` ignores its Poincare parameter and
returns the identity operator. The audit constructs a nonzero unit translation and
proves that it acts exactly like the identity. Hence the representation is not
injective.

A trivial representation can be correct for a scalar or invariant subsector. It
cannot, by itself, demonstrate that the repository has recovered the transformation
law of spacetime fields. The next test must include relational observables on which at
least some translations, rotations, or boosts act nontrivially.

### C. The structural continuum maps have no flow

The audit proves:

- `massGapAtDensity` has no density dependence;
- `physicalWilsonExpectation` has no density dependence;
- `physicalWilsonExpectation` has no coupling dependence.

These are stronger scope statements than merely observing that a `Tendsto` proof is
easy: they prove that no pair of parameter values can be distinguished by the current
functions.

## The new design rule

Before promoting a recovery result, require the relevant map to pass a separation
gate appropriate to its role:

| Claimed recovery | Minimum non-degeneracy gate |
|---|---|
| Geometry from order | Distinct benchmark orders differ on at least one declared observable |
| Renormalization flow | At least one effective observable changes at finite scale before converging |
| Coupled dynamics | At least one physical expectation changes with the coupling |
| Spacetime covariance | The tested sector contains observables with a nontrivial symmetry action |
| 2+1D gravity | Local modes vanish while quotient-level global observables survive |

Injectivity is not required for every physical observable, and universal quantities
may legitimately be constant. The gate applies when a map is cited as evidence that
the corresponding input structure has been reconstructed.

## Candidates rejected as breakthroughs

- More identities among `{2, 3, 4, 5, 7}`: the repo already proves that the atomic
  algebra generically fills small integers and is not Lie-selective.
- A quantum toric-code/3D-gravity identification: the full matrix and dynamics targets
  are not yet constructed.
- Bare `K_F -> J_4` infrared recovery: the recorded T11 experiment is negative for the
  tested direct identification.
- Trivial `True` targets and existential witnesses of the form `exists y, y = f x`:
  these certify consistency or typing, not a new physical consequence.

## Highest-value next theorem

The finite tower, binary holonomy, complete path-spinor algebra, and strongly
positive two-history kernel classification are now closed. Positivity alone has
been proved insufficient to select the extremal phase. Multiplicative normalized
coherence now has a CPTP realization, a covariant causal ordinal composition on
the order-isomorphism quotient, exact quotient-level associativity, a
multiplicative `Z_2` orientation character, and a reversible microscopic dilation
deriving all four endpoint amplitudes. The finite associator instance of quantum
sequential growth is now also closed: two distinct complete binary refinement
trees with the same unlabeled endpoint carry a normalized amplitude-Gram
decoherence functional, strongly positive on arbitrary finite route-events. The
microscopic dilation generates its route amplitudes, and its restriction is the
proved imaginary orientation kernel and CPTP ordinal-refinement output.

The projective-limit algebra is now closed for arbitrary finite branching.
Normalized complex local transition amplitudes generate compatible functionals
at all finite depths; exact marginal consistency holds across arbitrary gaps;
and refinement-equivalent finite presentations quotient to events on infinite
streams carrying a normalized strongly positive cylinder functional. Its
quantum measure is nonnegative and grade-two, and the binary orientation
instance recovers the finite kernel exactly.

The causal branch input is now constructed in
`UnifiedTheory/Audit/KFCausalSetSequentialGrowth.lean`. The fixed-alphabet theorem
has been upgraded to rank-dependent finite branching; causal orders at every
cardinality are quotiented by order isomorphism; and physical children are
exactly maximal-element births. Every parent has a finite nonempty unlabeled
successor set. A uniform real law supplies an unconditional normalized,
all-depth projective, strongly positive infinite-cylinder functional and assigns
zero amplitude to nonphysical histories.

The next load-bearing construction is now phase dynamics. The formalized complex
weight contract shows that any supported prefix-dependent weights with nonzero
local partition sum inherit the full projective theory. Projectivity and label
covariance therefore do not select the weights: causal microdynamics must force a
nontrivial phase and prove that its finite restriction is the orientation kernel.

That finite restriction is now explicit in
`UnifiedTheory/Audit/KFCausalSetOrientationRestriction.lean`. Any exhaustive,
disjoint two-sector partition of finite causet cylinders induces a strongly
positive `2 x 2` kernel. If balanced, it is one unique `D_y`. The new rank-one
theorem then uses the actual scalar-amplitude construction rather than strong
positivity alone: the induced determinant vanishes identically, so balance
forces `|y| = 1/2` and one of the two orientation projectors. Lean also proves
that full-preimage projective refinement leaves the selected matrix and `y`
exactly invariant for every number of steps. Purity selects the endpoint;
projectivity stabilizes it.

That precursor-resolved object is now constructed. Every downward-closed past
set of a labeled parent is a distinct transition slot, its maximal birth is a
certified child, and parent relabelings act by target-preserving equivalences.
The cardinality of each target fiber descends to the unlabeled link as the
Rideout--Sorkin multiplicity. Lean proves the weighted Markov sum is exactly the
raw precursor sum and certifies a link of multiplicity at least two above the
two-antichain.
The uniform baseline has consequently been corrected: uniformity over raw
slots induces child weights proportional to multiplicity.

`UnifiedTheory/Audit/KFCausalSetBellCausality.lean` supplies the missing canonical
spectator deletion by restricting a precursor pair to its union. It proves that
both ancestor number and maximal-element number survive, hence the complete
Rideout--Sorkin `(omega,m)` signature is unchanged. Complex amplitudes are now
defined on raw edges with explicit relabeling covariance; amplitudes landing at
one unlabeled child add coherently and the normalized child sum is one whenever
the partition amplitude is nonzero.

The zero-safe cross-multiplied Bell equation yields a negative classification
result: every complex `(omega,m)` weight is Bell-causal after spectator deletion,
and the ancestor-local subfamily is an injective copy of `ℕ → ℂ`. Bell causality
therefore does not choose a unique dynamics or the endpoint sign. The remaining
physics is a further microscopic principle selecting one amplitude law. If an
interior balanced kernel is physically required, the current scalar-amplitude
outer-product ansatz must itself be generalized.

The first additional principle has now been tested rather than assumed to be
decisive. Independent-composition locality forces
`w(omega,m)=a^omega b^m`, but leaves the two complex generator amplitudes free.
Fixing `a=1` as the ancestor gauge and `b=+/-i` as a chirality-aligned
maximal-event quarter turn then gives a unique reflected pair of Bell-causal
characters. Reflection conjugates the characters and swaps them. The exact
`C_8 ⊕ A_6` cancellation then proves that this fixed ancestor-gauge character
cannot be the complete globally normalized law; it does not classify every
other choice in the two-coupling family.

`UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean` supplies and certifies a
specific interacting completion:

```text
A(omega,m) = lambda^(omega(omega-1)) (±i)^m,
lambda = liouvilleNumber 2.
```

The pair exponent vanishes for zero and one ancestor, so the elementary birth
and its pure `D_(+/-1/2)` restriction are unchanged. It obeys the exact
composition-defect law

```text
A(sigma_1 + sigma_2)
  = A(sigma_1) A(sigma_2) lambda^(2 omega_1 omega_2),
```

and is therefore genuinely interacting, while remaining signature-local,
label-covariant, and zero-safe Bell-causal. The central all-rank proof associates
an integer polynomial to every finite parent. Its value at `lambda` is the real
raw partition, and its constant coefficient is exactly one: the empty precursor
contributes one, every singleton contributes a purely imaginary quarter turn,
and every larger precursor carries a positive pair exponent. Transcendence of
the base-two Liouville number then forbids a zero at every finite parent without
enumeration. Direct coherent normalization consequently produces a fallback-free
unlabeled law with exact projectivity and strong positivity on infinite cylinder
events. The former 14-event obstruction is repaired, and the depth-two endpoint
is exactly the previous chiral kernel.

This closes the mathematical target “construct a normalized complex causal-order
dynamics.” It does not establish that nature selects the Liouville coupling.
In fact the new identifiability theorem sharpens what the parameter means:

```text
omega(omega-1) = 2 choose(omega,2),
g = lambda^2,
A(omega,m) = g^choose(omega,2) (±i)^m.
```

The sign of `lambda` is therefore exact redundancy. Conversely `g` is
injectively recoverable from the raw signature law already at `(omega,m)=(2,0)`;
two `lambda` values define the same law exactly when they are equal up to sign.
All-rank normalizability still fails to select `g`: Lean proves that `g=0`
has parent-partition real part exactly one at every rank, so its sparse
normalized law never uses the totalization fallback, is strongly positive on
the infinite cylinder algebra, and induces the same depth-two pure orientation
endpoint. The theorem `full raw support iff lambda != 0` excludes precisely this
degenerate alternative, but leaves the nonzero value undetermined. This is not
merely a logical possibility: Lean proves `lambda+1` transcendental and
positive, constructs its full-support zero-free normalized growth law, proves
infinite-cylinder strong positivity, recovers the same endpoint, and proves
its raw signature law differs from the canonical one. Thus normalization,
Bell causality, strong positivity, full support, and the endpoint constraint
jointly fail to select the pair coupling. The true remaining derivation is
therefore sharper. The exact theorem
`effectivePairChiralSignatureWeight_append_singleton` says that adding one
ancestor contributes the rank-dependent factor `g^omega`. The reproducible
generalization audit exhausts every unlabeled parent through rank six and tests
random and structured parents through rank sixteen. Every tested fixed `g>1`
concentrates on the full-precursor/timid slot, while fixed `0<=g<1` suppresses
multi-ancestor precursors. To keep adjacent high-ancestor sectors at finite
relative weight requires `(n-1) log g_n = O(1)`, equivalently
`g_n = exp(kappa/(n-1) + o(1/n))`. The tested running trajectory preserves
precursor diversity but increases cancellation sensitivity, reaching a partition
condition number about `652` on the rank-sixteen antichain. The remaining law must
therefore select a stable running coupling, complement symmetry, and the
reflection-odd sign from microphysics, and then show a nontrivial infrared flow
to ordinary QFT/GR.

That adjacent-edge criterion is necessary but not sufficient once sector
degeneracy is counted. `KFCausalSetCriticalMultiplicity.lean` proves that an
`(n+1)`-antichain has one timid precursor and `n+1` one-missing precursors. The
exact incoherent precursor-slot Born-mass ratio is

```text
(one-missing mass)/(timid mass) = (n+1)/g_(n+1)^(2n).
```

The unlabeled transition law instead aggregates those isomorphic slots
coherently before taking the Born square, giving the larger physical ratio
`(n+1)^2/g_(n+1)^(2n)`. It then proves that both ratios tend to infinity whenever
`n log g_(n+1) -> kappa` is finite. In particular, every positive-rational
zero-free trajectory formalized below eventually loses coherent timid balance
on antichains. Holding the unlabeled ratio finite instead requires the corrected
window `2n log g_(n+1)=2log(n+1)+O(1)`. This is not a choice of a better constant
`kappa`; it is a logarithmic change of scaling forced by precursor entropy.

`KFCausalSetMultiplicityCorrectedRunning.lean` closes the corresponding
existence problem. With `H_n` the rational harmonic number, the schedule

```text
lambda_0 = lambda_1 = 2,
lambda_n = 1 + H_n/(2(n-1))  for n >= 2
```

is rational and strictly above one at every rank. It therefore avoids every
parent polynomial zero by the rational-root theorem. Lean proves
`lambda_n -> 1`, bounds the scaled nonlinear error in `log(1+x)`, and derives
the exact coherent limit `(n+1)^2/g_(n+1)^(2n) -> exp(-2gamma)`. The schedule is
then promoted to one normalized projective strongly-positive infinite-cylinder
growth law. The frontier has consequently moved again: kinematic compatibility
is proved.

`KFCausalSetHarmonicRefinementLaw.lean` classifies the remaining closed-form
arbitrariness. It proves that an exchangeable, unit-normalized source on `n`
spectator slots must assign each slot weight `1/n`. Writing
`Q_n=2(n-1)(lambda_n-1)`, the local refinement equation
`Q_(n+1)=Q_n+1/(n+1)` classifies its solutions as
`Q_n=H_n+Q_2-H_2`. The canonical rank-two seed `Q_2=H_2=3/2` recovers the
zero-free harmonic schedule exactly. The same module proves the universality
law

```text
2n(lambda_(n+1)-1)-log(n+1) -> delta,
scaled nonlinear log remainder -> 0
  implies coherent Born ratio -> exp(-2delta).
```

It then discharges the nonlinear-remainder premise for every nonnegative seed,
giving the exact family of limits `exp(-2(gamma+Q_2-H_2))`. Consequently,
matching `exp(-2gamma)` is equivalent to the canonical seed. Its finite-rank
offset is the discrete-continuum spectator entropy anomaly `H_n-log n`, and
Lean proves that this tends to Euler's constant.

`KFCausalSetMicroscopicSpectatorAction.lean` turns the two remaining inputs into
consequences of a single history-level action law. A source is allowed to
depend on the complete unlabeled prefix and child, but must be invariant under
every permutation of the `n+1` event slots and have unit total density.
Permutation transitivity derives exchangeability and forces every slot to
carry `1/(n+1)`. Defining the finite action as the sum of the newborn-slot
density from the empty causet then proves, for every history,

```text
S(empty)=0,
S(path snoc child)=S(path)+1/(n+1),
S(path at depth n)=H_n,
Q_2=H_2=3/2.
```

The reconstructed pair coupling is definitionally connected to the complete
chiral transition-edge dynamics. Lean proves all-parent zero-freeness,
normalization, projective consistency, infinite-cylinder strong positivity,
and coherent limit `exp(-2gamma)` for either chirality. At that stage the open
microscopic question had narrowed to deriving the relabeling-invariant,
unit-normalized spectator-action density from a geometric causal action rather
than postulating that local principle. Subexponential all-parent condition
control also remains open.

`KFCausalSetGeometricVolumeAction.lean` closes that question for the pure volume
sector. Causal-set number-volume assigns `V_n=n v` for an arbitrary nonzero
microscopic cell volume. Every certified one-element growth edge satisfies

```text
V_(n+1)-V_n = v,
(V_(n+1)-V_n)/V_(n+1) = 1/(n+1).
```

The same quotient is unchanged after multiplying the action by any nonzero
cosmological coupling. It is also a direct specialization of the existing
`VolumeFromCounting.volume_ratio_parameter_free` theorem, so the sprinkling
density cancels independently. It therefore constructs the canonical spectator
action and inherits its `Q_n=H_n`, all-parent zero-free, projective,
strongly-positive dynamics. The boundary is also machine-checked. Inclusive
past volume gives an order-isomorphism-covariant, normalized density on the
two-chain with weights `(1/3,2/3)`, disproving the inference from discrete
general covariance to arbitrary slot exchangeability. More generally, a
trace-free curvature correction leaves total density one but reproduces the
uniform volume profile iff it vanishes pointwise. Finite averaging is proved to
be the unique total-preserving map into the fully permutation-invariant volume
sector. On the two-chain the complementary centered profile is exactly
`(-1/6,+1/6)` and reverses sign under endpoint reflection. Thus the remaining
geometric frontier is extending this volume/orientation split to a dynamical
higher-rank curvature channel.

`UnifiedTheory/Audit/KFCausalSetCriticalRunning.lean` closes the qualitative
zero-safe-running part without pretending to select the dynamics. For every
n-event parent it proves

```text
degree P_C <= n(n-1),
|coeff_k P_C| <= #Past(C) <= 2^n.
```

Any exact complex parent cancellation makes `lambda` a root of this nonzero
integer polynomial. Hence every exceptional coupling is algebraic and the
union over all finite parents is countable. This is the correct genericity
statement: cancellation is confined to a countable subset of the algebraic
locus, not asserted at every algebraic coupling. The explicit schedule

```text
lambda_n = 1 + (L-1)/(n+1),
g_n = lambda_n^2
```

keeps every rank transcendental, full-support, and all-parent zero-free while
`g_n -> 1` and `(n+1)(g_n-1) -> 2(L-1)`. Thus critical running does not force a
return to an exceptional coupling at any finite rank.

`UnifiedTheory/Audit/KFCausalSetRationalCriticalRunning.lean` strengthens this
from qualitative genericity to an effective arithmetic theorem. Since every
parent polynomial has integer coefficients and constant coefficient exactly
one, the rational-root theorem puts every rational root in `[-1,1]`. Therefore

```text
lambda_n = (n+2)/(n+1),
g_n = lambda_n^2
```

is full-support and zero-free for every parent at every rank, while `g_n -> 1`
and `(n+1)(g_n-1) -> 2`. It defines a single rank-dependent normalized law,
not merely a family of fixed-rank examples; its finite decoherence functionals
are projectively consistent and its infinite cylinder functional is normalized,
Hermitian, and strongly positive. Denominator clearing also proves

```text
|Z_C(lambda_n)| >= (n+1)^(-n(n-1)),
condition(C,lambda_n) <= 2^n (n+2)^(n(n-1)).
```

The remaining problem is now narrower: the certified condition bound is
superexponential, so one must derive/select the trajectory from microphysics
and obtain subexponential or polynomial stability if a controlled infrared
limit requires it. Transcendence is neither necessary for zero-freeness nor
sufficient for that sharper stability theorem.

`KFCausalSetRationalCriticalFamily.lean` also removes any accidental
interpretation of the representative limit `kappa=2` as a prediction. For
positive `a,b`, the schedule `lambda_n=1+(a/b)/(n+1)` has limit
`(n+1)(g_n-1) -> 2a/b`, remains all-parent zero-free, and supplies a complete
projective strongly-positive law with the denominator-adjusted effective
bounds. Therefore the microscopic dynamics must select `kappa`; the kinematic
axioms do not.

The most direct coefficient shortcut is formally unavailable.
`KFCausalSetPartitionCoefficientStructure.lean` proves that the two-antichain
parent already has coefficients `P_0=1` and `P_2=-1`, hence no universal
real-coefficient positivity theorem exists. In the exhaustive unlabeled census,
317 of 318 rank-six parents have mixed-sign real coefficients and 26 already
violate absolute-coefficient unimodality. A better condition theorem must see
phase pairing, the imaginary coordinate, root geometry, or a dynamically
restricted parent ensemble.
See `CHIRAL_GROWTH_GENERALIZATION_AUDIT.md`.

The higher-rank escape is exact. An explicit two-component amplitude has Gram
kernel `D_y` for every `|y|<=1/2`. Its second latent component has squared weight
`1/2-2y^2`, which vanishes exactly at the endpoints. Strict interior kernels
have positive determinant and are impossible for any scalar amplitude. The
minimal latent rank is therefore one at the endpoints and two in the interior.
Finally, reflection invariance fixes only `y=0`; selecting either endpoint sign
requires a reflection-odd chirality input or spontaneous symmetry breaking.

That target is sharper than merely finding another matrix identity. A diagonal or
real stochastic history law is now formally insufficient because the two sectors
agree on every real route-event measure. Only after the complex phase survives an
iterated, relabeling-covariant refinement system should the model be tested on
formalized sprinkling ensembles and connected to the unresolved `10^41` scale gap.
