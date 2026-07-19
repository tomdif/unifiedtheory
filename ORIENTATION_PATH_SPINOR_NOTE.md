# Orientation as an Imaginary Refinement-Path Phase

## Result

The repository now contains a machine-checked finite synthesis connecting
coarse-graining path dependence, quantum coherence, spin-half algebra, and
relational chirality.

Two exact quotient routes with the same endpoint have an antisymmetric curvature
whose Hermitian representative is

```text
Y = [[0, -i],
     [i,  0]].
```

If the two routes are treated as coherent alternatives, they form the `Z` basis
of a two-dimensional Hilbert space and the two curvature orientations are the
`Y` eigenstates

```text
|+> = (|route 1> + i |route 2>) / sqrt(2),
|-> = (|route 1> - i |route 2>) / sqrt(2).
```

This interpretation is not inserted into the original quotient calculation: the
matrix `Y` and its sign projectors were derived before the Hilbert-space promotion.
The promotion tests exactly what quantum structure that finite result supports.

## What is proved

The path-spinor statements below are theorems in
`UnifiedTheory/Audit/KFOrientationPathQuantum.lean`; the complete strong-positivity
classification is in
`UnifiedTheory/Audit/KFOrientationHistoryRigidity.lean`.

1. The two route kets and the two orientation kets are orthonormal bases.
2. The bases are mutually unbiased. A definite route gives Born weights
   `(1/2,1/2)` for orientation, while an orientation eigenstate has a definite
   sign.
3. Route dephasing maps both orientation states to `I/2`; orientation is lost
   when inter-route coherence is discarded.
4. The real parts of the two complete history kernels agree pointwise. Thus every
   route-event quantum measure is identical in the two sectors.
5. The sectors differ only by the sign of the imaginary off-diagonal history
   amplitude.
6. Route `Z` and curvature `Y` generate coherence `X`. These operators span all
   of `M_2(C)`.
7. The half-scaled generators obey `su(2)` and have Casimir `3/4 I`.
8. Curvature generates an exact unitary one-parameter group that mixes routes and
   preserves both orientation Born weights.
9. In spin-half parameterization, `2*pi` negates every ket but fixes every density
   matrix; `4*pi` returns every ket.
10. An independently derived cubic relational-chirality witness selects the
    positive orientation projector, while its reflection selects the negative
    projector.
11. Every strongly positive balanced normalized kernel is uniquely
    `D_y=[[1/2,iy],[-iy,1/2]]` with `|y|<=1/2`.
12. Every `D_y` is the convex mixture `(1/2-y)P_+ + (1/2+y)P_-`, and reflection
    maps `y` to `-y`.
13. Strong positivity alone does not select the phase: `D_0=I/2` is admissible
    and differs from both projectors. All `D_y` have identical real route-event
    (`Z`-sector) measures
    and dephase to `I/2`.
14. Purity, convex extremality, deterministic curvature orientation, and endpoint
    saturation `y=+/-1/2` are equivalent. Cubic chirality selects these endpoints.

The relevant capstone theorems are:

- `path_holonomy_complementarity`
- `orientation_holonomy_requires_path_coherence`
- `orientation_sign_is_imaginary_history_phase`
- `finite_path_spin_half_algebra`
- `finite_path_spinor_periodicity`
- `holonomyEvolution_isStableTransport`
- `relational_chirality_selects_binary_path_holonomy`
- `admissibleBalancedKernel_iff`
- `admissibleBalancedKernel_unique_parameter`
- `balancedHistoryKernel_endpoint_equivalences`
- `strong_positivity_does_not_select_orientation`
- `balanced_history_rigidity_boundary`
- `multiplicative_refinement_selects_extremal_magnitude`

Their axiom audits contain only the standard Lean foundations used throughout the
repository (`propext`, `Classical.choice`, and `Quot.sound`), with no `sorryAx`.

The endpoint-selection theorem is one four-way characterization:

> algebraic purity ⇔ convex-geometric extremality ⇔ deterministic curvature-basis
> outcome ⇔ selection by the reflected cubic-chirality witness pair.

These criteria arise from algebraic, convex, operational, and geometric directions
respectively; their coincidence is the strongest finite evidence that the
endpoints are physically distinguished rather than merely convenient.

## The new physical idea

The candidate degree of freedom is not a grain of geometry attached to a point.
It is a phase relation between two ways of reaching the same coarse description.
Orientation is invisible to all real route-event measures and becomes visible only
to an operator sensitive to imaginary inter-history coherence.

That suggests a precise working hypothesis:

> A microscopic orientation or spin sector can emerge as a projective phase of
> coherent refinement histories, rather than as a local variable placed on an
> already existing geometry.

The finite algebra has the exact kinematics of a spinor, including the distinction
between `2*pi` periodic observables and `4*pi` periodic state vectors. This is a
novel structural connection inside the repository. It is not yet evidence that an
observed fermion or continuum spin structure has been derived.

## Why a classical growth law is insufficient

A classical stochastic process retains diagonal history probabilities. Here both
orientation signs have the same diagonals. Even allowing the usual real quantum
measure of every two-path event does not help, because the full real kernels agree.
The sign resides in an imaginary off-diagonal entry.

Therefore any microscopic theory intended to reproduce this sector must provide a
complex decoherence functional or an equivalent phase-bearing amplitude law. A
real transition matrix alone cannot distinguish the two orientations in this
benchmark.

Strong positivity narrows but does not remove the ambiguity. The complete
admissible family is the interval `D_y`, `|y|<=1/2`; its midpoint is maximally
mixed and its endpoints are the two pure orientation projectors. A physical theory
must therefore explain not only why the coherence is imaginary, but why its
magnitude saturates the positivity bound.

## Finite quantum-channel refinement

`UnifiedTheory/Audit/KFOrientationHistoryRefinement.lean` formalizes the law
`y⋆z=2yz`. `UnifiedTheory/Audit/KFOrientationHistoryRefinementChannel.lean`
derives it from an explicit four-Kraus CPTP channel:
`Phi(D_y ⊗ D_z)=D_(2yz)`. The channel measures the two curvature signs and
prepares their negative product. It is associative and reflection-equivariant on
balanced inputs. Its four pure-endpoint outputs uniquely fix its action on the
whole balanced product sector. Every nonzero interior value contracts under
self-refinement and repeated identical stages converge to zero; exactly the two
endpoints preserve coherence magnitude.

`UnifiedTheory/Audit/KFOrientationUnlabeledRefinement.lean` now closes the
finite causal and descent algebra. It constructs serial ordinal composition of
finite causal orders, proves that it is covariant under genuine order
isomorphism and associative after quotienting, and descends the concrete
composition to the channel on unlabeled histories. The rescaled orientation sign
is a multiplicative `Z_2` character of this serial causal semigroup: detailed
causal structure remains in the source, while its orientation shadow is abelian.
It also constructs a rectangular Stinespring isometry: the environment
retains one of four orthogonal refinement records, the four input endpoint kets
acquire exactly the required parity outputs, and tracing out that record recovers
the CPTP map.

`UnifiedTheory/Audit/KFOrientationGrowthDecoherence.lean` constructs the finite
associator-sector quantum measure. A complete trajectory is a binary refinement
tree, so the left- and right-associated three-block routes remain distinct even
though they have the same unlabeled endpoint. Their amplitude-Gram decoherence
functional is Hermitian and normalized. Strong positivity holds not only on the
two atomic routes but on arbitrary finite families of finite route-events; every
event quantum measure is nonnegative, the total event has weight one, and the
measure obeys the grade-two sum rule. The
explicit Stinespring isometry generates the route ket with its endpoint-pair
record retained in the environment, and the resulting kernel is exactly the
extremal orientation kernel and reduced CPTP channel output.

`UnifiedTheory/Audit/KFOrientationInfiniteCylinderDecoherence.lean` supplies the
all-depth mathematical completion. For any finite branching alphabet, a complex
transition law whose immediate amplitudes sum to one produces an exactly
projective family at every depth. Quotienting finite cylinder presentations by
refinement gives literal events of infinite branch streams. Their decoherence
functional is normalized, Hermitian, strongly positive for arbitrary finite
event families, finitely additive on common-depth cylinders, and induces a
nonnegative grade-two quantum measure. The binary orientation law differs from
the finite ket only by a global phase and recovers its kernel exactly at depth
one.

`UnifiedTheory/Audit/KFCausalSetSequentialGrowth.lean` now extends this to every
unlabeled causal-set growth path built by maximal-element births. It uses a
rank-dependent tree because the branch type changes with cardinality, quotients
each finite order by isomorphism, proves that every successor set is finite and
nonempty, and constructs a normalized uniform law. Nonphysical prefixes have
zero amplitude, arbitrary-depth marginals agree exactly, and the quotient of
infinite cylinder presentations carries a normalized strongly positive
functional. The remaining bridge is no longer the branch alphabet; it is to
derive nontrivial complex causal weights whose restriction reproduces the
orientation kernel.

That restriction is now an explicit Lean map. A disjoint exhaustive pair of
causet cylinder events induces a `2 x 2` kernel; balanced singleton weights force
it to be a unique `D_y`. Because the causal growth functional is generated by a
single scalar path amplitude, the restricted kernel is an outer product and its
determinant vanishes. Balance therefore forces `|y| = 1/2`: the restriction is
already one of the two pure orientation projectors. Exact projective refinement
leaves that kernel and `y` unchanged through every finite depth. Purity selects
the endpoint; refinement covariance makes the selection stable.

The child-state graph has now been refined to the faithful Rideout--Sorkin
transition fiber. Distinct downward-closed precursor sets remain distinct raw
slots, parent relabelings preserve their unlabeled targets, and target-fiber
cardinality gives a representative-independent Markov multiplicity. The
multiplicity-weighted child sum is exactly the raw precursor sum, including a
certified two-antichain link of multiplicity at least two. The zero-safe complex
ratio now acts on precursor-resolved alternative pairs. Canonical spectator
deletion restricts the parent to the union of those precursors and preserves
both Rideout--Sorkin statistics `(omega,m)`. Covariant raw-edge amplitudes add
coherently over each child fiber and admit normalized child weights.

The Bell classification is non-unique: every complex function of `(omega,m)` is
spectator-independent and zero-safe Bell-causal, and even the ancestor-local
laws contain an injective copy of every sequence `ℕ → ℂ`. Bell causality alone
therefore cannot choose the physical edge law or distinguish the two endpoint
signs. Independent-composition locality sharpens the freedom to exactly two
complex couplings, `w(omega,m)=a^omega b^m`. The minimal chiral boundary law
`a=1`, `b=+/-i` then selects a unique reflected pair of characters, and
reflection conjugates one into the other. What remains is to derive that
quarter-turn birth phase rather than postulate it, and to prove the selected
character induces the matching cylinder-sector sign.

The mixed-state alternative is completely classified at finite rank. Every
allowed `D_y` is the Gram kernel of an explicit two-component amplitude. The
second latent component has squared weight `1/2-2y^2`, vanishes exactly at the
endpoints, and cannot be removed in the strict interior. Thus rank one is
minimal at `|y|=1/2`, rank two is minimal at `|y|<1/2`, and reflection fixes only
the central state `D_0`.

## Falsifiable promotion gates

The finite interpretation should be rejected as physical if any required gate
fails:

1. **Causal child alphabet (closed):** every distinct unlabeled child state
   obtainable by a maximal-element birth lies in a finite, nonempty,
   label-covariant branch type.
2. **Precursor transition fiber (closed):** distinct precursor slots,
   representative-independent multiplicities, the weighted Markov identity,
   and a nontrivial multiplicity benchmark are machine-checked.
3. **Complex Bell causality (closed kinematically, non-unique dynamically):**
   canonical spectator deletion, signature preservation, and the zero-safe
   constraint are machine-checked; the constraint admits an injective
   `ℕ → ℂ` family and therefore does not select a unique law.
4. **Microscopic transition law (candidate classified):** composition reduces
   the law to `a^omega b^m`; elementary relation-complement symmetry derives
   `a=1,b=+/-i`, while normalization alone leaves `b=i t`. A nonzero local
   partition sum invokes the projective theorem automatically, but an explicit
   14-event parent proves that nonvanishing fails globally.
5. **Physical restriction (endpoint magnitude closed):** a balanced
   causal-cylinder partition induces one unique `D_y`, and scalar-amplitude
   purity forces `|y|=1/2`; still derive which sign and parity law the selected
   microdynamics realizes.
6. **Measurable completion (model-dependent):** only if observables beyond the
   cylinder ring are required, prove the vector-measure extension criterion;
   extension is known to fail for some strongly positive quantum measures.
7. **Dynamical selection:** identify whether the unitary parameter is time, scale,
   or neither.
8. **Chirality coupling:** derive the connection to the cubic relational
   pseudoscalar beyond the explicit matching witness.
9. **Continuum observable:** recover a spin structure, fermionic correlation, or
   another independently measurable infrared quantity.

## Highest-value next theorem

The zero-free route is closed negatively: `C_8 ⊕ A_6` is an exact destructive
zero for both chiral characters. The next theorem must therefore classify
zero-safe replacements. A successful law should agree with `(chi i)^m` on
nonzero parents, remain covariant and Bell-causal, and replace the uniform jump
at a zero parent by a projectively stable local dilation or additional latent
channel. It must then prove that the induced two-sector kernel retains the same
chirality endpoint across the zero rather than erasing it.

For the mixed route, lift the scalar projective-growth theorem to
two-component amplitudes and show that vector-valued marginal consistency
preserves the explicit rank-two factor. The finite theorem already fixes the
boundary: **rank-one growth forces pure endpoints; mixed balanced orientation
requires a persistent latent component with weight `1/2-2y^2`**.
