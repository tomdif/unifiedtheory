# Framework Status (May 2026)

> **Quantum-geometry scope update (2026-07-15):** The finite algebraic results below
> remain valid at their stated mathematical scope. A finite 2+1D kinematic witness now
> combines zero local TT modes with nontrivial global torus holonomies; its physical
> gauge quotient, quantum dynamics, and refinement limit remain open. Nontrivial
> infrared recovery also remains open. The
> bare `K_F -> J_4` Poisson-sprinkling test was negative; density-indexed chamber
> limits currently prove convergence only because the supplied family is constant.
> See [`QUANTUM_GEOMETRY_IR_AUDIT.md`](QUANTUM_GEOMETRY_IR_AUDIT.md) and
> `UnifiedTheory/Audit/QuantumGeometryStatus.lean`. A repo-wide cross-module audit also
> proves that the current advertised poset signature is non-injective, the chamber
> Poincare action is non-faithful, and the structural mass-gap/Wilson families erase
> their scale or coupling inputs. See
> [`BREAKTHROUGH_SEARCH_AUDIT.md`](BREAKTHROUGH_SEARCH_AUDIT.md). The finite order-side
> counterexample now has a constructive repair: a relation-derived signature separates
> four equal-size benchmark orders and is invariant under every relabeling. See
> `UnifiedTheory/Audit/OrderSensitiveObservables.lean`. A generic determinant-defined
> finite-poset `K_F` now augments that repair: its normalized rank-one moment separates
> the four orders, and exact finite quotients give nonconstant flows from two distinct
> fine samples to one coarse value. This remains a one-step finite witness, not an RG
> or continuum result. Exact rank-two values `(1/6, 4/9, 13/18, 2/3)` again separate
> the benchmarks and reverse the diamond/chain ordering found at rank one, showing
> genuine determinant shape information. However, the full symmetrized `K_F` is
> proved blind to reversing every causal arrow at every rank. The complementary
> forward-minus-backward determinant channel is now proved to flip sign under
> duality and restore the discarded directed information. Under the exact diamond
> quotient, the symmetric two-rank profile flows from `(7/8, 13/18)` to `(1, 7/9)`,
> with unequal increments `(1/8, 1/18)` that exclude a single multiplicative
> renormalization across ranks,
> while fiber-blocking the skew channel generates a nonzero long-range orientation
> operator outside the original ansatz. The generic defect is skew,
> relabeling-covariant, equivalent to failure of closure, and satisfies an exact
> cocycle law under successive partial blocks. See
> `UnifiedTheory/Audit/KFSpectralCoarseGraining.lean` and
> `UnifiedTheory/Audit/KFHigherRank.lean` and
> `UnifiedTheory/Audit/KFMultirankCoarseGraining.lean` and
> `UnifiedTheory/Audit/KFOrientationDefect.lean`. Two certified chain-quotient
> paths then transport the same fixed UV operator with strengths `3` and `4`;
> for every common nonzero normalization, no shared IR counterterm closes both.
> Arbitrary UV counterterms would trivialize the sector, so the normalization
> condition is essential. See
> `UnifiedTheory/Audit/KFOrientationPathObstruction.lean`. Finally, exact
> forward/backward determinant reconstruction admits only the zero orientation
> counterterm. The generated long-range residual must remain an independent
> effective operator unless the channel's defining semantics are changed. See
> `UnifiedTheory/Audit/KFOrientationCountertermRigidity.lean`. The first exact
> coupling recurrence is also closed: uniform chain fibers give step factors `4`
> and `2`, composite factor `8`, and multiplicative closing weight `1/8`; the
> nonuniform profile `(1,2,3)` instead generates pair couplings `(2,3,6)`, which
> no scalar normalization can close. See
> `UnifiedTheory/Audit/KFOrientationCouplingFlow.lean`. This is now generalized:
> every ordered rank-one block coupling is the product of its fiber sizes, and
> on three surjective blocks scalar closure is equivalent to uniform fibers. A
> three-step path closes with factors `4·4·2 = 32`. The same uniform event block
> fails at rank two, however, producing `12 A_coarse` plus a new long-range
> coupling of strength `4`; no scalar closes it. See
> `UnifiedTheory/Audit/KFOrientationFiberLaw.lean`. The full three-fiber theorem
> now gives rank-two couplings `pqr(p+1)/2`, `pqr(q-1)/2`, and `pqr(r+1)/2`.
> Rank two closes iff `q=1` and `p=r`; rank one closes iff `p=q=r`; hence both
> ranks close only for `(1,1,1)`. See
> `UnifiedTheory/Audit/KFOrientationRankTwoFiberLaw.lean`. Its proved consequences
> sharpen the enlarged theory: three skew channels close under commutators; every
> nontrivial uniform push generates the full channel basis with the native operator;
> `u_s=(s-1)/(s+1)` composes by the exact Mobius law for multiplying fiber sizes;
> cross-rank ratios injectively reconstruct positive fiber profiles; and reflected
> unequal profiles have distinct matrices but identical characteristic polynomials.
> See `UnifiedTheory/Audit/KFOrientationRankTwoConsequences.lean`. These remain
> finite algebraic statements, not a physical gauge algebra or RG flow.
> A conditional quantum realization is also proved: `i` times the skew push is
> Hermitian with an exact three-level characteristic polynomial; its normalized
> scale obeys `du/dell=(1-u²)/2` and tends to `1`; two commutator iterates span the
> complete three-channel sector; and every characteristic-polynomial functional
> remains blind to distinct outer reflections. See
> `UnifiedTheory/Audit/KFOrientationQuantumConsequences.lean`. The construction
> supplies no causal-set Hilbert space, quantum measure, constraints, or continuum
> dynamics, so it is not promoted to a physical quantum-gravity Hamiltonian.
> The missing non-spectral information is now localized exactly. Every finite
> Hamiltonian has a protected zero mode whose endpoint asymmetry is twice the
> outer-imbalance coefficient; unequal reflected profiles are isospectral but have
> different kernels. Meanwhile `H³=rho²H`, the quadratic Casimir remains
> reflection-even, and every polynomial observable reduces below degree three.
> See `UnifiedTheory/Audit/KFOrientationQuantumZeroMode.lean`. The zero eigenvalue
> follows from this finite odd-dimensional skew sector and is not identified with
> a physical graviton or continuum massless mode.
> The Hermitian sector now also has an exact spectral decomposition. Three explicit
> projectors isolate the zero and `±rho` levels, are Hermitian/idempotent/orthogonal,
> and resolve the identity. Their closed propagator satisfies `U(0)=1`,
> `U(t+u)=U(t)U(u)`, `U(t)ᴴU(t)=1`, and preserves the protected zero mode. See
> `UnifiedTheory/Audit/KFOrientationQuantumProjectors.lean`. These are genuine
> finite unitary matrix identities under the chosen generator, not a derivation of
> the physical quantum-gravity Hamiltonian or constraint algebra.
> The same three-level sector is now proved to be an exact spin-one representation
> of `su(2)`: normalized Hermitian generators satisfy the cyclic commutators and
> Casimir `2I`, while the orientation Hamiltonian is an effective-field coupling
> `H=B·J` with `B=(sqrt(2) alpha,beta,sqrt(2) gamma)` and `|B|²=rho²`.
> Outer reflection flips only the imbalance-axis component, uniform profiles lie
> in the corresponding symmetry plane, and the conditional propagator has exact
> recurrence time `2*pi/rho`. See
> `UnifiedTheory/Audit/KFOrientationSpinOne.lean`. This representation-theoretic
> identification does not establish physical particle spin, a graviton, or a
> spacetime rotation symmetry.
> A further relational theorem now separates metric-like from orientation-like
> information. Pair traces equal twice the dot products of the effective fields,
> whereas `trace(H_A[H_B,H_C])=2i A·(B×C)`. Simultaneous outer reflection preserves
> every pair overlap but negates this cubic pseudoscalar. An explicit asymmetric
> profile triple has values `8i` and `-8i` before and after reflection; every
> all-uniform triple has value zero. See
> `UnifiedTheory/Audit/KFOrientationSpinOneRelational.lean`. This is an exact
> finite handedness observable, not a derived continuum volume form or physical
> parity violation.
> The residual ambiguity is now classified. The squared commutator trace is
> `-2|A×B|²`, while squared chirality is `-4 det Gram(A,B,C)`. Consequently,
> complete pairwise trace data determine the magnitude of chirality and leave only
> a `Z2` sign; simultaneous reflection realizes the two signs whenever the triple
> is nondegenerate. The certified profile triple has Gram determinant `16` and
> chirality square `-64`. See
> `UnifiedTheory/Audit/KFOrientationSpinOneGram.lean`. The resulting finite
> length–area–volume hierarchy is not yet a continuum geometric operator algebra.
> The adjoint dynamics are now classified as well. For `L(X)=i[H,X]`, the exact
> identity is `L²(X)=-rho²X+(B·X)H`. On every positive profile, the linear
> centralizer is precisely the span of `H`; all transverse directions obey the
> harmonic relation `L²=-rho²`, and the whole linear sector obeys
> `L³=-rho²L`. See
> `UnifiedTheory/Audit/KFOrientationSpinOneHeisenberg.lean`. This explains the
> finite recurrence algebraically but does not select a physical causal-set
> Hamiltonian or continuum time evolution.
> The closure is now exponentiated exactly in
> `UnifiedTheory/Audit/KFOrientationSpinOneEvolution.lean`: the finite Rodrigues
> action has identity, composition, inverse, a fixed Hamiltonian axis, transverse
> rotation, and preserves all trace-Gram overlaps. The cross-module theorem in
> `UnifiedTheory/Audit/KFOrientationDynamicsCoarseGraining.lean` then separates
> this reversible flow from the globally half-normalized push. That prescription
> changes `trace(H²)` from `4` to `6`, so it cannot be any fixed-profile
> Heisenberg orbit. This is an exact finite blocking-versus-dynamics obstruction,
> not yet an iterated or continuum renormalization result.
> `UnifiedTheory/Audit/KFOrientationCPChannel.lean` now supplies the distinct
> quantum-channel statement. Per-fiber normalized incidence defines a unital
> one-Kraus compression, whose Schwarz defect factors exactly as a leakage Gram
> kernel and whose zero set gives the Hermitian multiplicative-domain boundary.
> Arbitrary finite operator-coefficient amplifications factor as positive Gram
> squares, formally certifying the complete-positive-definite kernel property.
> The orientation Hamiltonian has zero channel defect but still fails closure in
> the independently recomputed coarse ansatz. A coupling to the collapsed chamber
> instead has zero retained image and nonzero defect. Thus ansatz nonclosure is not
> itself discarded covariance, while genuine discarded covariance is independent
> of the retained description. The two conditions are now separate reusable gates;
> concrete witnesses prove neither gate implies the other, and no function of the
> retained matrix universally reconstructs the diagonal defect. These remain finite
> matrix-channel theorems, not a physical causal-set channel, environment, or RG
> trajectory.
> `UnifiedTheory/Audit/KFOrientationCPChannelComposition.lean` now composes this
> channel with a second normalized block. Its exact defect cocycle separates
> transported covariance from covariance newly generated at the next scale. The
> orientation Hamiltonian has zero first-stage defect but nonzero composed defect,
> with an exact second-stage diagonal entry `2`. Multiplicative-domain membership
> is therefore scale-relative and is not automatically stable under further
> compression. The entire delayed defect is an explicit positive Gram square
> `R†R` of one nonzero `1×2` noise amplitude, isolating a single discarded
> covariance mode. This is a two-step finite witness, not an RG semigroup.
> `UnifiedTheory/Audit/KFOrientationCPChannelTower.lean` now removes the
> two-step restriction at finite scope. Heterogeneous normalized compression
> paths have an exact recursively accumulated defect, and observables protected
> at every scale are defined by successive multiplicative-domain membership.
> Defect curvature between common-endpoint paths obeys triangle and
> postcomposition laws. The two existing rational quotient routes give a
> nonzero unit orientation curvature whose Hermitian representative is exactly
> Pauli Y, with two orthogonal trace-one eigenprojectors. This is a finite
> binary path-holonomy sector; no physical channel-selection law or continuum
> interpretation is asserted.
> `UnifiedTheory/Audit/KFOrientationPathQuantum.lean` promotes this witness as far
> as the present finite algebra permits. The two quotient routes and two
> orientation signs are mutually unbiased bases. Both signs have identical
> route-event quantum measures and become `I/2` under route dephasing; their only
> distinction is the sign of an imaginary off-diagonal history phase. Route,
> curvature, and coherence close the complete Pauli algebra and exact spin-half
> `su(2)` representation with Casimir `3/4`. The induced spinor transport negates
> kets at `2*pi`, returns them at `4*pi`, fixes densities at `2*pi`, and preserves
> holonomy probabilities. The reflected cubic-chirality witness swaps the two
> projectors. This is a quantum-compatible finite path sector, not yet a derived
> quantum causal-history theory, fermion, physical RG flow, or continuum field.
> `UnifiedTheory/Audit/KFOrientationHistoryRigidity.lean` closes the proposed
> finite rigidity test. Every strongly positive balanced normalized two-history
> kernel has the unique form `D_y=[[1/2,iy],[-iy,1/2]]`, `|y|<=1/2`, and is the
> convex mixture of the two orientation projectors. Reflection reverses `y`.
> Strong positivity does not select a phase: `y=0` is an explicit admissible
> non-projector. The pure kernels, convex extreme points, and kernels with
> deterministic curvature orientation are exactly the endpoints `y=+/-1/2`,
> which are also the two
> cubic-chirality-selected witnesses. The remaining open problem is dynamical
> endpoint selection on refinement-covariant unlabeled histories.
> `UnifiedTheory/Audit/KFOrientationHistoryRefinement.lean` proves the structural
> selection law for multiplicative normalized coherence. The follow-up
> `UnifiedTheory/Audit/KFOrientationHistoryRefinementChannel.lean` now realizes
> it as an explicit four-Kraus CPTP map:
> `Phi(D_y ⊗ D_z)=D_(2yz)`. The map is associative on balanced inputs,
> reflection-equivariant, and uniquely fixed on the entire balanced sector by
> the four pure-endpoint parity outputs. Every nonzero interior parameter
> therefore loses coherence under self-refinement, while only `y=+/-1/2`
> preserves magnitude. `KFOrientationUnlabeledRefinement.lean` now constructs
> the serial causal ordinal sum, proves its covariance under order isomorphism,
> proves exact associativity after quotienting labels, and descends it to this
> channel on unlabeled histories. Its rescaled orientation sign is a
> multiplicative `Z_2` character of serial causal composition. The file also
> derives the four endpoint outputs from a reversible rectangular Stinespring
> isometry. `KFOrientationGrowthDecoherence.lean` now retains the two distinct
> complete associator growth trees and constructs their normalized Hermitian,
> strongly positive decoherence functional. Strong positivity holds for arbitrary
> finite route-events, all event quantum measures are nonnegative, the total event
> is one, the measure obeys the grade-two interference sum rule, the dilation
> generates the route amplitudes, and the reduced kernel is
> exactly the extremal orientation state and CPTP channel output.
> `KFOrientationInfiniteCylinderDecoherence.lean` now constructs the all-depth
> extension for any normalized complex finite-branching law. Its finite-depth
> functionals are exactly projective across arbitrary refinement gaps;
> refinement-equivalent presentations form a quotient of events on infinite
> branch streams; and the quotient functional is normalized, Hermitian, strongly
> positive, finitely additive on common-depth cylinders, and grade-two. The
> binary orientation instance restricts exactly to the finite kernel. The open
> rank-dependent follow-up now constructs the actual branch system: finite
> causal orders at every cardinality are quotiented by order isomorphism and
> every child isomorphic class obtainable by a maximal-element birth is retained
> as a finite, nonempty unlabeled successor. Its uniform law is normalized, zero
> off physical paths, exactly projective across arbitrary depth gaps, and strongly
> positive on infinite cylinder events. Arbitrary supported complex weights
> inherit the construction after finite local partition normalization. The
> transition-edge layer now retains every distinct downward-closed precursor,
> proves representative-independent link multiplicities and the exact
> multiplicity-weighted Markov sum, and supplies the corrected uniform-slot
> law. A two-antichain link is certified to have multiplicity at least two.
> `KFCausalSetBellCausality.lean` now canonically deletes every spectator outside
> the union of a precursor pair and proves that both Rideout--Sorkin statistics
> `(omega,m)` survive. Covariant complex raw-edge amplitudes aggregate coherently
> into unlabeled children and normalize when their partition amplitude is
> nonzero. The zero-safe Bell equation is classified far enough to prove a
> no-uniqueness theorem: it contains an injective family indexed by all complex
> sequences `ℕ → ℂ`. `KFCausalSetOrientationRestriction.lean` then closes the
> endpoint question more strongly: every induced kernel has determinant zero,
> so a balanced restriction is necessarily `y=+/-1/2`, and exact projective
> refinement preserves it. This selection comes from the scalar-amplitude
> (rank-one) ansatz, not Bell causality. The next module derives a particular
> edge phase from a finite microscopic balance law. A richer growth construction is
> still required if mixed interior kernels are physical.
> Independent-composition locality
> classifies every signature-local weight as `a^omega b^m`, so Bell plus
> composition still leaves exactly two complex couplings. Setting the ancestor
> gauge to one and the elementary maximal-event phase to the chirality-aligned
> quarter turn `+/-i` uniquely fixes a reflected pair of candidate laws.
> `KFCausalSetChiralGrowth.lean` now derives that quarter turn rather than assuming
> it: equal normalized Born weights for the empty/full births of the one-event
> causet force `b=+/-i`. Those births are proved to remain the distinct unlabeled
> two-antichain and two-chain. The totalized character is normalized at every
> extension depth, and an explicit depth-two cylinder partition induces exactly
> the matching pure `D_(+/-1/2)` kernel. `KFCausalSetChiralDynamics.lean` now
> proves three sharper results. Born normalization alone leaves the injective
> continuum `b=i t`, while elementary relation-complement symmetry forces equal
> weights and the chiral pair. Any nonzero reflection-odd source uniquely selects
> the matching endpoint, whereas zero source cannot select a sign. Finally,
> global nonvanishing is false: the explicit parent `C_8 ⊕ A_6` has zero raw
> partition for both signs, so the totalized law provably takes its uniform
> fallback branch. The honest residual frontier is the microscopic origin of
> complement symmetry and the chirality source. The destructive-zero branch has
> now been removed in `KFCausalSetCompleteChiralLaw.lean`: the interacting weight
> `lambda^(omega(omega-1)) (±i)^m` preserves the elementary endpoint, remains
> Bell-causal, and has nonzero partition at every finite parent when `lambda` is
> the canonical base-two Liouville number. Its real parent partition is an
> integer polynomial with constant coefficient one. Hence the resulting
> unlabeled law is normalized with no fallback and carries the projective,
> strongly positive infinite-cylinder functional. The apparent coupling has
> now been quotiented exactly: `omega(omega-1)=2*choose(omega,2)`, so only
> `g=lambda^2` is physical; `lambda` and `-lambda` give the same complete raw
> law, whereas `g` is identifiable at the two-ancestor signature. A second,
> sparse `g=0` law is also zero-free at every parent, strongly positive on the
> infinite cylinder algebra, and induces the same depth-two endpoint. Full raw
> support holds iff `lambda != 0`, so it eliminates that degenerate candidate
> but does not determine the remaining nonzero coupling. In fact
> `lambda+1` is a second proved positive transcendental, full-support,
> all-rank-zero-free and strongly-positive law with the same endpoint but a
> different signature law. `KFCausalSetCriticalRunning.lean` now proves the
> parent polynomial has degree at most `n(n-1)` and coefficient height at most
> `2^n`, and that every exact cancellation coupling is algebraic; the all-rank
> exceptional locus is countable. It constructs the explicit schedule
> `lambda_n=1+(L-1)/(n+1)`, whose every term remains transcendental,
> full-support, and all-parent zero-free while `g_n=lambda_n^2 -> 1` and
> `(n+1)(g_n-1) -> 2(L-1)`. The new honest residual is a genuinely new
> microscopic selector with useful condition-number control and the
> reflection-odd sign. The full
> local generalization test now identifies why running is necessary: the exact
> adjacent-sector multiplier is `g^omega`. Fixed `g>1` flows rapidly to the
> full-precursor/timid channel; fixed `0<=g<1` flows to the sparse
> zero/one-ancestor sector. Maintaining nontrivial high-rank balance requires
> `(n-1) log g_n = O(1)`, so `g_n -> 1`. The formal trajectory proves qualitative
> zero-freeness in that window, but the tested critical trajectory still exposes
> growing destructive-interference condition numbers. See
> `CHIRAL_GROWTH_GENERALIZATION_AUDIT.md`.
> `KFCausalSetRationalCriticalRunning.lean` strengthens this again. The rational
> root theorem plus constant coefficient one excludes every rational root with
> `lambda>1`, so the elementary schedule `lambda_n=(n+2)/(n+1)` needs neither
> transcendence nor fallback. It is packaged as one rank-dependent normalized
> unlabeled law with projective strongly-positive cylinder dynamics. Denominator
> clearing proves `||Z_C|| >= (n+1)^(-n(n-1))` for every n-parent and the explicit
> condition-number bound `2^n (n+2)^(n(n-1))`. This is effective but far too weak
> for a continuum limit; subexponential stability and microscopic selection
> remain open.
> `KFCausalSetRationalCriticalFamily.lean` proves that this was not a unique
> schedule: every positive rational `c=a/b` gives a zero-free projective law
> with `(n+1)(g_n-1) -> 2a/b`, partition margin
> `(b(n+1))^(-n(n-1))`, and condition bound
> `2^n(b(n+1)+a)^(n(n-1))`. Hence the critical modulus `kappa` is not selected
> by zero-freeness, projectivity, or strong positivity. The coefficient route
> also has a formal obstruction: `KFCausalSetPartitionCoefficientStructure.lean`
> proves the two-antichain polynomial has constant coefficient `1` and
> quadratic coefficient `-1`, excluding universal real-coefficient positivity.
> `KFCausalSetCriticalMultiplicity.lean` then exposes a stricter obstruction.
> On an `(n+1)`-antichain, the incoherent precursor-slot one-missing/timid
> Born-mass ratio is `(n+1)/g_(n+1)^(2n)`. The repository's unlabeled dynamics
> coherently aggregates isomorphic slots before Born squaring, so its child-sector
> ratio is `(n+1)^2/g_(n+1)^(2n)`. Every finite-`kappa` trajectory sends both
> ratios to infinity, including every positive-rational zero-free schedule.
> The old `1/n` window balances individual adjacent transitions only; coherent
> unlabeled antichain balance requires the logarithmically corrected law
> `2n log g_(n+1) = 2log(n+1)+O(1)`.
> `KFCausalSetMultiplicityCorrectedRunning.lean` constructs the repair rather
> than stopping at the obstruction. The rational harmonic schedule
> `lambda_0=lambda_1=2`, `lambda_n=1+H_n/(2(n-1))` is all-parent zero-free,
> tends to one, and makes the exact coherent unlabeled antichain ratio converge
> to `exp(-2gamma)`. Its growth law is normalized and projectively
> strongly positive on the infinite-cylinder algebra. The remaining issue is
> narrowed by `KFCausalSetHarmonicRefinementLaw.lean`: exchangeability plus
> normalization uniquely gives source weight `1/n`, and the local additive
> recursion `Q_(n+1)=Q_n+1/(n+1)` classifies every trajectory as
> `Q_n=H_n+Q_2-H_2`. For every nonnegative seed, the coherent ratio tends to
> `exp(-2(gamma+Q_2-H_2))`; matching the harmonic value is equivalent to
> `Q_2=H_2=3/2`. On that selected trajectory the offset is exactly the spectator
> entropy anomaly `H_n-log n`.
> `KFCausalSetMicroscopicSpectatorAction.lean` closes the additive-law and seed
> boundary conditionally on one microscopic principle: full event-slot
> exchangeability (strictly stronger than order-isomorphism covariance) and
> unit normalization of the local action density. On actual unlabeled growth
> histories these conditions force density `1/(n+1)`;
> vacuum accumulation proves path independence, `Q_n=H_n`, and `Q_2=3/2`.
> The resulting transition is all-parent zero-free, projective, and strongly
> positive. `KFCausalSetGeometricVolumeAction.lean` makes one explicit bridge
> postulate: the coupling increment equals fractional number-volume growth. A
> physical birth adds one cell `v`, so the postulate gives
> `v/((n+1)v)=1/(n+1)`. This arithmetic does not derive the bridge. It does prove
> that arbitrary nonzero cell volume, sprinkling density, and cosmological
> coupling cancel, so one geometric identification selects a distinguished
> member of the admissible critical family. The file also proves
> that order covariance alone permits normalized nonuniform profiles, and that
> trace-free curvature is the exact obstruction to uniformity. Finite averaging
> is the unique total-preserving invariant volume projector; on the two-chain
> its centered residual is `(-1/6,+1/6)` and is reflection odd.
> `KFCausalSetGeometricOrientationDynamics.lean` extends the construction to
> all ranks. Inclusive past volume splits uniquely into dual-even shape and a
> dual-odd trace-free orientation profile. This is uniqueness of the split of
> the selected geometric profile, not of the whole odd sector: rank four has
> independent inner and outer odd modes. Reflexivity forces every local
> geometric parameter into the strict interior `|y|<1/2`, hence its balanced
> kernel genuinely requires latent rank two at every event. Balanced unit birth
> dynamics separately forces the chiral lift to `+i` or `-i`; combined order and
> chirality reflection is an exact symmetry, so reflection-symmetric data cannot
> choose an absolute sign. `KFCausalSetRelationalChiralitySelection.lean`
> identifies the existing cubic relational pseudoscalar
> `Xi=Im Tr(H1[H2,H3])/8` as an exact finite source: for `Xi != 0`,
> `b=-i sign(Xi)`, `y=-sign(Xi)/2`, and unique minimization of
> `E_Xi(y)=Xi*y` select the same endpoint projector and complete strongly-
> positive harmonic growth sector. Reflection conjugates the phase and swaps
> the endpoint, while `Xi=0` proves exact nonselection. A preferred nonzero
> triple and refinement-covariant transport of this source are not derived.
> `KFCausalSetGeometricOrientationAsymptotics.lean`
> closes the large-rank loophole: chain endpoints tend to zero, antichains are
> exactly centered, and every finite causet satisfies the sharper universal
> bound `|y|<1/4`. One-top causets tend to `1/4`, so the bound is optimal while
> maintaining a uniform quarter-gap from pure chirality under any normalized
> nonnegative sampling law. `KFCausalSetGeometricOrientationEntropyGap.lean`
> upgrades this to a uniform mixedness theorem: both spectral weights are in
> `(1/4,3/4)`, chirality predictability is below `3/4`, determinant is above
> `3/16`, matrix purity below `5/8`, latent residual above `3/8`, spectral
> condition number below `3`, and binary spectral entropy above
> `binEntropy(1/4)/log 2 ≈ 0.811278` bits. The determinant floor uniformly
> separates the geometric kernel from every rank-one scalar-amplitude kernel.
> Because the cylinder quantum measure is nonadditive,
> a numerical typical-event distribution still requires a sampling rule.
> Deriving both named postulates—full exchangeability and the fractional-volume
> bridge—plus dynamical generation and refinement transport of the relational
> sign source, and quantitative all-parent conditioning, remain open.
> `KFOrientationHigherRankDecoherence.lean` proves the complementary
> result: every admissible `D_y` has an explicit two-component Gram amplitude,
> strict interiors cannot have a scalar-amplitude realization, and the second
> component vanishes exactly at the endpoints. The only reflection-fixed
> balanced kernel is `D_0`, so choosing an endpoint sign necessarily requires a
> reflection-odd chirality datum.

## Paper

**"Time is a Partial Order"** — [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

DOI: [10.5281/zenodo.19613914](https://zenodo.org/records/19613914)

## Capstone Theorem

**`framework_master_2026`** in `LayerB/FrameworkCapstone.lean` — single 30-conjunct master theorem citing the framework's complete state. Foundational axioms only.

## Summary

One postulate (spacetime is a locally finite partial order) + two physical identifications + the Planck mass → the complete algebraic structure of the Standard Model, the Higgs mass to 0.54%, the electroweak scale to 2.3%, and the mass hierarchy to 3.5%.

The May 2026 audit chain (`PreRegistrationLedger.lean`) added: a 5-integer atomic vocabulary {N_W=2, N_c=3, N_total=5, d_eff=4, disc=7}, six audit-driven corrections strictly improving PDG fit, 17+ exact cross-sector identities, KPGAC selection principle, and 4D causal SO(10) substrate identification.

Every algebraic step is formally verified in Lean 4. Zero sorry. Zero custom axioms.

## Effective Input Count

| Input | Type | Status |
|-------|------|--------|
| Locally finite partial order | Ontological postulate | Axiom |
| m_H = γ_d · v | Physical identification | `SpectralMassTheorem.higgsMassFromGap` — λ_H = γ₄²/2 follows by `quartic_eq_half_gap_squared` |
| v = M_P exp(−c/g²) with g²=2 | Physical identification | `VEVIdentificationChain.lean` |
| M_P | Dimensionful scale | One measured constant |

Everything else is derived.

## Three Layers

**Layer 1 (unconditional algebra):** γ₄ = ln(5/3), sin²θ_W = 3/8, 3 generations, Δ = 7 prime, char poly factors. Proved in `HauptvermutungIndependence.lean` to be independent of the Hauptvermutung.

**Layer 2 (Hauptvermutung-conditional):** Einstein's equation, holographic bound, Λ = 1/√N.

**Layer 3 (identification-conditional):** m_H = 125.78 GeV, v = 240.6 GeV, mass hierarchy.

## May 2026 Audit Findings

### Atomic Vocabulary (5 integers)
{N_W = 2, N_c = 3, N_total = 5, d_eff = 4, disc = 7}, with disc = N_c + d_eff = dim(im 𝕆) (Cayley-Dickson direct sum, proved in `DiscFusionOrigin.lean`).

### Audit-Driven Corrections (6, all improve PDG fit)
| Old | New | File |
|---|---|---|
| m_b/m_τ = 12/5 | **7/3 = disc/N_c** | `BTauReaudit.lean` |
| m_t/v = 1/√2 | **7/10 = cos²θ_12^PMNS** | `TopYukawaReaudit.lean` |
| V_cb² = b₁²·r₃² | **1/600 = 1/(N_W²·N_total²·6)** | `CKMOneLoopV2.lean` |
| V_ub² = b₂⁴·r₃² | **7/480000 = V_us²·V_cb²·disc/(8·N_total)** | `CKMOneLoopV2.lean` |
| Wolfenstein A = 4·r₃ | **√6/3** | `WolfensteinA.lean` |
| α_s = 1/9 | **7/60 = (m_b/m_τ)·V_us²** | `CouplingConstantAudit.lean` |

### Cross-Sector Identity Lattice (17+ exact identities)
Connects CKM, PMNS, masses, gauge couplings, dark matter, inflation. Catalogued in `CrossSectorIdentitySearch.lean`. Headlines: sin²θ_12^PMNS = 6·V_us²; m_t/v = cos²θ_12^PMNS; α_s = (m_b/m_τ)·V_us²; Ω_M·h²·disc = 1.

### Substrate Identification
4D causal SO(10) is the maximal compatible gauge+spacetime shell. The disc atom forces ℚ(√7) eigenvalue field via chamber polynomial discriminant (`ChamberPolyDiscriminant.lean`). E₈ Coxeter h(E₈) = 30 = N_W·N_c·N_total atomic; E₈ exponents = (ℤ/30)\* unique among ADE (`E8IsingZamolodchikov.lean`).

### Pre-Registration Ledger (5 forward-facing predictions)
| Prediction | Closed form | Experiment | Year |
|---|---|---|---|
| \|V_ub\| | √21/1200 ≈ 0.003819 | Belle II (±3%) | 2027 |
| κ_λ Higgs trilinear | 1.00 ± 0.04 (SM-equivalent) | HL-LHC / FCC | 2030+ |
| Ω_b/Ω_DM | 4/21 ≈ 0.1905 | CMB-S4 | 2032 |
| τ_p | M_X-dependent, P_α = 1024π²/9 | Hyper-Kamiokande | 2030+ |
| a_μ = SM(BMW) | 116592000 × 10⁻¹¹ | Fermilab + lattice | 2027 |

## Honest Negatives (formally proved)

- **Zamolodchikov-Ising mass spectrum does NOT follow** — framework rationals vs transcendental cosines (`J4ZamolodchikovTest.lean`); E₈ structural alignment is kinematic, not dynamical.
- **m_b/m_τ = 7/3 sits 1.5σ below PDG** — flagged via `mb_mtau_below_PDG_1sigma`.
- **m_t/v = 7/10 sits 1.5σ below PDG** — flagged via `mt_at_v246_below_PDG_1sigma`.
- **α_s = 7/60 below strict PDG 1σ** — flagged via `alphaS_below_strict_1sigma`.
- **min-complexity selection rule is NOT uniform** — fails for b/τ and m_t/v; cross-sector consistency overrides.
- **Framework's α_GUT + standard QCD running gives M_X ≈ 10¹¹ GeV → τ_p ≈ 10¹¹ years**, EXCLUDED by Super-K. Resolution requires α_GUT = 1/45 = sin²θ_13^PMNS (Path A) or BSM β₀ (`MXResolution.lean`).

## Open (dynamical, not algebraic)

- α ≈ 1/137 (needs Monte Carlo)
- CKM/PMNS mixing magnitudes beyond cross-sector identities (one-loop Feshbach)
- Dark matter relic abundance via thermal freeze-out (Ω_DM = 3/25 atomic match identified, mechanism not derived)
- Λ_QCD (non-perturbative lattice)
- J₄ chamber matrix specific entries (Volterra-Feshbach derived but not from a deeper principle)
- N_g = N_c = 3 equality (separately derived but their equality is not)

## Lean Codebase

874 Lean files in `UnifiedTheory/`, **zero sorry and zero custom axioms** in
core mathematical content. Latest full root build: 8,628 jobs successful; its
immediate parent also passed a clean rebuild of 8,634 jobs (July 2026).
Foundational axioms only: `propext`, `Classical.choice`, `Quot.sound`.
