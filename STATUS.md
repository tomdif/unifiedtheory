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
> triple is not derived; the next module settles refinement transport.
> `KFCausalSetChiralityGenerationNoGo.lean` now proves exact transport and a
> matching generation obstruction. The action-derived depth-two cylinder sign
> `Xi_cyl=-2 Im D(0,1)` equals the supplied relational sign and is unchanged by
> every finite projective refinement. However, no reflection-equivariant
> selector can choose a fixed-point-free chirality from the reflection-fixed
> vacuum action; the equal reflected mixture is exactly the strongly-positive
> mixed center `D_0`. The current finite dynamics therefore transports but
> cannot spontaneously generate a preferred sign.
> `KFCausalSetWeakHandednessBridge.lean` turns the transported sign into an
> explicit weak vertex on a correctly factorized Dirac-spinor weak doublet.
> Gamma five acts only on Dirac chirality, while the proved `T+`, `T-`, `T3`
> commutators act only on weak isospin. The unique affine locking law
> `P_weak(Xi)=(1-Xi*gammaFive)/2` gives `P_L` for `Xi=+1` and `P_R` for
> `Xi=-1`. Hence a positive relational branch produces, at every refinement
> depth, a nonzero charged current that annihilates all right Weyl states; the
> negative branch is its exact reflected mirror. This is relational and
> conditional: the current symmetric vacuum still cannot select nonzero `Xi`,
> and the Lorentzian continuum spin/Dirac reconstruction remains open. See
> `WEAK_HANDEDNESS_DERIVATION_AUDIT.md` for the exact claim boundary.
> `KFCausalSetFutureFrequencyHandedness.lean` now gives the finite clock
> construction its decisive reflection stress test. For a fixed oriented
> quotient-curvature operator `H`, `aI+H` is positive semidefinite exactly for
> `a>=1`; zero-ground normalization therefore selects the minimal shift
> `H_plus=1+H=2P_plus`. Its spectrum is nondegenerate, its flow is unitary, and
> both causal routes first orthogonalize at `pi/2`, with
> `path13 -> -i path22`. Reflection gives the equally positive zero-ground
> partner `H_minus=1-H=2P_minus`, the same survival amplitude and minimal time,
> but `path13 -> +i path22`. Both coefficients extend to normalized, strongly
> positive, projectively consistent unlabeled growth laws, transporting
> opposite nonzero cylinder signs through every refinement. Positive frequency,
> positivity, ground-zero normalization, and minimality thus produce a
> reflection doublet rather than an absolute vacuum selection. At this module
> boundary the clock/birth identification is an interpretation map: it names
> the already-selected character as the first orthogonal transition of one
> reflected spectral assignment. It is not used by the finite sign selector.
> The next modules derive the source side of that alignment and then prove the
> residual printed sign is one
> cylinder-operational conjugation gauge orbit. The next response-rigidity
> module proves the mechanism unique inside the minimal affine-local class;
> deriving that class from deeper dynamics and the continuum Lorentzian Dirac
> reconstruction remain open.
> `KFCausalSetGrowthArrowChirality.lean` identifies the process-level datum
> absent from that static test. A sequential-growth edge distinguishes a
> newborn maximal event. Its future incidence volume is exactly `1`, its past
> incidence volume is `1+precursorPopulation`, and its normalized orientation
> source is therefore nonnegative, vanishing exactly on a gregarious birth.
> Every causally linked birth produces a strictly positive order-odd source;
> the order-dual minimal-birth process produces its negative. The first linked
> birth is the canonical two-chain and has source exactly `1/6`. With the
> standard phase response this gives `-i` and the complete projective
> `Xi=+1` transport law, while the all-antichain history remains source-free.
> The residual theorem is equally sharp: complex-conjugate phase responses map
> the same positive source to opposite quarter turns and both are reflection
> covariant. `KFCausalSetConjugationCompleteness.lean` now tests that apparent
> Z2 on the complete constructed theory. Conjugation exchanges the raw edge
> laws, coherent unlabeled aggregation, the provably active zero-partition
> fallback, all finite path/event amplitudes, and the infinite-cylinder
> decoherence functional. It commutes with arbitrary finite refinement and
> fixes every real event quantum measure. The quotient of the two labels is a
> subsingleton, so the cylinder-operational theory contains one conjugation
> gauge orbit rather than two distinguishable absolute signs. Both
> representatives remain normalized, Hermitian, and strongly positive. The
> invariant statement is the growth-arrow/chirality correlation; this is not a
> continuum CP classification. The same module proves that the maximal-birth source is exactly
> the geometric odd residual at the newborn at every rank. The three-chain
> newborn repeats `1/6`, while the rank-three fork gives `1/5`: the source is
> unified, but its magnitude depends on geometry.
> `KFCausalSetMicroscopicResponseLaw.lean` classifies the finite response
> mechanism at a stated hypothesis boundary. For the general energy affine in
> source `Xi` and orientation `y`, combined reflection and zero-source
> neutrality uniquely remove the constant and one-variable terms, leaving
> `E_g(Xi,y)=g Xi y`. A positive effective drive uniquely minimizes at
> `y=-1/2`; a negative drive uniquely minimizes at `y=+1/2`; zero drive has no
> phase. This minimum is an auxiliary optimum on the abstract closed
> positivity interval, not a finite geometric value. The geometric image has
> the rank-uniform bound `|y_geom|<1/4`; the attainment audit now proves it is
> distinct from both endpoints and has strictly greater energy for every
> nonzero drive. Elementary Born normalization plus relation-complement symmetry,
> ancestor gauge, and independent composition classify the corresponding
> signature character as exactly one of the conjugate `+i/-i` pair. The
> explicit sign rule matches a linked source to one member. A new theorem proves
> direct sign matching and variational selection are extensionally equivalent
> on nonzero drive, so the energy is bookkeeping rather than a dynamical flow.
> The conjugation proof is also
> lifted through the newest zero-free harmonic law generated by the microscopic
> spectator action: transitions, paths, events, real measures, arbitrary
> refinements, and infinite-cylinder functionals all commute. Thus an arbitrary
> response table and an observable finite Z2 are eliminated. What remains is
> to derive affine locality and elementary complement symmetry from a deeper
> causal action, not to choose another response function.
> `KFCausalSetSourceMagnitudeDecoherence.lean` gives the source magnitude a
> separate exact role. For the rank-three chain/fork births, source values
> `1/6` and `1/5` give normalized-coherence retention bases `1/3` and `2/5`,
> purities `5/9` and `29/50`, and determinants `2/9` and `21/100`. Conditional
> on a separate multiplicative CP mixing channel, the fork retains more coherence
> at every positive depth. The general law is `r(y)=|2y|`: pure endpoints
> persist, gregarious coherence vanishes after one stage, and every finite
> geometric kernel decays strictly faster than `2^{-n}` to zero. A checked
> `RealizesMultiplicativeSourceMixing` contract now makes the required physical
> channel identification explicit; none of these rates describe projective
> growth without that contract.
> `KFCausalSetSourceQuantumEnsemble.lean` then computes the first exact
> harmonic source profile. Its bin measures sum to `3681/2113` rather than
> one; destructive empty/full interference `-1568/2113` restores normalized
> total measure. A classical expectation therefore needs an extra sampling
> rule; explicit singleton-Born renormalization gives `6082/18405` at this
> rank. `KFCausalSetSourceInterferenceRefinement.lean` proves that exhaustive
> projective continuation cannot supply the missing classicalization: every
> cylinder entry obeys `D(A↑k,B↑k)=D(A,B)` at every depth. Thus nonzero
> off-diagonals are conserved, and any cylinder realization of the local source
> bins keeps `D(0,2)=-784/2113` and pair interference `-1568/2113` forever,
> while the separate multiplicative benchmark predicts zero after one stage.
> An actual CP/environment/record coarse graining is therefore required. The
> same module boundary records that ancestor number is not a sufficient grain:
> one-ancestor births have both source `1/6` and `1/8` depending on context.
> `KFCausalSetSpectatorRecordChannel.lean` then tests canonical record tracing.
> The channel is explicitly CPTP and permutation-covariant and kills the
> empty/full off-diagonal, but cannot preserve decoherence normalization:
> `sum_ij D_ij=1` while `trace D=3681/2113`. Every trace-preserving map with a
> record-diagonal output therefore has total measure `3681/2113`; no standard
> CPTP replacement can repair the conflict. Direct route-record dephasing also
> erases the chiral pair. The remaining target is a growth-compatible
> `D(Omega,Omega)`-preserving conditional expectation/instrument with a derived
> protected chiral algebra, not an ordinary trace-preserving record channel.
> The forced eigenbasis alternative is positive: for
> `D_y=[[1/2,iy],[-iy,1/2]]`, chirality-projector pinching is CPTP, fixes every
> `D_y`, and yields the exact normalized record profile
> `diag(1/2-y,1/2+y)`. Under a separately named source-times-chirality tensor
> ansatz, the chiral cells are exactly decoherent while the geometric
> empty/full entry `-784/2113` persists inside the selected pure cell. This
> conditionally realizes “chirality classical, geometry quantum”; the scalar
> growth theory cannot derive the tensor factor and does not classify all
> higher-rank decoherent partitions. Projectivity only transports a partition already
> proved decoherent at its base cylinder depth.
> `KFCausalSetChiralityRecordCompounding.lean` identifies the interior source's
> exact record observable: chirality probabilities are
> `(1/2-y,1/2+y)`, hence the signed record bias is `2y`. The chain, fork, and
> singleton-antichain biases are `1/3`, `2/5`, and `1/4`. This statistical
> geometric record is not the pure signature character selected by the sign
> response; a theorem now separates those two kernels explicitly. For the
> first two linked chain births, independent records have table
> `(1/9,2/9,2/9,4/9)` and preserve the `2/3` marginal, so independence does not
> amplify handedness. A separately named common-sector transport contract does
> amplify the same pair to `(1/5,4/5)` and induces
> `y boxplus z=(y+z)/(1+4yz)`, or `(r+s)/(1+rs)` in bias coordinates. Repeated
> fixed positive evidence converges to one, while every finite aggregate remains
> strictly below one. This is a conditional odds/rapidity law, not projective
> refinement and not the `2yz` CP benchmark.
> Growth still has to derive the common-sector factorization and establish the
> required product-evidence condition for its varying source sequence. The
> scalar-amplitude route is now excluded below; this requires higher-rank
> transition data rather than another scalar law.
> `KFCausalSetChiralityEvidenceAsymptotics.lean` turns that last condition into
> exact log-odds arithmetic. The additive charge is
> `q(y)=artanh(2y)=1/2 log((1/2+y)/(1/2-y))`; common-sector composition adds
> `q`, so this is binary Bayesian evidence rather than emergent Lorentz
> kinematics. For future-maximal chain growth,
> `y_n=n/((n+1)(n+2))`; its first two values are both `1/6`. Accumulated charge
> lies between one and four shifted harmonic tails. The sharp-rate module now
> telescopes the bias sum and bounds the nonlinear `artanh` excess by a
> summable cubic tail. It proves evidence/log tends to `2`, log-odds/log tends
> to `4`, and log posterior-error/log tends to `-4`, so the conditional error
> is `N^(-4+o(1))`, not `1/N`. The `4` is arithmetic, not dimension: one
> factor `2` comes from the full-chain bias and one from converting additive
> half-log-odds to log-odds.
> A checked positive geometric-
> decay source has summable charge, however. Positivity and a transported sign
> therefore do not prove decisiveness for arbitrary paths, much less a
> quantum-measure typical-history statement. Constructing the necessary
> vector/operator-valued common-sector law and proving the appropriate typical
> divergence theorem remain open.
> `KFCausalSetChiralityEvidenceExtrema.lean` proves the exact rankwise range.
> For an `n`-event parent the source has gregarious minimum `0`, linked minimum
> `1/(n(n+1)+4)` attained by the singleton-bottom precursor in a chain, and
> star maximum `n/(2(2n+1))` attained over the full antichain. The timid
> full-chain source lies strictly inside this range for `n>=2`; thus rankwise
> linked charge spans `O(1/n^2)` through a nonzero limiting constant. The
> extremizers are not asserted to form a projectively compatible history.
> `KFCausalSetChiralityFactorizationNoGo.lean` proves the exact factorization
> obstruction. Every finite-depth scalar growth event kernel has zero
> two-event determinant. Consequently two nonzero cells have nonzero
> cross-decoherence, and projective refinement preserves that interference at
> every later depth. This rules out every nontrivial exactly decoherent binary
> chirality record in the scalar sequential-growth container, even after a
> conserved chirality label is appended to the history alphabet. In
> particular the interior record `diag(1/2-y,1/2+y)` and the first linked-birth
> weights `(1/3,2/3)` are impossible. Latent rank two is already proved both
> sufficient for the balanced kernel and necessary in its strict interior.
> The surviving construction frontier is therefore a projectively consistent
> vector/operator-valued growth law with an orthogonal transported sector.
> `KFCubicMarkedSheetRankTwo.lean` now constructs one concrete finite carrier
> of exactly that minimal rank. Three marked cubic sheets decompose into the
> invariant uniform line plus a canonical zero-sum plane equivalent to
> `C^2`; sheet permutations act isometrically, and its Gram construction is
> strongly positive. The exact witness `diag(2,6)` has determinant `12`, hence
> two nonzero decoherent cells and no scalar-amplitude representation. This is
> an algebraic higher-rank exit, not yet a causal-growth derivation of cubic
> roots, a resultant-one slice, or projective vector-valued dynamics.
> `KFCubicSheetIntrinsicCarrier.lean` upgrades that construction to a
> label-free standard representation. On every abstract three-sheet type the
> canonical vertices `delta_s-1/3` span an exact complex rank-two carrier; the
> normalized Gram matrix is positive semidefinite with entries `1` and
> `-1/2`. Bijections transport vertices isometrically, while the only vector
> invariant under every sheet permutation is zero. A separate theorem proves
> that projectively consistent vector amplitudes with such coordinate transport
> induce Hermitian, normalized, strongly positive, exactly projective event
> kernels. Coarse amplitudes may be arbitrary carrier superpositions rather
> than single-sheet rays. `KFCubicSheetFrameRigidity.lean` proves that the raw
> vertices resolve the identity, the normalized vertices average to the
> positive maximally mixed state `I/2`, and their rescaled rank-one operators
> form a positive three-outcome POVM. Direct `S_3` commutant rigidity makes
> `I/2` the unique fully symmetric unit-frame-trace operator. A
> fixed-point-free monodromy loop also obstructs every transported global
> deterministic sheet marking. What remains open is not the carrier,
> projective implication, state, or measurement, but a nontrivial equivariant
> causal transfer law `K_e : W(S_h) -> W(S_h')`.
> `KFCubicTwistedTransfer.lean` formalizes that law as an interface. Complex
> edge weights and child-to-parent sheet bijections define `T_W`; every
> nonzero eigen-section of `T_W` obeys the transported branch-sum identity at
> one and all finite exhaustive depths. A unit-norm parent then carries a
> normalized Hermitian strongly positive branch functional. Local sheet
> gauges conjugate `T_W`, preserve the eigen-section equation, and leave its
> Gram kernel invariant. `CAUSAL_CUBIC_TRANSFER_BRIDGE_AUDIT.md` records the
> source-level boundary: the neighboring causal-algebraic repo currently has
> an allowed-transition relation, branching counts, and diagonal interval
> projectors, but no derived cubic sheet functor, `S_3` edge transport, complex
> transfer eigenpair, or theorem identifying its spectral state with this
> growth operator.
> `KFCausalProduct3SheetBridge.lean` now supplies the exact finite candidate
> for the sheet functor. The order atoms of the elementary Boolean tangent
> cube are canonically three primitive directions, and restriction to atoms
> classifies every cube order automorphism uniquely as an `S3` permutation,
> compatibly with composition. The trace-free projection of directional birth
> incidence is equivariant and gives `v_s` for one active direction,
> `-v_missing` for two, and zero for isotropic zero/three-direction births.
> These chart automorphisms instantiate the twisted-transfer interface. The
> remaining bridge is now the existence and nontrivial gluing of locally
> unlabeled three-product charts on actual causal/CSpec states, plus spectral
> selection of a nonzero twisted eigen-section; a globally labeled fixed grid
> gives only gauge-trivial transport.
> `KFCausalDiamondDirectionCover.lean` now reconstructs local directions
> without coordinates: Hasse cover edges are quotiented by opposite sides of
> commuting diamonds. On the Boolean tangent cube this quotient is exactly
> three-element, order isomorphisms transport it functorially, and unequal
> same-endpoint path transports obstruct any global labeling.
> `KFCausalSheetConnectionLaplacian.lean` proves the exact reversible
> connection-energy identity, identifies the Laplacian kernel with parallel
> sections, and proves that full `S3` holonomy plus positive connectivity
> makes the kernel trivial and every nonzero field's energy positive.
> `KFCausalSheetHolonomyWitness.lean` realizes that hypothesis on a connected
> four-state regular Boolean-chart complex: two triangle loops carry the
> adjacent transpositions, six explicit loop words exhaust `S3`, and the
> twisted kernel is therefore unconditionally trivial for this example.
> `KFCausalCSpecSheetRealization.lean` now uses the pinned native
> causal-algebraic-geometry definitions to construct the Boolean cube causal
> scheme, prove its three atom directions are distinct genuine `CSpec` points,
> and transport them through the witnessed overlaps and six loops with exactly
> the expected full `S3` action. This closes local causal/CSpec realization.
> The same module proves a sharp no-go for the naive global candidate: the two
> middle events of a four-event causal diamond have identical strict futures,
> so its canonical principal-point map into `CSpec` is not injective.
> It remains qualitative and atlas-relative: one global `CSpec` has not been
> proved to generate the four-state gluing, no numerical gap is bounded, and
> no simple lowest eigenline or canonical ground projector is selected.
> `KFCausalSetChiralityChargePartitionNoGo.lean` checks the missing probability
> license at the first nontrivial rank and returns a no-go. The three charges
> above the two-antichain are distinct, yet both ordered threshold cuts have
> nonzero cross-decoherence; the exact empty/full entry is `-784/2113`.
> Projective continuation preserves the obstruction for every cylinder
> realization. Finite charge concentration therefore already needs the
> protected record factorization, while the infinite divergence tail event is
> not evaluated by the cylinder functional supplied here.
> `KFCausalSetPostulateFootprint.lean` certifies the
> transitive dependency partition at build time: finite selection and abstract
> transport avoid clock, exchangeability, and volume bridges; the concrete
> harmonic action uses exchangeability; volume supplies its interpretation;
> clock evolution and the weak map occur only in the handedness layer.
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
> Deriving full exchangeability, the fractional-volume bridge, affine-local
> response encoding, and elementary complement symmetry, plus obtaining
> quantitative all-parent conditioning, remain open. The absolute printed response sign is not a
> separate open datum at the proved cylinder-event scope.
> `KFOrientationHigherRankDecoherence.lean` proves the complementary
> result: every admissible `D_y` has an explicit two-component Gram amplitude,
> strict interiors cannot have a scalar-amplitude realization, and the second
> component vanishes exactly at the endpoints. The only reflection-fixed
> balanced kernel is `D_0`, so choosing an endpoint sign necessarily requires a
> reflection-odd chirality datum.

## Checked Causal-Growth Dependency Ledger

`KFCausalSetPostulateFootprint.lean` makes these rows build-time assertions on
transitive declaration dependencies, rather than a hand-maintained prose
partition.

| Layer | Inputs actually used | Current theorem boundary |
|---|---|---|
| Finite character selection | Balanced birth symmetry plus the explicit source-sign response | Leaves exactly one of the conjugate `+/-i` characters for nonzero drive. It uses no clock, exchangeability, spectator action, or fractional-volume bridge. The variational predicate is extensionally equivalent bookkeeping, with no flow or attainable geometric minimum |
| Abstract projective sign transport | The already selected chiral growth law | Uses no clock, exchangeability, spectator action, or fractional-volume bridge |
| Concrete harmonic spectator realization | An exchangeable normalized spectator action | Exchangeability forces the uniform local source used by the zero-free projective action. Order-isomorphism covariance alone is insufficient |
| Geometric interpretation | Fractional-volume coupling bridge | Identifies the harmonic increment with one-cell fractional number-volume growth. The arithmetic and dimensional cancellation are derived; the identification is postulated and is not a dependency of abstract selection or transport |
| Handedness interpretation | Future-frequency clock evolution plus the weak/Lorentzian map | Names a fixed transported representative as a left-handed weak current. It does not select that representative in the finite core |

The separate continuum target is to reconstruct the Lorentzian spin bundle,
Dirac operator, and scaling limit. It belongs to the interpretation layer, not
the finite selection or abstract transport core.

## Paper

**"Time is a Partial Order"** — [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

DOI: [10.5281/zenodo.19613914](https://zenodo.org/records/19613914)

## Capstone Theorem

**`framework_master_2026`** in `LayerB/FrameworkCapstone.lean` — single 30-conjunct master theorem citing the framework's complete state. Foundational axioms only.

## Summary

The core algebraic/numerical proposal uses one ontological postulate, two
physical identifications, and the Planck mass. The causal-growth extension is
not included in that count. Its finite selector, abstract transport, concrete
harmonic realization, geometric interpretation, and handedness interpretation
have the separate machine-checked dependency footprints listed above.
Within the stated core assumptions, the repository obtains the proposed
Standard Model algebraic structure, the Higgs mass to 0.54%, the electroweak
scale to 2.3%, and the mass hierarchy to 3.5%.

The May 2026 audit chain (`PreRegistrationLedger.lean`) added: a 5-integer atomic vocabulary {N_W=2, N_c=3, N_total=5, d_eff=4, disc=7}, six audit-driven corrections strictly improving PDG fit, 17+ exact cross-sector identities, KPGAC selection principle, and 4D causal SO(10) substrate identification.

Every algebraic step is formally verified in Lean 4. Zero sorry. Zero custom axioms.

## Effective Input Count

| Input | Type | Status |
|-------|------|--------|
| Locally finite partial order | Ontological postulate | Axiom |
| m_H = γ_d · v | Physical identification | `SpectralMassTheorem.higgsMassFromGap` — λ_H = γ₄²/2 follows by `quartic_eq_half_gap_squared` |
| v = M_P exp(−c/g²) with g²=2 | Physical identification | `VEVIdentificationChain.lean` |
| M_P | Dimensionful scale | One measured constant |

Everything else in this core input table is derived within the stated
framework. The causal-growth principles and continuum targets are recorded
separately above.

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

900 Lean files in `UnifiedTheory/`, **zero sorry and zero custom axioms** in
core mathematical content. Latest full root build: 8,664 jobs successful
(July 2026).
Foundational axioms only: `propext`, `Classical.choice`, `Quot.sound`.
