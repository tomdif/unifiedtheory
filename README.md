# Time is a Partial Order

**One postulate. Two identifications. Zero free parameters. Machine-checked in Lean 4.**

> **Current scope note (July 2026).** The finite-poset and matrix results are
> machine-checked mathematics. The repository now constructs projective quantum
> causal-set cylinder kinematics and a zero-free, normalized chiral
> ancestor-pair law, but does **not** yet derive its symmetry/source or
> a zero-safe running pair coupling from deeper microphysics
> or recover ordinary GR/QFT through
> a nontrivial coarse-graining flow. The direct Poisson-sprinkling test of the bare
> `K_F -> J_4` identification was negative. The later scope statement in
> [`FINAL_FRAMEWORK_CHARACTERIZATION.md`](FINAL_FRAMEWORK_CHARACTERIZATION.md) and
> the executable audit in
> [`QUANTUM_GEOMETRY_IR_AUDIT.md`](QUANTUM_GEOMETRY_IR_AUDIT.md) control quantum-
> gravity and continuum claims.

The repository formally verifies a proposed chain from a locally finite partial order
to Standard Model structures and numerical identifications. The finite algebraic steps
are Lean-checked; calling the full chain a physical derivation still requires the open
quantum-dynamics, order-to-geometry, and infrared-recovery bridges named above.

**Paper:** [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

## What Is Derived

**From one postulate** (spacetime is a locally finite partial order), **two identifications** (λ_H = γ₄²/2 and v = M_P exp(-c/g²)), and **one scale** (M_P):

### Structure (Layer 1 — unconditional algebra)

| Result | Status | Key File |
|--------|--------|----------|
| Spacetime dimension d = 3+1 | Lean ✓ | `DimensionDerived.lean` |
| d_spatial = 3 (independent confirmation) | Lean ✓ | `AntichainOverlap.lean` |
| Gauge group SU(3) × SU(2) × U(1) | Lean ✓ | `GaugeGroupDerived.lean` |
| sin²θ_W = 3/8 | Lean ✓ | `WeinbergAngle.lean` |
| 15 Weyl fermions per generation | Lean ✓ | `FermionCountFromAnomaly.lean` |
| 3 generations | Lean ✓ | `ThreeGenerations.lean` |
| All electric charges | Lean ✓ | `AnomalyConstraints.lean` |
| θ_QCD = 0 (strong CP solved) | Lean ✓ | `StrongCP.lean` |
| Proton stability | Lean ✓ | `ProtonStability.lean` |
| Spectral gap γ₄ = ln(5/3) | Lean ✓ | `FeshbachJ4.lean` |
| Feshbach discriminant Δ = 7 (prime, unique to d=4) | Lean ✓ | `ChamberPolynomialTheory.lean` |
| Char poly (5λ−3)(150λ²−50λ+3) = 0 | Lean ✓ | `FeshbachJ4.lean` |

### Quantum Mechanics (derived, not postulated)

| Result | Status | Key File |
|--------|--------|----------|
| Complex amplitudes from K/P | Lean ✓ | `ComplexFromDressing.lean` |
| Born rule \|z\|² unique | Lean ✓ | `BornRuleUnique.lean` |
| Bell violation CHSH² = 8 > 4 | Lean ✓ | `BellTheorem.lean` |
| No spooky action at a distance | Lean ✓ | `NoSpookyAction.lean` |
| Decoherence → classical | Lean ✓ | `Decoherence.lean` |
| Poset growth = Born rule | Lean ✓ | `PosetGrowthIsQuantum.lean` |
| QM is a theorem | Lean ✓ | `QuantumMechanicsIsATheorem.lean` |

### Parameters (Layer 3 — conditional on two identifications)

| Observable | Predicted | Measured | Agreement |
|-----------|-----------|---------|-----------|
| Higgs mass m_H | ln(5/3) · v = 125.78 GeV | 125.10 ± 0.14 GeV | 0.54% |
| Higgs quartic λ_H | [ln(5/3)]²/2 = 0.1305 | ~0.13 | ~1% |
| Electroweak scale v | 240.6 GeV | 246 GeV | 2.3% |
| Mass hierarchy shape | ln(5−√7)/ln(5+√7) = 0.421 | 0.436 | 3.5% |
| Cabibbo angle (Fritzsch) | 0.224 | 0.225 | 0.5% |
| Proton mass (with Λ_QCD) | 941 MeV | 938 MeV | 0.3% |

### Resolved Foundational Debates

| Debate | Resolution | Key File |
|--------|-----------|----------|
| Information paradox | Finite → invertible → unitary | `InformationParadox.lean` |
| Hierarchy problem | γ₄ = ln(5/3) is O(1), scale-invariant | `HierarchyProblem.lean` |
| Problem of time | Partial order IS time | `ProblemOfTime.lean` |
| Why something? | Flat grid beats empty set | `WhySomething.lean` |
| Continuous time | Emergent from discrete chains | `ContinuousTimeEmergent.lean` |
| Big Bang | Poset minimum | `BigBangIsPosetMinimum.lean` |
| Anti-gravity | Impossible (3 routes) | `AntiGravityImpossible.lean` |

### Four Falsifiable Predictions

| Prediction | Test | Key File |
|-----------|------|----------|
| No axion at any mass | ADMX, CAST, ALPS II | `FalsifiablePredictions.lean` |
| P-sector DM at ~126 GeV | HL-LHC invisible Higgs | `FalsifiablePredictions.lean` |
| BH remnants at 6 M_P | Hawking evaporation endpoint | `FalsifiablePredictions.lean` |
| Normal ν ordering, m₁ ≈ 5 μeV | JUNO, CMB-S4, Euclid | `FalsifiablePredictions.lean` |

## Three Layers, Three Risk Profiles

**Layer 1 (unconditional).** Theorems of finite mathematics. Do not depend on the Hauptvermutung or any physical identification. Proved in `HauptvermutungIndependence.lean`.

**Layer 2 (conditional on Hauptvermutung).** Einstein's equation, holographic bound, cosmological constant. Require the causal set to be manifold-like.

**Layer 3 (conditional on two identifications).** Higgs mass, electroweak scale, mass hierarchy. Require Layer 1 plus:
- `IdentificationChain.lean`: λ_H = γ₄²/2
- `VEVIdentificationChain.lean`: v = M_P exp(−c/g²) with g² = 2

## Quantum Geometry and Continuum Scope

- Unlabeled causal-growth cylinder histories now carry normalized, projectively
  consistent, strongly positive decoherence functionals. A concrete Bell-causal
  law `lambda^(omega(omega-1)) (±i)^m`, with canonical base-two Liouville
  `lambda`, is proved zero-free at every finite parent and therefore needs no
  fallback. Exact cancellations across all finite parents are confined to a
  countable algebraic exceptional locus. More strongly, the unit constant term
  excludes every rational cancellation with `lambda>1`. The elementary schedule
  `lambda_n=(n+2)/(n+1)` defines one rank-dependent normalized law, runs to
  `g=1` in the required `1/n` window, and has an explicit all-parent partition
  and condition-number bound. Subexponential stability, physical coupling/sign
  selection, and the infrared limit remain open.
- The original growth/Born result is only a finite implication from a quadratic
  SO(2)-invariant ansatz. The later causal-growth modules derive `b=+/-i` from
  normalized elementary relation-complement symmetry and prove that a nonzero
  reflection-odd source selects its sign. The deeper origin of that symmetry
  and source remains open.
- The 2+1D audit now combines zero local TT modes with a flat finite-torus
  connection carrying two distinct gauge-invariant global holonomies. This is a
  kinematic benchmark; quantum dynamics and refinement invariance remain open.
- `H_chamber_at_density` is constant by definition. Its `Tendsto` result is
  structural density rigidity, not a nontrivial renormalization trajectory.
- T11 is negative for the tested bare `K_F` sprinkling spectrum. A renormalized
  operator remains an open, preregisterable research route.
- A generic determinant-defined finite-poset `K_F` now exists. Its normalized
  rank-one second moment separates four benchmark orders, and two distinct fine
  orders admit exact nonconstant quotient flows to one coarse spectral value.
  This is a finite one-step witness, not Poisson-ensemble RG or a continuum limit;
  the full symmetrized operator is generically blind to reversing causal orientation
  at every chamber rank.
- Exact rank-two evaluation also separates the four orders, with normalized values
  `1/6`, `4/9`, `13/18`, and `2/3`. It produces negative determinant-interference
  entries and reverses the diamond/total-chain ordering seen at rank one, proving
  that higher rank adds shape information even though it cannot add orientation.
- The precise repair is now explicit: the omitted forward-minus-backward
  determinant channel is skew-symmetric, flips sign under order duality, and
  together with `K_F` reconstructs each directed zeta determinant. On rank-two
  diamond chambers its value changes exactly from `1` to `-1` under duality.
- Joint blocking is now tracked rather than inferred. The symmetric rank profile
  flows from `(7/8, 13/18)` on the diamond to `(1, 7/9)` on the coarse chain.
  Its exact increments are `(1/8, 1/18)`, so this is not a uniform amplitude
  rescaling: the two ranks require distinct effective couplings.
  The skew channel is not closed under naïve fiber blocking: besides the recomputed
  coarse channel it generates an exact nonzero long-range orientation operator.
  The resulting orientation defect is now generic: it is skew, relabeling-covariant,
  vanishes exactly when the ansatz closes, and obeys an affine cocycle law under
  successive partial blocks. Endpoint redefinitions shift it by an exact
  compositional coboundary. This is finite RG structure, not yet an iterated physical
  flow.
- A genuine path comparison now exists. Two certified
  `chain₄ → chain₃ → chain₂` quotients have endpoint fiber profiles `(1,3)` and
  `(2,2)` and transport the same UV orientation operator with exact strengths
  `3` and `4`. For every shared nonzero normalization, no single IR counterterm
  closes both paths. Unrestricted counterterms remain trivial because they may
  erase every native operator; the obstruction requires fixed UV normalization.
- The physically natural semantic restriction is now exact: if a corrected
  orientation channel must still reconstruct the same forward and backward zeta
  determinants together with the unchanged `K_F`, its additive counterterm is
  necessarily zero. The generated diamond long-range term therefore cannot be
  absorbed into the native channel without changing its observable meaning; it is
  an independent effective operator in this reconstruction scheme.
- The first exact two-step coupling recurrence is now certified on total chains.
  Equal fibers `(2,2,2)` transport the rank-one orientation coupling by `4`; the
  next block transports it by `2`, and the composite factor is `8`. Accordingly,
  the closing weights multiply as `(1/4)(1/2) = 1/8`. By contrast, fibers
  `(1,2,3)` generate the three pair couplings `(2,3,6)`, so no scalar normalization
  closes the one-coupling ansatz. In this finite benchmark, fiber homogeneity is
  the mechanism separating closed flow from operator proliferation; this is not
  yet an arbitrary-poset or continuum classification.
- That mechanism is now a theorem rather than a pattern match. For every finite
  ordered block map, the transported rank-one coupling between coarse blocks
  `a < b` is exactly `|f⁻¹(a)| |f⁻¹(b)|`. For a surjective quotient onto three
  blocks, scalar closure holds if and only if all three fibers have equal size.
  A certified `chain₁₂ → chain₆ → chain₃ → chain₂` path consequently has factors
  `4`, `4`, and `2`, composite factor `32`, and closing normalization `1/32`.
- Uniformity is not sufficient across chamber rank. Lifting the uniform
  `chain₆ → chain₃` event quotient to rank-two chambers gives
  `push(A₂) = 12 A₂,coarse + G`, where `G` is a nonzero long-range coupling of
  strength `4`. No scalar normalization closes it. Thus rank-one closure does
  not imply multirank closure: determinant interlacing itself generates an
  operator even when the event fibers are perfectly homogeneous.
- The rank-two mechanism is now parametric. For three consecutive positive
  fiber sizes `(p,q,r)`, the exact upper couplings are `pqr(p+1)/2`,
  `pqr(q-1)/2`, and `pqr(r+1)/2`. Rank two closes up to a scalar exactly when
  `q=1` and `p=r`; combining this with rank-one closure leaves only the identity
  profile `(1,1,1)`. For uniform size `s`, the generated/adjacent ratio is
  `1 - 2/(s+1)`, so the new operator is not suppressed at large fiber size.
- The parametric law has four further exact consequences. The native adjacent,
  generated long-range, and outer-fiber imbalance matrices form a unique
  three-channel skew basis closed by commutators; any uniform block with `s > 1`
  and the native operator generate that basis. The normalized uniform parameter
  `u_s = (s-1)/(s+1)` obeys
  `u_(st) = (u_s+u_t)/(1+u_s u_t)` and has rapidity `log(s)/2`.
  Cross-rank rank-two/rank-one coupling ratios reconstruct every positive fiber
  triple `(p,q,r)` and satisfy exact odd-square certificates. Finally, unequal
  reflected profiles `(p,q,r)` and `(r,q,p)` give different orientation matrices
  with the same characteristic polynomial: the spectrum retains the squared
  coupling norm but loses the sign of the imbalance channel.
- A conditional quantum lift is now exact. The continuous interpolation
  `u(ell)=(exp(ell)-1)/(exp(ell)+1)` recovers every discrete uniform profile at
  `ell=log(s)`, satisfies `du/dell=(1-u²)/2`, and tends to `1`. Multiplication of
  the real skew push by `i` is Hermitian with roots `0, ±rho`; both its raw radius
  `rho²=s⁶(3s²+2s+3)/4` and normalized radius `rho²=2+u_s²` are proved. For every
  `s>1`, the first two commutator iterates from the native channel span the full
  three-channel skew sector. Every function of the Hamiltonian characteristic
  polynomial is nevertheless blind to distinct outer-reflected profiles. This is
  a finite matrix model, not a state space or physical Hamiltonian for causal sets.
- The spectral blind spot is now constructively resolved at the eigenvector level.
  Every profile has an explicit nonzero zero mode
  `(right coupling, -long coupling, left coupling)`. Its endpoint asymmetry equals
  exactly twice the imbalance coefficient and is nonzero precisely when `p ≠ r`.
  Consequently unequal outer-reflected Hamiltonians have the same spectrum but
  different kernels. The Hamiltonian also obeys `H³=rho²H`; its quadratic Casimir
  is reflection-even, and every polynomial in `H` reduces exactly to degree below
  three. Thus the retained spectrum and discarded orientation direction are now
  separated by explicit machine-checked observables.
- The finite Hamiltonian now has an exact spectral resolution. For positive fibers,
  explicit Hermitian projectors onto the `0`, `+rho`, and `-rho` sectors are
  idempotent, mutually orthogonal, and sum to the identity. They produce the closed
  propagator
  `U(t)=P₀+cos(rho t)Q-i sin(rho t)J`, with machine-checked laws
  `U(0)=1`, `U(t+u)=U(t)U(u)`, `U(t)ᴴU(t)=1`, and `U(t)v₀=v₀`.
  This is the first exact unitary evolution in the enlarged finite orientation
  sector, conditional on choosing `H=iP` as its generator; it is not yet causal-set
  quantum dynamics.
- The three-level sector is now identified exactly as the spin-one representation
  of `su(2)`. Three normalized Hermitian generators obey
  `[J₁,J₂]=iJ₃` and cyclic permutations, with
  `J₁²+J₂²+J₃²=2I`. The profile Hamiltonian is
  `H=B₁J₁+B₂J₂+B₃J₃`, where
  `B=(sqrt(2) alpha, beta, sqrt(2) gamma)` and `|B|²=rho²`.
  Outer-fiber reflection flips only `B₃`; uniform profiles have field direction
  `(sqrt(2),u_s,0)`. For positive fibers, the conditional propagator recurs exactly
  after `2*pi/rho`. This is an exact finite representation, not evidence that the
  sector is a physical spin-1 particle, graviton, or spacetime rotation group.
- The spin-one coordinates produce an exact relational hierarchy. For effective
  fields `A`, `B`, and `C`,
  `trace(H_A H_B)=2 A·B` and
  `trace(H_A[H_B,H_C])=2i A·(B×C)`.
  Simultaneously reflecting every outer-fiber profile preserves all pairwise
  overlaps—the entire Gram data—but reverses the cubic trace. The certified
  profiles `(1,1,1)`, `(2,2,2)`, and `(2,1,1)` give `8i`; their simultaneous
  reflection gives `-8i`. Every triple of uniform profiles has zero cubic
  chirality. Thus pairwise relational data remain orientation-blind, while a
  three-operator pseudoscalar suffices to recover handedness in this finite sector.
  This is not yet a continuum volume form or physical parity-violating observable.
- The amount of missing information is now classified exactly. The commutator
  satisfies
  `trace([H_A,H_B]²)=-2|A×B|²`, so noncommutativity measures relational
  area and vanishes exactly when the cross-product area does. The cubic scalar
  obeys
  `[A·(B×C)]²=det Gram(A,B,C)` and therefore
  `trace(H_A[H_B,H_C])²=-4 det Gram(A,B,C)`.
  Equal complete pairwise Gram data force the two cubic values to be equal or
  opposite. Thus pair traces fix the magnitude of chirality, leaving exactly one
  `Z2` orientation sign for a nondegenerate triple—not another continuous degree
  of freedom. The explicit witness has Gram determinant `16`, chirality square
  `-64`, and realizes both signs under reflection.
- The conditional Heisenberg action is now completely classified on the linear
  spin-one sector. Writing `L(X)=i[H,X]`, Lean proves
  `L²(X)=-rho² X+(B·X)H`. For positive profiles, `L(X)=0` exactly when
  the effective field of `X` is a scalar multiple of `B`: the Hamiltonian direction
  is the unique conserved linear channel. Every transverse observable satisfies
  `L²(X)=-rho²X`, and the full sector satisfies `L³=-rho²L`.
  This is the algebraic source of the previously proved sinusoidal recurrence:
  one stationary longitudinal mode plus a two-dimensional transverse oscillator.
  It remains conditional on selecting the finite orientation Hamiltonian.
- The cubic closure now exponentiates to an exact finite Rodrigues action,
  `R_t(X)=X+(sin(rho*t)/rho)LX+((1-cos(rho*t))/rho²)L²X`. Lean proves
  `R_0=id`, `R_(t+u)=R_t R_u`, `R_(-t)R_t=id`, exact transverse rotation,
  and preservation of every pairwise trace overlap. Thus the complete Gram
  geometry is conserved by this reversible conditional dynamics.
- The same invariant produces a dynamics-versus-blocking no-go. The recomputed
  coarse chain orientation Hamiltonian has trace strength `trace(H²)=4`, while
  the globally half-normalized diamond push generates the long-range edge and
  raises it to `6`. Therefore no positive-profile fixed-Hamiltonian Rodrigues
  evolution can turn the native coarse operator into that blocked operator. This
  separates the certified finite blocking prescription from ordinary reversible
  time evolution; it is not yet an RG theorem.
- Per-fiber normalization now gives a genuine unital one-Kraus quantum channel
  `Phi(A)=V†AV`. Lean proves its exact Kadison–Schwarz factorization
  `D(A,B)=L(A)†L(B)`, positivity of `D(A,A)`, and the Hermitian
  multiplicative-domain criterion `D(A,A)=0 iff L(A)=0`. The defect is now
  certified as a completely positive operator-valued kernel: every finite
  coefficient amplification factors as one positive Gram square.
  Multiplicative-domain members preserve products on both sides. The orientation Hamiltonian is a sharp
  boundary case: its channel defect is zero although its compressed image does not
  equal the independently recomputed coarse ansatz. By contrast, a coupling to the
  collapsed chamber has retained image zero and nonzero defect. Hence ansatz
  nonclosure and discarded covariance are distinct. Lean now packages them as two
  reusable gates and proves neither implies the other. It also proves the stronger
  no-go: no function of the retained operator can reconstruct the diagonal defect
  for every fine observable.
- A second normalized block channel now gives an exact two-scale law,
  `D_(Psi∘Phi)=Psi(D_Phi)+D_Psi(Phi·,Phi·)`. The orientation Hamiltonian
  passes the first multiplicative-domain gate but develops a nonzero composed
  defect at the next scale, with an exact diagonal witness equal to `2`. Thus
  losslessness is scale-relative: passing one coarse-graining step does not make
  an observable safe under further compression. The new defect is not generic:
  Lean identifies its full `2×2` matrix and factors it as `R†R` for one explicit
  nonzero `1×2` noise row. Only one discarded covariance mode is generated in
  this benchmark.
- The channel construction now extends to arbitrary finite heterogeneous towers.
  Lean proves that the total Schwarz defect is exactly the recursively transported
  sum of defects generated at each scale, and defines the protected sector by
  multiplicative-domain membership at every successive image. The concrete
  orientation observable is protected for one scale but not for the two-scale
  tower. Two common-endpoint paths also carry a defect curvature with exact
  antisymmetry, triangle, and postcomposition laws. Independently, the existing
  rational `(1,3)` and `(2,2)` quotient routes differ by exactly one native
  orientation unit. Hermitianizing that curvature gives the Pauli-Y matrix: it is
  traceless, squares to `I`, and has two explicit orthogonal trace-one projectors.
  This is a finite binary orientation-holonomy witness, not yet a physical qubit,
  particle, gauge charge, or continuum RG holonomy.
- That witness now has an exact finite quantum promotion. The two quotient routes
  form an orthonormal path basis and the two curvature signs form the mutually
  unbiased `(1, +/- i)/sqrt(2)` basis. Route dephasing sends both signs to `I/2`.
  More strongly, every finite route event has the same real decoherence measure in
  both sectors: the orientation bit lives only in the sign of an imaginary
  off-diagonal history amplitude. Route `Z` and curvature `Y` generate coherence
  `X`, close all of `M_2(C)`, obey the spin-half `su(2)` algebra with Casimir
  `3/4`, and exhibit the exact spinor law: a `2*pi` rotation negates kets but fixes
  density matrices, while `4*pi` returns the ket. Curvature-generated transport is
  unitary and conserves the two sign probabilities. The independent cubic
  relational-chirality witness and its reflection select the `+/-` projectors.
  These are exact finite algebraic theorems conditional on treating quotient paths
  as coherent alternatives; no microscopic sum over causal histories, physical
  clock/refinement parameter, fermion identification, or continuum observable is
  claimed.
- Strong positivity and balanced normalization do not uniquely force the
  extremal phase. Lean classifies every admissible kernel as
  `D_y=[[1/2,iy],[-iy,1/2]]` with a unique `|y|<=1/2`. Every member is the convex
  mixture `(1/2-y)P_+ + (1/2+y)P_-`; reflection sends `y` to `-y`. The center
  `y=0` is an explicit normalized strongly positive counterexample to kinematic
  phase uniqueness. In fact every `y` gives the same real route-event (`Z`-sector)
  measures and
  dephases to `I/2`. Purity, convex extremality, and deterministic curvature
  orientation are each equivalent to endpoint saturation `y=+/-1/2`, and the independent cubic
  chirality witnesses select exactly those endpoints. Thus microscopic dynamics
  or refinement covariance must select the physical phase; positivity alone
  cannot.
- The multiplicative refinement mechanism now has an explicit quantum-channel
  realization. A four-Kraus CPTP map measures the two input curvature sectors
  and prepares their orientation-parity output, proving exactly
  `Phi(D_y ⊗ D_z)=D_(2yz)`. On the balanced sector it is associative,
  commutative under input exchange, reflection-equivariant, and uniquely fixed
  by its four pure-endpoint outputs. Consequently every nonzero interior kernel
  contracts strictly under self-refinement, while exactly the two
  pure/chirality-selected endpoints preserve coherence magnitude. This derives
  the semigroup from a finite physical channel. The follow-up frontier theorem
  constructs the causal ordinal sum `P then Q`, proves that it is covariant under
  genuine order isomorphism and associative after label quotienting, and descends
  it to this channel on unlabeled histories. The rescaled orientation sign is a
  multiplicative `Z_2` character of that serial composition. It also constructs a
  reversible rectangular Stinespring dilation
  whose four endpoint amplitudes produce the parity table. The next finite
  construction retains the two distinct complete associator trees and equips
  them with a normalized Hermitian decoherence functional. Its Gram form is
  strongly positive both on sampled routes and arbitrary finite route-events,
  every event has nonnegative quantum measure, the measure obeys Sorkin's
  grade-two sum rule, and its total event has value one.
  The microscopic dilation generates the route amplitudes, and restriction gives
  exactly the extremal orientation kernel and CPTP refinement output. The
  all-depth follow-up proves a generic extension theorem: every normalized complex
  finite-branching law produces normalized, Hermitian, strongly positive
  decoherence functionals at every depth, with exact marginal consistency across
  arbitrary depth gaps. Refinement-equivalent finite presentations are quotiented
  into literal events of infinite branch streams. The resulting cylinder
  functional is normalized and strongly positive, is finitely additive on
  common-depth presentations, has a nonnegative grade-two quantum measure, and
  restricts at depth one to the finite orientation kernel. The physical follow-up
  removes the fixed-alphabet restriction: fixed-cardinality causal orders are
  quotiented by genuine isomorphism, every child obtainable by a maximal-element
  birth is an unlabeled branch, the successor set is finite and nonempty, and a
  child-uniform law gives an
  exactly projective normalized strongly positive functional on complete
  unlabeled causal-set cylinder histories. General supported complex weights
  inherit the same theorem after local partition normalization. The
  transition-edge follow-up retains every distinct downward-closed precursor
  slot, proves representative-independent link multiplicity and the exact
  multiplicity-weighted Markov identity, and supplies the corrected law that is
  uniform over precursor slots rather than child isomorphism classes. The
  two-antichain benchmark has a certified link of multiplicity at least two.
  The explicit restriction module now maps any
  complete two-sector cylinder partition to a `2 x 2` kernel and proves that a
  balanced restriction is a unique `D_y`. Since every current growth functional
  is built from one scalar path amplitude, the induced kernel has determinant
  zero; balance therefore forces `|y| = 1/2` and one of the two orientation
  projectors. Projective refinement preserves that endpoint exactly. Canonical
  spectator deletion now restricts each pair of precursor alternatives to their
  union and preserves the full Rideout--Sorkin `(omega,m)` signature. Covariant
  complex raw-edge amplitudes, coherent child aggregation, and zero-safe Bell
  causality are formalized. Bell causality alone is underdetermined: it contains
  an injective family parameterized by every complex sequence `ℕ → ℂ`. The open
  physics problem is now sharply reduced. Independent-composition locality
  classifies signature-local laws as `a^omega b^m`, leaving two complex
  couplings. Fixing the ancestor gauge `a=1` and a chirality-aligned elementary
  phase `b=+/-i` selects one unique reflected character. The new microscopic
  birth theorem removes one more assumption: at the one-event parent, the only
  precursor slots are empty and full, with normalized amplitudes `1/(1+b)` and
  `b/(1+b)`; requiring equal Born weights forces `b=+i` or `b=-i`. The two slots
  remain distinct after quotienting to the unlabeled two-antichain and two-chain.
  A totalized Bell-causal character supplies a normalized law at every depth,
  and its depth-two cylinder restriction is exactly
  `D_(chiralBoundaryOrientationParameter chirality)`, hence a pure endpoint.
  Reflection cannot choose the sign by itself: its only fixed balanced kernel is
  `D_0`. The next module isolates the missing laws exactly. Born normalization
  alone leaves an injective real family `b=i t`; imposing elementary
  relation-complement symmetry forces balance and hence `b=+/-i`. A nonzero
  reflection-odd source uniquely selects the corresponding endpoint, while zero
  source leaves the two signs degenerate. The hoped-for global zero-free theorem
  for the independently compositional character is false: for the explicit
  14-event causet `C_8 ⊕ A_6`, both raw chiral
  partition sums vanish by exact destructive interference. Thus the totalized
  character's uniform fallback is structurally active, not defensive bookkeeping.
  `KFCausalSetCompleteChiralLaw.lean` supplies a replacement: an ancestor-pair
  interaction invisible at the elementary birth. Every parent partition has a
  real integer polynomial with constant coefficient one; evaluating it at the
  canonical base-two Liouville number proves global nonvanishing. The resulting
  normalized law has no exceptional branch, inherits the infinite strongly
  positive projective functional, and recovers the same depth-two endpoint.
  The coupling classification is now exact: since
  `omega(omega-1)=2*choose(omega,2)`, the law depends only on the effective
  unordered-pair coupling `g=lambda^2`. Thus `lambda` and `-lambda` are the
  same microscopic law, while `g` is already identifiable from the
  two-ancestor signature. All-rank normalizability does not choose `g`: the
  distinct sparse `g=0` candidate is also zero-free, strongly positive, and
  has the same depth-two orientation endpoint. Full raw transition support
  excludes exactly that degenerate law, but still does not restore uniqueness:
  `lambda+1` is machine-checked as a second positive transcendental,
  full-support, all-rank-zero-free, strongly-positive law with the same
  endpoint and a genuinely different effective coupling. The quantitative
  extension bounds every n-parent polynomial by degree `n(n-1)` and coefficient
  height `2^n`, and proves that all exact cancellation couplings over all ranks
  form a countable subset of the algebraic reals. It also constructs
  `lambda_n = 1 + (L-1)/(n+1)`: every term is transcendental, full-support, and
  all-parent zero-free, while `g_n=lambda_n^2 -> 1` and
  `(n+1)(g_n-1) -> 2(L-1)`. Thus zero-freeness is compatible with critical
  running. The rational-root refinement is stronger: constant coefficient one
  implies that no rational `lambda>1` can cancel. Taking
  `lambda_n=(n+2)/(n+1)` yields a single genuinely rank-dependent normalized,
  projective, strongly-positive law and the effective estimates
  `||Z_C|| >= (n+1)^(-n(n-1))` and
  `condition <= 2^n (n+2)^(n(n-1))`. Transcendence is therefore sufficient but
  unnecessary. More generally, every positive rational `c=a/b` gives
  `lambda_n=1+c/(n+1)` with scaled limit `kappa=2a/b`, the effective margin
  `(b(n+1))^(-n(n-1))`, and its own complete projective strongly-positive law.
  Thus `kappa=2` is a representative, not a kinematic prediction. The simplest
  hoped-for stability mechanism is also ruled out: the two-antichain parent
  polynomial has coefficients `P_0=1` and `P_2=-1`, so real-coefficient
  positivity fails already at rank two. The exhaustive census finds a negative
  real coefficient in 317 of 318 rank-six parents and absolute-coefficient
  nonunimodality in 26 of them. A further exact correction comes from precursor
  multiplicity. On an `(n+1)`-antichain the incoherent precursor-slot
  one-missing/timid Born-mass ratio is `(n+1)/g_(n+1)^(2n)`, while the actual
  unlabeled transition law first adds the isomorphic slots coherently and has
  ratio `(n+1)^2/g_(n+1)^(2n)`. Hence every finite-`kappa` schedule with
  `n log g_(n+1) -> kappa` sends both ratios to infinity, including the whole
  positive-rational family above. The earlier `1/n` criterion balances two
  individual edges, not complete unlabeled sectors. Coherent antichain balance
  instead requires `2n log g_(n+1) = 2log(n+1)+O(1)`. That corrected window is
  constructively inhabited. With rational harmonic numbers `H_n`, set
  `lambda_0=lambda_1=2` and `lambda_n=1+H_n/(2(n-1))` for `n>=2`. Every term is
  rational and above one, hence universally zero-free, while `lambda_n -> 1`
  and the coherent unlabeled antichain ratio tends to `exp(-2gamma)`. The same law
  is normalized, projective, and strongly positive on infinite cylinders. What
  looked like an inserted closed form is now reduced to a local refinement law.
  `KFCausalSetHarmonicRefinementLaw.lean` proves that exchangeability and unit
  normalization uniquely force spectator weight `1/n`; the additive charge
  recursion `Q_(n+1)=Q_n+1/(n+1)` classifies all solutions as
  `Q_n=H_n+Q_2-H_2`. The canonical seed `Q_2=H_2=3/2` uniquely gives the
  harmonic coupling above. Every nonnegative seed stays in the critical window
  and has coherent limit `exp(-2(gamma+Q_2-H_2))`; matching `exp(-2gamma)` is
  equivalent to the canonical seed. For that trajectory, the exact offset is
  the discrete-continuum spectator anomaly `H_n-log n`.
  `KFCausalSetMicroscopicSpectatorAction.lean` now derives both the additive
  update and the seed from one action law on actual unlabeled growth histories.
  Event-slot invariance under every finite permutation plus unit normalization
  forces the newborn action density `1/(n+1)`; summing it from the empty causet
  gives `Q_n=H_n` on every path and hence `Q_2=3/2`. The reconstructed coupling
  is the same all-parent zero-free, projective, strongly-positive law above.
  What remains open is deriving this normalized spectator-action law from a
  geometric causal action, obtaining a useful all-parent condition-number
  bound, and selecting the reflection-odd sign/source.
  A local exhaustive and higher-rank stress test sharpens this further. Adding
  one ancestor multiplies the effective amplitude by the exact factor
  `g^omega`; every tested fixed `g>1` ran toward the full-precursor/timid
  channel, while fixed `0<=g<1` ran toward the zero/one-ancestor sparse sector.
  Comparing two individual adjacent sectors requires
  `(n-1) log g_n = O(1)`, hence `g_n -> 1`. Counting the multiplicity of every
  precursor in a coherently aggregated unlabeled sector strengthens this on
  antichains to `2(n-1) log g_n = 2log n + O(1)`. Both regimes require control of the
  destructive interference that becomes severe near the critical surface.
  See [`CHIRAL_GROWTH_GENERALIZATION_AUDIT.md`](CHIRAL_GROWTH_GENERALIZATION_AUDIT.md)
  and `scripts/chiral_growth_generalization.py`.
  The higher-rank alternative is exact: an explicit two-component latent
  amplitude realizes every admissible `D_y`; rank two is necessary at every
  strict interior point and collapses to rank one exactly at the endpoints.

See [`QUANTUM_GEOMETRY_IR_AUDIT.md`](QUANTUM_GEOMETRY_IR_AUDIT.md) for the claim
policy, 3D benchmark, and infrared recovery protocol. The machine-checkable ledger
is `UnifiedTheory/Audit/QuantumGeometryStatus.lean`; the finite 3D bridge is
`UnifiedTheory/Audit/ThreeDTopologicalBenchmark.lean`. The repo-wide theorem that
the current order, symmetry, and continuum interfaces erase their relevant inputs is
documented in [`BREAKTHROUGH_SEARCH_AUDIT.md`](BREAKTHROUGH_SEARCH_AUDIT.md) and proved
in `UnifiedTheory/Audit/ObservableSeparation.lean`. Its constructive finite repair—an
order-derived signature that separates four benchmark orders and is invariant under
all relabelings—is proved in
`UnifiedTheory/Audit/OrderSensitiveObservables.lean`. Its generic spectral extension,
finite quotient flow, and exact order-duality limitation are proved in
`UnifiedTheory/Audit/KFSpectralCoarseGraining.lean`; the exact higher-rank result is
in `UnifiedTheory/Audit/KFHigherRank.lean`, and the joint blocking result is in
`UnifiedTheory/Audit/KFMultirankCoarseGraining.lean`. Its generic covariant defect
and composition law are in `UnifiedTheory/Audit/KFOrientationDefect.lean`.
The fixed-UV two-path obstruction is in
`UnifiedTheory/Audit/KFOrientationPathObstruction.lean`.
The arbitrary finite CP tower, protected-sector gate, path-curvature calculus,
and binary quotient-holonomy witness are in
`UnifiedTheory/Audit/KFOrientationCPChannelTower.lean`.
Its finite Hilbert-space promotion, imaginary-history-phase theorem, complete
Pauli/spin-half algebra, spinor periodicity, stable unitary transport, and
relational-chirality bridge are in
`UnifiedTheory/Audit/KFOrientationPathQuantum.lean`.
The exact strongly positive kernel classification, non-uniqueness witness, and
pure/deterministic endpoint theorem are in
`UnifiedTheory/Audit/KFOrientationHistoryRigidity.lean`.
The multiplicative-refinement semigroup, strict interior contraction, and
asymptotic decoherence theorem are in
`UnifiedTheory/Audit/KFOrientationHistoryRefinement.lean`.
Its explicit four-Kraus CPTP realization, endpoint truth table, associativity,
reflection covariance, and balanced-sector rigidity theorem are in
`UnifiedTheory/Audit/KFOrientationHistoryRefinementChannel.lean`.
The associative causal ordinal composition, its multiplicative `Z_2` orientation
character, finite-order isomorphism quotient, unconditional unlabeled-history
channel theorem, reversible microscopic dilation, and four endpoint amplitude
table are
in `UnifiedTheory/Audit/KFOrientationUnlabeledRefinement.lean`.
The complete binary growth-tree type, normalized strongly positive associator
decoherence functional, event extension, microscopic amplitude derivation, and
exact channel restriction are in
`UnifiedTheory/Audit/KFOrientationGrowthDecoherence.lean`.
The generic all-depth projective family, infinite-stream cylinder quotient,
normalized strongly positive cylinder functional, and exact orientation
depth-one restriction are in
`UnifiedTheory/Audit/KFOrientationInfiniteCylinderDecoherence.lean`.
The rank-dependent extension to every unlabeled maximal-element causal-set birth,
its uniform physical baseline, arbitrary-depth projectivity, infinite-cylinder
functional, and general complex-weight contract are in
`UnifiedTheory/Audit/KFCausalSetSequentialGrowth.lean`.
The complete precursor alphabet, birth construction, relabeling equivalence,
representative-independent Rideout--Sorkin link multiplicity, exact weighted
Markov sum, corrected uniform-slot law, and nontrivial multiplicity benchmark
are in
`UnifiedTheory/Audit/KFCausalSetTransitionEdges.lean`.
Canonical spectator deletion, preservation of `(omega,m)`, covariant complex
edge amplitudes, coherent normalized child aggregation, and the zero-safe Bell
underdetermination theorem, together with the two-coupling composition
classification and unique chiral boundary character, are in
`UnifiedTheory/Audit/KFCausalSetBellCausality.lean`.
The explicit causet-cylinder-to-`D_y` restriction, its unique parameter,
rank-one determinant theorem, endpoint saturation, and projective-refinement
invariance are in `UnifiedTheory/Audit/KFCausalSetOrientationRestriction.lean`.
The explicit two-component Gram realization, strict-interior rank-one no-go,
minimal latent-rank theorem, and reflection-breaking sign boundary are in
`UnifiedTheory/Audit/KFOrientationHigherRankDecoherence.lean`.
The elementary-birth balance theorem, unlabeled two-child separation,
unconditional totalized chiral growth law, and exact depth-two endpoint
restriction are in
`UnifiedTheory/Audit/KFCausalSetChiralGrowth.lean`.
The 14-event zero-partition obstruction, proof that the totalized law actually
uses its uniform branch there, normalization underdetermination theorem,
relation-complement balance law, and reflection-breaking endpoint selector are
in `UnifiedTheory/Audit/KFCausalSetChiralDynamics.lean`.
The all-parent polynomial nonvanishing theorem, exact ancestor-pair composition
defect, canonical Liouville coupling, fallback-free normalized growth law,
infinite-cylinder strong positivity, and exact recovery of the same finite
orientation endpoint are in
`UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`.
The rank-controlled degree/height bounds, countable algebraic cancellation
locus, and explicit zero-free `1/n` critical-running trajectory are in
`UnifiedTheory/Audit/KFCausalSetCriticalRunning.lean`.
The rational-root exclusion theorem, denominator-cleared partition margin,
explicit condition-number bound, and single rank-dependent critical growth law
are in `UnifiedTheory/Audit/KFCausalSetRationalCriticalRunning.lean`.
The complete positive-rational `kappa=2a/b` family is in
`UnifiedTheory/Audit/KFCausalSetRationalCriticalFamily.lean`; the exact
two-antichain mixed-sign coefficient obstruction is in
`UnifiedTheory/Audit/KFCausalSetPartitionCoefficientStructure.lean`; and the
multiplicity-corrected antichain scaling theorem is in
`UnifiedTheory/Audit/KFCausalSetCriticalMultiplicity.lean`. The explicit
harmonic zero-free law whose coherent antichain ratio tends to `exp(-2gamma)` is
in `UnifiedTheory/Audit/KFCausalSetMultiplicityCorrectedRunning.lean`.
The concise physics interpretation, falsification boundary, and next theorem are
collected in
[`ORIENTATION_PATH_SPINOR_NOTE.md`](ORIENTATION_PATH_SPINOR_NOTE.md).
The reconstruction-rigidity theorem is in
`UnifiedTheory/Audit/KFOrientationCountertermRigidity.lean`.
The exact uniform/nonuniform coupling-flow benchmark is in
`UnifiedTheory/Audit/KFOrientationCouplingFlow.lean`.
The general fiber law, three-step recurrence, and rank-two lift obstruction are in
`UnifiedTheory/Audit/KFOrientationFiberLaw.lean`. Its parametric rank-two extension
is in `UnifiedTheory/Audit/KFOrientationRankTwoFiberLaw.lean`: for fiber sizes
`(p,q,r)` it derives all three transported couplings and proves that simultaneous
rank-one/rank-two scalar closure forces the identity profile `(1,1,1)`.
Its operator-algebra, scale-composition, tomography, and spectral consequences are
proved in `UnifiedTheory/Audit/KFOrientationRankTwoConsequences.lean`.
The exact conditional Hermitian lift and its quantum-dynamics scope boundary are in
`UnifiedTheory/Audit/KFOrientationQuantumConsequences.lean`.
The protected zero mode, unequal reflected kernels, Casimir, and polynomial closure
are in `UnifiedTheory/Audit/KFOrientationQuantumZeroMode.lean`.
The exact projector triple and conditional unitary propagator are in
`UnifiedTheory/Audit/KFOrientationQuantumProjectors.lean`.
The exact spin-one generators, effective-field decomposition, reflection law, and
propagator recurrence are in `UnifiedTheory/Audit/KFOrientationSpinOne.lean`.
The pairwise trace geometry, cubic orientation observable, uniform no-go, and
explicit chirality witness are in
`UnifiedTheory/Audit/KFOrientationSpinOneRelational.lean`.
The commutator-area identity, Gram determinant theorem, and exact `Z2` orientation
classification are in `UnifiedTheory/Audit/KFOrientationSpinOneGram.lean`.
The unique linear centralizer, transverse oscillator, and cubic Heisenberg closure
are in `UnifiedTheory/Audit/KFOrientationSpinOneHeisenberg.lean`.
The exact Rodrigues action, inverse, transverse rotation, and trace-Gram invariance
are in `UnifiedTheory/Audit/KFOrientationSpinOneEvolution.lean`.
The certified `4 -> 6` blocking-strength jump and the resulting Heisenberg-orbit
no-go are in `UnifiedTheory/Audit/KFOrientationDynamicsCoarseGraining.lean`.
The unital block channel, exact Schwarz-defect factorization, multiplicative-domain
boundary, and unreconstructible discarded-covariance witness are in
`UnifiedTheory/Audit/KFOrientationCPChannel.lean`.
The two-scale defect cocycle and delayed-loss witness are in
`UnifiedTheory/Audit/KFOrientationCPChannelComposition.lean`.

## What Is Not Derived

- **α ≈ 1/137** — requires non-perturbative Monte Carlo
- **CKM/PMNS mixing matrices** — one-loop Feshbach effect
- **Dark matter abundance** — thermal freeze-out dynamics
- **Λ_QCD** — non-perturbative lattice computation

These are dynamical quantities at the algebra/dynamics boundary.

## Lean Formalization

**430+ files. 1,800+ theorems. Zero sorry. Zero custom axioms.**

```bash
lake build          # builds everything
```

### Capstone Files

| File | Assembles |
|------|-----------|
| `ConditionalEinstein.lean` | RG + null + K/P + Lovelock → Einstein |
| `Capstone.lean` | Metric + connection → gravity + gauge + quantum |
| `MasterCapstone.lean` | `standard_model_is_a_theorem` (21 results) |
| `PhysicsFromCounting.lean` | `physics_is_counting` (23 results) |

### Companion Repository

The algebraic/combinatorial foundations: [causal-algebraic-geometry-lean](https://github.com/tomdif/causal-algebraic-geometry-lean)

Combined: 430+ files, 1,800+ theorems, zero sorry, zero custom axioms across both repos.

## Citation

```bibtex
@article{difiore2026time,
  title={Time is a Partial Order: The Standard Model, the Higgs Mass,
         and the Electroweak Scale from a Single Ontological Postulate},
  author={DiFiore, Thomas},
  year={2026},
  note={Lean 4 formalization: 430+ files, 1800+ theorems,
        zero sorry, zero custom axioms}
}
```

## License

Apache 2.0
