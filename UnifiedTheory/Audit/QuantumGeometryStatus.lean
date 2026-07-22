/-
  Audit/QuantumGeometryStatus.lean

  A machine-checkable scope ledger for the quantum-geometry and
  continuum-recovery claims.

  This file deliberately proves no new physics.  It does three things:

  1. Separates finite mathematical results from conditional bridges,
     empirical negatives, and open physical targets.
  2. Records a genuine negative fact about the current density-indexed
     chamber family: it is constant by definition, so it has no
     nontrivial density dependence.
  3. Defines reusable success criteria for a scale-dependent infrared
     observable and for the proposed 2+1-dimensional benchmark.

  The companion narrative audit is QUANTUM_GEOMETRY_IR_AUDIT.md.
-/

import UnifiedTheory.LayerB.CL1_ContinuumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.QuantumGeometryStatus

open Filter Topology
open UnifiedTheory.LayerB.CL1_ContinuumLimit

/-! ## 1. Claim-scope ledger -/

/-- The evidential scope of a claim in the quantum-geometry program. -/
inductive ClaimScope where
  /-- A theorem about an explicitly defined finite/algebraic object. -/
  | provedFinite
  /-- A theorem whose physical use still requires a bridge hypothesis. -/
  | conditionalBridge
  /-- A proposed identification that failed a recorded numerical test. -/
  | empiricalNegative
  /-- A physical construction or recovery theorem not yet supplied. -/
  | openTarget
  deriving DecidableEq, Repr

/-- One auditable entry in the quantum-geometry claim ledger. -/
structure ClaimEntry where
  name : String
  scope : ClaimScope
  deriving Repr

/--
The current honest boundary of the program.

The one hundred four `provedFinite` entries assert only their mathematical scope.
In particular, this ledger does not promote an algebraic identity to a
physical observable without a dynamics and infrared bridge.
-/
def claimLedger : List ClaimEntry := [
  { name := "finite causal-order substrate", scope := .provedFinite },
  { name := "quadratic SO(2)-invariant norm", scope := .provedFinite },
  { name := "deterministic finite chamber operator", scope := .provedFinite },
  { name := "finite 2+1D local-zero/global-holonomy witness",
    scope := .provedFinite },
  { name := "advertised poset signature is non-injective",
    scope := .provedFinite },
  { name := "order-sensitive finite signature separates benchmark orders",
    scope := .provedFinite },
  { name := "generic determinant K_F on arbitrary finite posets",
    scope := .provedFinite },
  { name := "finite order quotients produce nonconstant spectral recovery witnesses",
    scope := .provedFinite },
  { name := "rank-two inversion and all-rank orientation loss/repair",
    scope := .provedFinite },
  { name := "multirank blocking generates a long-range orientation operator",
    scope := .provedFinite },
  { name := "orientation coarse-graining defect obeys a covariant cocycle law",
    scope := .provedFinite },
  { name := "fixed-UV quotient paths obstruct one shared IR counterterm",
    scope := .provedFinite },
  { name := "directed reconstruction rigidly excludes orientation counterterms",
    scope := .provedFinite },
  { name := "uniform fibers close an exact orientation coupling recurrence",
    scope := .provedFinite },
  { name := "rank-one fiber-product closure does not lift to rank two",
    scope := .provedFinite },
  { name := "parametric rank-two fiber law and multirank closure no-go",
    scope := .provedFinite },
  { name := "rank-two channel algebra, fiber tomography, and spectral blind spot",
    scope := .provedFinite },
  { name := "conditional Hermitian rank-two model and spectral-functional no-go",
    scope := .provedFinite },
  { name := "zero-mode orientation recovery and finite polynomial closure",
    scope := .provedFinite },
  { name := "exact spectral projectors and conditional unitary propagator",
    scope := .provedFinite },
  { name := "exact spin-one representation and recurrent conditional dynamics",
    scope := .provedFinite },
  { name := "pairwise-relational no-go and cubic orientation witness",
    scope := .provedFinite },
  { name := "length-area-volume hierarchy and exact Z2 orientation ambiguity",
    scope := .provedFinite },
  { name := "unique linear centralizer and transverse Heisenberg oscillator",
    scope := .provedFinite },
  { name := "exact Rodrigues Heisenberg action and trace-Gram conservation",
    scope := .provedFinite },
  { name := "orientation blocking lies outside fixed-profile Heisenberg orbits",
    scope := .provedFinite },
  { name := "unital block channel has a CPD defect kernel and independent gates",
    scope := .provedFinite },
  { name := "no retained-image function reconstructs discarded covariance",
    scope := .provedFinite },
  { name := "two-scale defect cocycle and single-mode delayed covariance",
    scope := .provedFinite },
  { name := "arbitrary finite CP tower and all-scale protected sector",
    scope := .provedFinite },
  { name := "binary orientation path holonomy and spectral projectors",
    scope := .provedFinite },
  { name := "path-holonomy Born complementarity and imaginary history phase",
    scope := .provedFinite },
  { name := "full path-qubit Pauli algebra and spin-half periodicity",
    scope := .provedFinite },
  { name := "unitary holonomy transport and reflected chirality-sector bridge",
    scope := .provedFinite },
  { name := "strongly positive balanced history kernels form one closed interval",
    scope := .provedFinite },
  { name := "purity and deterministic orientation select only chirality endpoints",
    scope := .provedFinite },
  { name := "a separate multiplicative CP benchmark contracts interior coherence",
    scope := .provedFinite },
  { name := "four-Kraus CPTP mixing realizes and rigidly fixes coherence multiplication",
    scope := .provedFinite },
  { name := "causal ordinal composition, isomorphism quotient, and unlabeled channel descent",
    scope := .provedFinite },
  { name := "orientation sign is a multiplicative Z2 character of serial causal composition",
    scope := .provedFinite },
  { name := "rectangular Stinespring dilation derives the four endpoint amplitudes",
    scope := .provedFinite },
  { name := "finite complete-route decoherence is normalized and strongly positive",
    scope := .provedFinite },
  { name := "finite-branching growth has a projective infinite-cylinder decoherence functional",
    scope := .provedFinite },
  { name := "unlabeled one-element causal growth has a projective infinite-cylinder functional",
    scope := .provedFinite },
  { name := "Rideout-Sorkin precursor fibers give invariant Markov multiplicities",
    scope := .provedFinite },
  { name := "canonical spectator deletion preserves the full (omega,m) edge signature",
    scope := .provedFinite },
  { name := "independent edge composition reduces signature-local Bell laws to two couplings",
    scope := .provedFinite },
  { name := "balanced scalar-amplitude causet restrictions force orientation endpoints",
    scope := .provedFinite },
  { name := "latent rank two is necessary and sufficient for balanced interior orientation",
    scope := .provedFinite },
  { name := "balanced causet-cylinder restrictions induce a refinement-invariant unique D_y",
    scope := .provedFinite },
  { name := "balanced first causal birth derives the chiral quarter turn and endpoint kernel",
    scope := .provedFinite },
  { name := "relation-complement symmetry derives balanced elementary causal birth",
    scope := .provedFinite },
  { name := "a 14-event causal parent has exactly zero raw chiral partition",
    scope := .provedFinite },
  { name := "a reflection-odd source uniquely selects opposite chirality endpoints",
    scope := .provedFinite },
  { name := "canonical ancestor-pair chiral growth is zero-free, normalized, and projective",
    scope := .provedFinite },
  { name := "endpoint consistency does not select the sign-quotiented pair coupling",
    scope := .provedFinite },
  { name := "ancestor-pair interaction has an exact rank-amplified adjacent-sector factor",
    scope := .provedFinite },
  { name := "all-parent chiral cancellations form a countable algebraic exceptional locus",
    scope := .provedFinite },
  { name := "an explicit zero-free pair coupling runs into the 1/n critical window",
    scope := .provedFinite },
  { name := "unit parent constant term excludes rational cancellation above one",
    scope := .provedFinite },
  { name := "rational critical running has an effective all-parent partition margin",
    scope := .provedFinite },
  { name := "every positive-rational critical modulus defines a projective zero-free law",
    scope := .provedFinite },
  { name := "real chiral parent-polynomial coefficients are not universally positive",
    scope := .provedFinite },
  { name := "finite-kappa running fails slot and coherent antichain balance",
    scope := .provedFinite },
  { name := "a harmonic rational law is zero-free and coherent-antichain balanced",
    scope := .provedFinite },
  { name := "spectator refinement classifies running and IR matching selects the harmonic seed",
    scope := .provedFinite },
  { name := "a covariant normalized vacuum spectator action derives harmonic quantum growth",
    scope := .provedFinite },
  { name := "number-volume and its unique invariant projector derive harmonic spectator growth",
    scope := .provedFinite },
  { name := "projective growth conserves every cylinder interference entry",
    scope := .provedFinite },
  { name := "trace-preserving record diagonalization breaks source normalization",
    scope := .provedFinite },
  { name := "chirality-basis pinching fixes every balanced kernel and exactly \
      decoheres its records",
    scope := .provedFinite },
  { name := "two-antichain tensor extension decoheres chirality while retaining \
      source interference",
    scope := .conditionalBridge },
  { name := "geometric source magnitude is exactly half the signed chirality-record bias",
    scope := .provedFinite },
  { name := "independent two-birth chirality records preserve their one-birth marginals",
    scope := .provedFinite },
  { name := "common-sector transport compounds record bias by the hyperbolic addition law",
    scope := .conditionalBridge },
  { name := "common-sector chirality evidence is additive half-log-odds",
    scope := .conditionalBridge },
  { name := "future-maximal chain evidence is sandwiched by shifted harmonic tails",
    scope := .provedFinite },
  { name := "conditional full-chain chirality record error has logarithmic exponent minus four",
    scope := .provedFinite },
  { name := "rankwise linked-birth source has exact chain-bottom minimum and star maximum",
    scope := .provedFinite },
  { name := "scalar sequential growth cannot realize a nontrivial exactly decoherent \
      chirality record",
    scope := .provedFinite },
  { name := "three marked sheets supply a permutation-isometric rank-two record carrier",
    scope := .provedFinite },
  { name := "intrinsic three-sheet simplex is equivariant and spans exact \
      complex rank two",
    scope := .provedFinite },
  { name := "transported projective vector amplitudes induce consistent positive \
      event kernels",
    scope := .provedFinite },
  { name := "three-sheet simplex projectors form a positive POVM and average to \
      the maximally mixed half-identity",
    scope := .provedFinite },
  { name := "every fully sheet-symmetric standard-carrier endomorphism is scalar",
    scope := .provedFinite },
  { name := "fixed-point-free sheet monodromy obstructs a transported global marking",
    scope := .provedFinite },
  { name := "twisted-transfer eigen-sections obey exhaustive carrier consistency \
      at every finite depth",
    scope := .provedFinite },
  { name := "fiber gauge conjugation preserves twisted eigen-sections and branch Gram kernels",
    scope := .provedFinite },
  { name := "unit twisted eigen-sections induce normalized strongly positive branch functionals",
    scope := .provedFinite },
  { name := "elementary three-cube atoms are three primitive directions and its order \
      automorphism law is exactly S3",
    scope := .provedFinite },
  { name := "centered binary directional incidence gives the equivariant vertex, \
      negative missing vertex, or zero",
    scope := .provedFinite },
  { name := "regular three-product chart transitions instantiate the twisted sheet transfer",
    scope := .provedFinite },
  { name := "opposite-diamond equivalence reconstructs exactly three Hasse directions \
      on the Boolean tangent cube",
    scope := .provedFinite },
  { name := "order isomorphisms transport diamond directions functorially and nontrivial \
      path comparison obstructs global labels",
    scope := .provedFinite },
  { name := "reversible sheet connection obeys the exact nonnegative Dirichlet-energy identity",
    scope := .provedFinite },
  { name := "the sheet connection-Laplacian kernel is exactly the parallel-section space",
    scope := .provedFinite },
  { name := "full S3 holonomy plus positive connectivity makes the sheet Laplacian kernel trivial",
    scope := .provedFinite },
  { name := "a connected four-state Boolean-chart connection realizes full S3 holonomy \
      and has trivial sheet-Laplacian kernel",
    scope := .provedFinite },
  { name := "the Boolean causal scheme has three distinct primitive-direction CSpec points \
      on which the witnessed chart loops realize full S3 holonomy",
    scope := .provedFinite },
  { name := "the canonical principal-point CSpec map collapses the two middle routes \
      of the naive four-event causal diamond",
    scope := .provedFinite },
  { name := "principal CSpec embedding is equivalent to future distinguishability, \
      and direction defects are exactly strict-future collisions",
    scope := .provedFinite },
  { name := "filled regular triple overlaps have identity boundary holonomy, so the \
      two witnessed transposition triangles are necessarily unfilled",
    scope := .provedFinite },
  { name := "one global finite causal CSpec has future-distinct regular points, an \
      unfilled four-chart nerve, and full S3 path-comparison monodromy",
    scope := .provedFinite },
  { name := "positive interior source sign alone does not force decisive records",
    scope := .provedFinite },
  { name := "rank-two-to-three charge-value and threshold partitions are not decoherent",
    scope := .provedFinite },
  { name := "chamber Poincare action is non-faithful",
    scope := .provedFinite },
  { name := "structural mass-gap and Wilson flows erase parameters",
    scope := .provedFinite },
  { name := "actual sprinkling links recover the null cone",
    scope := .conditionalBridge },
  { name := "bare Poisson-sprinkling K_F spectrum converges to J_4",
    scope := .empiricalNegative },
  { name := "quantum superpositions of causal orders", scope := .openTarget },
  { name := "relational/diffeomorphism-invariant observables",
    scope := .openTarget },
  { name := "2+1D local-zero/global-nonzero quantum benchmark",
    scope := .openTarget },
  { name := "nontrivial coarse-graining and renormalization flow",
    scope := .openTarget },
  { name := "ordinary GR and QFT recovered in the infrared",
    scope := .openTarget },
  { name := "higher-rank curvature dynamics extends the reflection-odd volume residual, \
      with subexponential stability, complement symmetry, and chirality source",
    scope := .openTarget },
  { name := "actual regular causal or CSpec neighborhoods assemble an intrinsic locally \
      three-sheeted diamond-direction cover",
    scope := .openTarget },
  { name := "physical sequential-growth or CSpec dynamics independently generates, \
      rather than receives, the constructed unfilled full-S3 global atlas",
    scope := .openTarget },
  { name := "the causal sheet connection selects a simple lowest eigenline or canonical \
      ground-space projector compatible with projective amplitudes",
    scope := .openTarget },
  { name := "protected records and an evaluable infinite charge-divergence tail event",
    scope := .openTarget }
]

private def hasScope (scope : ClaimScope) (entry : ClaimEntry) : Bool :=
  decide (entry.scope = scope)

/-- Regression check: the ledger contains exactly the intended scope split. -/
theorem claim_ledger_counts :
    claimLedger.length = 119
    ∧ (claimLedger.filter (hasScope .provedFinite)).length = 104
    ∧ (claimLedger.filter (hasScope .conditionalBridge)).length = 4
    ∧ (claimLedger.filter (hasScope .empiricalNegative)).length = 1
    ∧ (claimLedger.filter (hasScope .openTarget)).length = 10 := by
  decide

/-! ## 2. Constant families are not nontrivial density flows -/

/-- A family has nontrivial density dependence if two densities give
different values.  This is intentionally weaker than any claim about a
renormalization group; it is merely a guard against calling a definitionally
constant family a nontrivial flow. -/
def HasNontrivialDensityDependence {α : Type*} (family : ℝ → α) : Prop :=
  ∃ ρ₁ ρ₂ : ℝ, family ρ₁ ≠ family ρ₂

/-- The current chamber matrix family has no nontrivial density dependence.
The density argument is ignored by `H_chamber_at_density`. -/
theorem chamber_family_not_density_dependent :
    ¬ HasNontrivialDensityDependence H_chamber_at_density := by
  rintro ⟨ρ₁, ρ₂, hne⟩
  exact hne (H_chamber_density_independent ρ₁ ρ₂)

/-- The current top-eigenvalue family is likewise constant in density. -/
theorem top_eigenvalue_not_density_dependent :
    ¬ HasNontrivialDensityDependence lambda_top_at_density := by
  rintro ⟨ρ₁, ρ₂, hne⟩
  exact hne (lambda_top_density_independent ρ₁ ρ₂)

/-- The current chamber-gap family is likewise constant in density. -/
theorem chamber_gap_not_density_dependent :
    ¬ HasNontrivialDensityDependence chamber_gap_at := by
  rintro ⟨ρ₁, ρ₂, hne⟩
  exact hne (chamber_gap_density_independent ρ₁ ρ₂)

/-! ## 3. Reusable infrared-recovery interface -/

/-- A scale-indexed observable whose infrared behavior can be tested.

Future causal-set work should instantiate `State` with actual microscopic or
coarse-grained states.  The scale must affect `stateAtScale` or `observable`
through a defined coarse-graining/dynamics, rather than being an unused index.
-/
structure IRObservableFlow (State : Type*) where
  stateAtScale : ℕ → State
  observable : State → ℝ
  targetValue : ℝ

/-- The observable approaches its declared infrared target. -/
def IRObservableFlow.ConvergesInIR {State : Type*}
    (flow : IRObservableFlow State) : Prop :=
  Tendsto (fun scale => flow.observable (flow.stateAtScale scale))
    atTop (𝓝 flow.targetValue)

/-- The observable changes somewhere along the finite-scale flow. -/
def IRObservableFlow.HasNontrivialScaleDependence {State : Type*}
    (flow : IRObservableFlow State) : Prop :=
  ∃ scale₁ scale₂ : ℕ,
    flow.observable (flow.stateAtScale scale₁) ≠
      flow.observable (flow.stateAtScale scale₂)

/-- A convenient target for claims that specifically require both convergence
and evidence of a nonconstant finite-scale flow.  Not every universal observable
must satisfy the second conjunct; callers should use it only when claiming a
nontrivial renormalization trajectory. -/
def IRObservableFlow.IsNontrivialRecoveryWitness {State : Type*}
    (flow : IRObservableFlow State) : Prop :=
  flow.ConvergesInIR ∧ flow.HasNontrivialScaleDependence

/-! ## 4. The 2+1D topological benchmark -/

/-- Data that a 2+1-dimensional quantum-gravity benchmark must expose.

Passing requires more than the standard local polarization count: the local
bulk sector must vanish while a global/topological sector survives, and the
gauge quotient, relational observables, and quantum dynamics must actually be
constructed.  No witness is asserted in this audit file.
-/
structure ThreeDBenchmarkData where
  localPhysicalModes : ℕ
  globalPhysicalModes : ℕ
  gaugeQuotientConstructed : Bool
  relationalObservablesConstructed : Bool
  quantumDynamicsConstructed : Bool

/-- Success criterion for the proposed 2+1D benchmark. -/
def ThreeDBenchmarkData.Passes (data : ThreeDBenchmarkData) : Prop :=
  data.localPhysicalModes = 0
    ∧ 0 < data.globalPhysicalModes
    ∧ data.gaugeQuotientConstructed = true
    ∧ data.relationalObservablesConstructed = true
    ∧ data.quantumDynamicsConstructed = true

/-! ## Trust regression output -/

#print axioms claim_ledger_counts
#print axioms chamber_family_not_density_dependent
#print axioms top_eigenvalue_not_density_dependent
#print axioms chamber_gap_not_density_dependent

end UnifiedTheory.Audit.QuantumGeometryStatus
