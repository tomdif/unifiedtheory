# Framework Status (August 2026)

> **Quantum-gravity/Hauptvermutung bridge update (2026-08-20):** The current
> capstone is documented in
> [`QUANTUM_GRAVITY_HAUPTVERMUTUNG_CAPSTONE.md`](QUANTUM_GRAVITY_HAUPTVERMUTUNG_CAPSTONE.md).
> New Lean audit modules formalize the Dorau--Much/Jacobson horizon constant
> chain, exact finite entropy focusing, finite causal-growth birth-law
> normalization, finite-to-continuum horizon flux error control, the physical
> certificate interface for applying the quantitative Hauptvermutung, and the
> quotient construction of label/diffeomorphism-invariant observables. These
> are checked bridge interfaces, not a completed proof of full continuum quantum
> gravity. The latest finite control theorem adds horizon-orthogonal
> least-defect growth: a raw defect source has a unique covariance residual
> that does not change first-order horizon focusing. The next obstruction is
> also identified exactly: the finite second central area response is
> `-Cov(J, centered(S)^2)`. A null-cone scan now finds sample-mean
> two-channel defect mixtures with near-zero second-order leakage and large
> gap response. A follow-up Hauptvermutung-basis scan replaces shell proxies
> with interval-dimension, relation-bias, and count-window proxy channels; the
> low-leakage mechanism survives, but not yet as a stable physical certificate.
> The newest certificate-error basis uses named `countWindow`, `curvatureBias`,
> and `pairConsistency` proxy channels and gives the current best low-leakage
> candidate, but coefficient drift remains. Lean now also states the exact
> protected certificate-error source interface: a source with zero first
> horizon covariance, zero second-order horizon leakage, and negative
> certificate-error response preserves horizon area through the finite second
> central response while descending that certificate. A refinement version
> proves second central area response tends to zero when leakage tends to zero.
> A residualized two-channel bridge covers the null-cone scans directly, and
> the abstract certificate error is now specialized to the actual displayed
> Hauptvermutung distortion observable
> `(countWindow + curvatureBias + countWindow*curvatureBias)*scale
> + pairConsistency/2`. The newest descent gate proves that if the finite
> Taylor remainder is at most half of the protected descent margin, the
> displayed distortion strictly decreases; a geometric-majorant wrapper gives
> convergence to zero from `D_n <= D_0*q^n`, `0 <= q < 1`. The sequence-level
> bridge proves this same descent keeps first-order and second central
> horizon-area response zero at every finite stage. The current gate probe
> shows the certificate-basis candidate passes the half-remainder gate on all
> sampled parents at small steps once the source is oriented locally by parent;
> Lean now proves this sign orientation preserves horizon protection and makes
> every nonzero distortion response strictly descending. The new physics lead
> is documented in
> [`HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md`](HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md):
> a horizon-invisible geometric relaxation channel, packaged by
> `orientedProtectedHauptvermutungDistortionSource_bridge`, can descend the
> displayed Hauptvermutung distortion observable while leaving the Dorau--Much
> horizon area response zero through second order. The latest attack adds
> `canonicalHorizonInvisibleDescentSource`: projecting the certificate
> observable itself off the horizon source gives a parent-local gradient that
> Lean proves descends at residual-variance rate with zero first-order horizon
> response; the empirical null-cone correction `+ 3.5 residual(-gap)` nearly
> cancels second-order leakage while preserving the local descent gate. Lean
> now packages the corrected source in
> `correctedCanonicalHorizonInvisibleDescentSource_protected_bridge`, and the
> same `t=3.5` correction passes deeper `n=20` local gate checks on two seeds.
> A new coefficient scan estimates the leakage-null root directly; at `n=18`,
> `paths=4`, the two seed magnitudes are `3.67279` and `3.55183`, making
> coefficient stability the next finite proof target. Corrector comparison
> shows the effective `-gap` correction is the interior BDG channel after the
> horizon-boundary component is projected away; Lean now proves that this
> corrector-gauge quotient preserves first-order response and second-order
> horizon leakage, preserves roots of the leakage null-cone quadratic, and
> transports the full protected corrected-source bridge. The newest concrete
> specialization defines the private-marker bridge-census defect recovered from
> global order incidence, proves the canonical transport has zero defect while
> every noncanonical transport has positive defect, identifies the
> pair-consistency distortion with this defect, and applies the
> horizon-orthogonal corrected-source bridge directly to that order-derived
> target. Lean also proves the summed finite bridge distortion is nonnegative
> and vanishes exactly when every candidate transport is the order-recovered
> one. The TOE gap-closing roadmap is now tracked in
> [`TOE_COMPLETION_PLAN.md`](TOE_COMPLETION_PLAN.md). Its first Lean interface
> defines `physicalHauptvermutungDistortion`, proves the aggregate zero set
> under nonnegative component hypotheses, proves the bridge-census component is
> a strict transport minimizer inside that aggregate, and packages
> `PhysicalGrowthSuppliesRepairSource`, a horizon-protected contraction gate
> for physical repair sources with controlled finite remainders. The new
> `PhysicalGrowthRepairRefinement` wrapper records that gate at every finite
> refinement stage and proves stepwise horizon protection together with
> `D_{n+1} < D_n`; under a geometric majorant `D_n <= D_0*q^n`,
> `0 <= q < 1`, Lean now proves aggregate convergence `D_n -> 0`. A further
> step-factor gate derives that majorant from `D_{n+1} <= q * D_n`; the
> newest relative-margin gate derives the step factor from
> `(1 - q)*D_n <= step_n*descentRate_n/2`; the newest descent-budget gate
> packages the same requirement as `2*(1 - q)*D_n <= step_n*descentRate_n`,
> and the newest rate-floor gate derives that budget from
> `rateFloor_n*D_n <= descentRate_n` and
> `2*(1 - q) <= step_n*rateFloor_n`. The newest uniform gate derives
> convergence with `q = 1 - stepFloor*gamma/2` from
> `gamma*D_n <= descentRate_n`, `stepFloor <= step_n`, and
> `0 < stepFloor*gamma <= 2`, making those uniform bounds the next theorem
> target. The newest variable-product gate also proves convergence from
> `D_{n+1} <= q_n*D_n` and `Product_{k<n} q_k -> 0`, with an explicit
> variable-rate-floor specialization `q_n = 1 - step_n*rateFloor_n/2`. The
> newest uniform-bound bridge derives that product decay from
> `0 <= q_n <= qBound < 1`; the newest gain-window gate derives this bound
> from `0 < beta`, `beta <= step_n*rateFloor_n`, and
> `step_n*rateFloor_n <= 2`; the newest physical-total version discharges the
> external `D_n >= 0` side condition when `D_n` is exactly
> `physicalHauptvermutungTotalDistortion` with nonnegative component
> observables; the newest local-descent version replaces the global
> `rateFloor_n*D_n <= descentRate_n` assumption with finite per-cell descent
> certificates whose sum is `descentRate_n`; the newest uniform local-rate
> version derives convergence from those local certificates together with
> `gamma <= rateFloor_n`, `stepFloor <= step_n`, and
> `0 < stepFloor*gamma <= 2`; the newest source-local version identifies those
> certificates with the actual source's per-cell negative first-order response
> contributions and proves they sum to `-linearResponse(S_n, D_n)`; the newest
> centered-source floor gate derives those cellwise bounds from
> `rateFloor_n <= -w_{n,i}*centered(S_n)_i`; the newest weighted
> anti-alignment gate splits that into nonnegative weights, a weighted rate
> floor, and `alignment_{n,i} <= -centered(S_n)_i`; the newest uniform
> weighted-alignment gate derives the weighted rate floor from uniform lower
> bounds on sampling weight and anti-alignment amplitude; the newest
> rate-floor-free gate replaces `rateFloor_n` with the direct uniform bound
> `gamma <= weightFloor*alignmentFloor`; the newest direct centered-source
> floor gate removes the auxiliary alignment observable and proves the same
> theorem from `gamma <= weightFloor*sourceFloor`,
> `weightFloor <= w_{n,i}`, and
> `sourceFloor <= -centered(S_n)_i`; the newest gamma-free product gate sets
> the rate constant to `weightFloor*sourceFloor` itself and only requires
> `0 < stepFloor*(weightFloor*sourceFloor) <= 2`; the newest positive-floor
> gate derives that strict positivity from
> `0 < stepFloor`, `0 < weightFloor`, and `0 < sourceFloor`; the newest
> clipped-rate gate removes the product upper-bound side condition by using
> the effective rate
> `min (weightFloor*sourceFloor) (1/stepFloor)`, so the stability product is
> automatically at most `1`; the newest stagewise clipped-rate gate removes
> global uniformity at this layer and proves convergence from positive
> stage-dependent weight/source floors plus decay of the corresponding clipped
> contraction-factor product; the newest clipped-gain gate derives that decay
> from a uniform positive lower bound
> `beta <= step_n*min(weightFloor_n*sourceFloor_n, 1/step_n)`; the newest
> unclipped-gain gate derives that clipped bound from
> `beta <= 1` and
> `beta <= step_n*(weightFloor_n*sourceFloor_n)`; the newest component-gain
> gate derives that ordinary gain floor from separate lower bounds on step
> size, weight-floor amplitude, and centered-source-floor amplitude; the
> newest positive component-floor gate removes the auxiliary `beta` by setting
> `beta = min 1 (stepFloor*(weightBase*sourceBase))`, so positive component
> floors themselves imply the protected convergence theorem; the newest direct
> uniform component-floor gate removes the auxiliary stagewise floor sequences
> and asks only for positive uniform lower bounds on `step_n`, `w_{n,i}`, and
> `-centered(S_n)_i`; the newest certificate theorem packages those floors
> with the physical-total identity, nonnegative components, descent identity,
> and refinement data as `PhysicalHauptvermutungConvergenceCertificate`, then
> proves protected convergence from that single certificate; the newest
> exact-recovery theorem shows that if every noncanonical bridge candidate
> stays at least `epsilon > 0` above zero distortion, then the certificate
> forces eventual equality with the canonical CSpec bridge candidate; the
> newest bridge-defect-floor theorem derives that uniform gap from the local
> bridge penalty itself:
> `epsilon <= bridgeCensusDefect(edge_{n,i}, candidate_{n,i})` at every wrong
> local transport; the newest parameter-free recovery theorem proves the
> bridge census has fixed wrong-transport floor `18`, so the convergence
> certificate alone forces eventual canonical CSpec bridge recovery; the
> newest operational recovery corollaries then prove eventual zero bridge
> total and eventual order-incidence recovery of the candidate transport; the
> newest residual-split theorems prove that the post-recovery aggregate is
> exactly the count/curvature/spectral base distortion, that this base and
> each of its finite local components tend to zero, and that a fixed positive
> residual gap forces eventual exact zero total; those hypotheses are now
> packaged as `PhysicalHauptvermutungExactRecoveryCertificate`, which proves
> horizon protection plus eventual full operational recovery and gives a
> finite threshold after which `PhysicalHauptvermutungRecoveredStage` holds;
> the newest observable-zero corollary expands that threshold into total,
> physical-total, base, bridge, residual, canonical-transport, and incidence
> recovery facts.
> The remaining work is to derive the physical certificates and infrared GR/QFT
> recovery from the actual causal-growth dynamics.

> **TOE swarm integration update (2026-08-21):** Six bounded agents reviewed
> the remaining TOE gates.  Two results were integrated into
> `KFCausalCSpecBridgeDefectObservable.lean`: the base zero-set theorem
> `physicalHauptvermutungBaseDistortion_eq_zero_iff`, and the direct aggregate
> rate theorem
> `physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor`.
> The latter proves protected convergence from a positive aggregate rate floor
> and positive step floor, clipping the effective rate internally; it therefore
> separates the logical convergence gate from the stronger pointwise
> centered-source floor.  The prediction ledger is now mirrored in
> `PREDICTIONS_PREREGISTRATION_LEDGER.json`; the README points to that five-row
> preregistration set instead of treating older conditional proposals as the
> canonical forward list.
> `KFTOESevenGateAttack.lean` now mirrors the seven TOE gates as formal closure
> records and exposes the checked Gate 1, Gate 2, and Gate 3 theorem hooks:
> signed atlas fiber sums imply raw complete-chiral noncancellation, base
> Hauptvermutung distortion zero is equivalent to zero count/curvature/spectral
> components under nonnegativity, and a
> `PhysicalHauptvermutungConvergenceCertificate` gives horizon protection plus
> total-distortion convergence.  It also proves Gate 7 protocol closure from
> the existing preregistration/falsifiability ledger: frozen forward
> predictions, uncertainty/falsification rows, future-test horizons, and a
> failure ledger are all recorded. Gates 4-6 remain explicit closure records,
> and Gate 7 still awaits the future empirical comparisons themselves.

> **Gate 1 support update (2026-08-21):**
> `KFCausalSetCompleteChiralLaw.lean` now proves
> `completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical`.  The
> canonical chiral causal-growth law therefore has zero transition amplitude
> outside the physical one-element birth graph; the proof reduces the numerator
> to an empty labeled transition fiber before normalization.  The same module
> now also packages parent-isomorphism covariance, finite projectivity, and
> infinite-cylinder quantum consistency for the concrete law as
> `completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic`,
> `completeChiralCausalSetGrowthLaw_gate1_projective`, and
> `completeChiralCausalSetGrowthLaw_gate1_quantum_consistent`.

> **Gate 4 recovered-stage update (2026-08-21):**
> `KFCausalCSpecRecoveredStageGRLimit.lean` now connects exact recovered CSpec
> stages to the entropy-flux RSS/Poisson error budget.  It proves
> `PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero` and the eventual
> and threshold versions for `PhysicalHauptvermutungExactRecoveryCertificate`.
> This does not prove a continuum GR limit; it closes the finite plumbing from
> zero count-window/curvature residuals to zero cellwise horizon-flux error.
> `KFCausalCSpecRecoveredStageBDGInterface.lean` now adds
> `RecoveredStageBDGAsymptoticInterface`, bundling exact finite recovery with
> the named per-layer BDG/RNC asymptotic hypotheses.  Its combined theorems
> prove zero RSS/Poisson error together with the BDG d'Alembertian limit once
> those analytic layer hypotheses are supplied.
> `KFCausalCSpecRecoveredStageBDGProfile.lean` now converts real high-density
> profile limits sampled along a recovered-stage density sequence into the
> sequence-level `layer_asymptotics` field.  The next Gate 4 target is therefore
> the physical-law proof of those real BDG/RNC profile limits.
> `KFCausalCSpecRecoveredStageBDG4DOperator.lean` now packages the existing
> reduced 4D BDG operator theorem as `BDG4DOperatorProfileData`, samples it
> along any density sequence tending to infinity, and turns it into a
> one-channel `BDGProfileSequenceAsymptotics` object.  Gate 4 now needs the
> physical CSpec growth law and recovered charts to supply that data bundle.
> `KFCausalCSpecRecoveredStageBDG4DRecovered.lean` now combines that data bundle
> with exact finite recovery.  `RecoveredStageBDG4DOperatorInterface` proves
> eventual recovered stages, convergence of the sampled reduced 4D operator,
> and the combined zero RSS/Poisson error plus operator-limit theorem.
> `KFCausalCSpecRecoveredStageBDG4DChart.lean` now separates the exact finite
> CSpec sequence from the recovered local chart profile data.  The new
> `RecoveredStageBDG4DChartInterface` builds the concrete recovered-stage
> operator interface from chart-supplied density and `BDG4DOperatorProfileData`
> and proves the combined zero RSS/Poisson error plus chart-operator limit.
> `KFCausalCSpecRecoveredStageBDG4DPhysicalChart.lean` now feeds that chart
> interface from a sequence of `PhysicalGrowthHauptvermutungCertificate`s.  The
> new `RecoveredStageBDG4DPhysicalChartInterface` proves each finite certificate
> applies the quantitative Hauptvermutung bridge, the displayed chart
> distortion bound tends to zero, and exact finite recovery plus supplied 4D
> operator profile data gives zero finite horizon error, sampled operator
> convergence, and chart distortion collapse together.
> `KFCausalCSpecRecoveredStageBDG4DMatchedChart.lean` now removes the separate
> chart-channel convergence assumptions when the physical chart certificate's
> scalar channels are matched to exact recovered residual sums.  The recovered
> count, curvature, and spectral/locality sums tend to zero, so a matched chart
> certificate instantiates the physical-chart bridge directly.
> `KFCausalCSpecRecoveredStageBDG4DScheduledDensity.lean` now removes the
> separate density-convergence assumption when the chart certificate density is
> an affine positive-step refinement schedule.  Lean proves
> `affineDensity_tendsto_atTop`, instantiates the matched physical-chart
> interface, and preserves the combined zero finite horizon error, sampled 4D
> operator convergence, and chart-distortion collapse theorem.
> `KFCausalCSpecRecoveredStageBDG4DOperatorSplit.lean` now factors the
> monolithic `BDG4DOperatorProfileData` target into profile-function, scale,
> regularity, uniform-bound, support, and cone-bound certificates.  Lean proves
> the split package assembles back into the operator profile data and feeds the
> scheduled-density recovered chart bridge.
> `KFCausalCSpecRecoveredStageBDG4DConeBound.lean` now reduces the combined
> cone-bound certificate to lower lightcone support, an active-region weighted
> `f4D` kernel bound, the existing uniform chart-profile bound, and one
> cone-scale calibration inequality.  Lean proves this active kernel/profile
> package assembles into the split operator data and feeds the
> scheduled-density recovered chart bridge.
> `KFHopfSpinorBlochBridge.lean` now connects the finite spinor/qubit side to
> the Bloch/projective side: Lean proves the real-coordinate Hopf identity
> `|Bloch(psi)|^2 = |psi|^4`, the unit-spinor-to-unit-Bloch corollary, and
> invariance of all Bloch coordinates under common unit `U(1)` phase
> multiplication.  It also proves those coordinates agree with the repo's
> existing `WignerHardQubit.blochVector`.  This is the algebraic Hopf core,
> not yet the full topological fibration or Chern-class story.
> `KFHopfPhaseQuotient.lean` now names the algebraic common-phase quotient:
> common unit-phase related real-coordinate spinors form a Lean `Setoid`,
> spinor norm is preserved on equivalence classes, and all three Bloch
> coordinates descend to the quotient.
> `KFHopfUnitSphereQuotient.lean` restricts this to normalized spinors and
> proves the set-level algebraic Hopf statement `S^3 / U(1) -> S^2`: every
> normalized phase class carries a well-defined unit Bloch-sphere observable.
> `KFHopfFiberExactness.lean` proves the exact fiber converse at the same
> algebraic scope: equal unit Bloch observables are exactly common-`U(1)`
> phase related normalized spinors, and the normalized quotient-to-Bloch map is
> injective.  Surjectivity and the topological fibration remain separate.
> `KFHopfSurjectivity.lean` closes the set-level algebraic quotient: every unit
> Bloch point has a normalized spinor representative, and the normalized
> phase-quotient-to-Bloch map is bijective.  Topology, local trivializations,
> Chern classes, and continuum spin bundles remain outside this theorem.
> `KFHopfQuotientInverse.lean` packages that bijection as a noncomputable
> inverse from unit Bloch points to normalized phase classes, with both inverse
> laws proved.
> `KFRecoveredCSpecHopfFiber.lean` now lifts the Hopf bridge to local
> recovered-stage fiber data: for every stage and site, a normalized local
> Hopf spinor has a unit Bloch observable, agrees with the repo Bloch vector,
> and remains physically unchanged under local stagewise `U(1)` phase choices.
> This closes the finite local fiber attachment, not the continuum QFT dynamics.
> `KFRecoveredCSpecHopfQuotientFiber.lean` now connects that local fiber data
> to the normalized phase quotient: each recovered stage/site determines a
> phase class and a unit Bloch-sphere quotient observable, and local stagewise
> `U(1)` rotations leave both unchanged.
> `KFRecoveredCSpecHopfBornObservable.lean` now derives local Pauli-X/Y/Z Born
> probability pairs from those quotient Bloch observables; Lean proves each
> plus/minus pair is nonnegative, bounded by one, sums to one, and is invariant
> under local stagewise `U(1)` gauge rotation.
> `KFRecoveredCSpecHopfBornAxisObservable.lean` now extends the local Born
> interface to arbitrary unit Bloch measurement axes: Lean proves the dot
> expectation lies in `[-1,1]`, the resulting plus/minus pair is a valid
> probability pair, it is locally `U(1)` gauge-invariant, and the coordinate
> axes recover the Pauli-X/Y/Z pairs.
> `KFRecoveredCSpecHopfBornTomography.lean` now proves local finite qubit
> tomography: binary Born expectations recover the Pauli X/Y/Z Bloch
> coordinates, arbitrary-axis expectations are `a · B`, and the reconstructed
> local Bloch observable is invariant under local stagewise `U(1)` gauge
> rotation.
> `KFRecoveredCSpecHopfBornSeparation.lean` closes the finite local
> observational-completeness statement: equality of Pauli Born pairs, equality
> of all arbitrary-axis Born pairs, and equality of the recovered quotient
> Bloch observable are equivalent at any two local recovered-stage sites.
> `KFRecoveredCSpecHopfBornPhaseClassSeparation.lean` upgrades that statement
> through the algebraic Hopf quotient: equality of Pauli Born data, equality of
> all-axis Born data, equality of quotient Bloch observables, and equality of
> recovered normalized phase classes are equivalent locally.
> `KFRecoveredCSpecHopfBornPhaseClassReconstruction.lean` then reconstructs the
> recovered normalized phase class from the three Pauli Born expectations and
> proves the reconstruction is invariant under local stagewise `U(1)` rotation.
> `KFHopfProjectiveQubitState.lean` packages the normalized Hopf phase quotient
> as a finite projective-qubit state API: each state has Bloch and Born
> observables, Pauli Born expectations reconstruct the state, and Pauli/all-axis
> Born data are equivalent to state equality.
> `KFRecoveredCSpecHopfProjectiveQubitState.lean` identifies each recovered
> stage/site phase class with that state API and proves matching Bloch/Born
> observables, local projective-state reconstruction, local `U(1)` gauge
> invariance, and Born-data equivalence to recovered projective-state equality.
> `KFRecoveredCSpecHopfProjectiveQubitCarrier.lean` then bundles each recovered
> local projective state, Bloch point, and Born family as a compact carrier and
> proves carrier reconstruction, local gauge invariance, and Pauli/all-axis Born
> separation of carrier equality.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierField.lean` lifts that carrier to a
> recovered stagewise field, proving pointwise Pauli/all-axis Born data are
> equivalent to field equality, with whole-stage reconstruction and local
> `U(1)` gauge invariance.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRelabel.lean` proves finite
> site-relabel covariance: carrier-field reconstruction and Pauli/all-axis Born
> data commute with site bijections, relabeling is injective on fields, and
> recovered-stage gauge invisibility survives relabeling.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRestriction.lean` adds the
> non-bijective probe-map companion: carrier fields pull back along arbitrary
> probes, reconstruction and Pauli/all-axis Born data commute with pullback,
> recovered-stage gauge invisibility survives restriction, and surjective probes
> reflect carrier-field equality plus Born-data equality.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCover.lean` then adds the
> finite cover/descent theorem: for any jointly-surjective family of probe maps,
> equality and Pauli/all-axis Born-data equality on every pulled-back probe are
> equivalent to equality and Born-data equality of the whole carrier field, with
> recovered-stage gauge invisibility still pointwise visible on every probe.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverRefinement.lean` proves
> the reindex-refinement companion: surjective reindexings of a probe cover
> preserve and reflect joint surjectivity, carrier-field equality tests, and
> Pauli/all-axis Born-data tests, while recovered-stage gauge invisibility
> remains true on all refined probes.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCommonRefinement.lean` adds
> the finite common-refinement theorem: two jointly-surjective probe covers have
> a fiber-product common refinement that is jointly-surjective and still
> separates whole-field equality and Pauli/all-axis Born-data equality, with
> recovered-stage gauge invisibility on every common-refinement probe.
> `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverIndependence.lean`
> packages cover-choice independence: any two jointly-surjective probe covers
> give equivalent carrier-field equality and Pauli/all-axis Born-data tests,
> and both are equivalent to the common-refinement tests.  Recovered-stage
> local `U(1)` gauge invisibility remains true on both covers.

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
> `KFCausalCSpecAtlasCocycleNoGo.lean` upgrades this observation to an exact
> criterion: principal CSpec points embed iff the causal order is
> future-distinguishing, and a direction defect is exactly a collision of
> strict-future signatures. It also proves that a filled regular triple overlap
> has identity boundary holonomy. The two witnessed transposition triangles
> therefore cannot be filled Cech 2-simplices; a global realization must have
> unfilled nerve cycles or wind around an excluded defect.
> `KFCausalCSpecGlobalAtlas.lean` closes finite global existence. One
> 140-event causal scheme contains four exact Boolean chart cores and 60
> pairwise-distinct regular principal `CSpec` points. Every chart pair shares
> continuation records, every triple of distinct charts has empty regular
> intersection, and common-continuation membership in the native prime future
> sets uniquely recovers the direction transport. The two unfilled loops give
> the adjacent transpositions and six explicit words exhaust `S3`. Thus one
> global finite causal/CSpec object now realizes the full nontrivial atlas.
> The descent package separately certifies witness independence, total
> three-sheet overlap matching, identity/reverse laws, and the Cech cocycle on
> every genuine common regular point. Full monodromy acts transitively, forbids
> a path-independent global sheet labeling, and makes the associated rank-two
> connection's parallel-section space zero. “Connected cover” is used only in
> this algebraic transitivity sense because upstream `CSpec` has no topology.
> The construction is an existence witness whose causal order was designed to
> encode those overlap continuations; it is not derived from the repository's
> physical sequential-growth dynamics. The pinned native `CSpec` also has no
> topology/open-cover API, no numerical gap is bounded, and no simple lowest
> eigenline or canonical ground projector is selected.
> `KFCausalHolonomyBirthCouplingLaw.lean` couples the finite holonomy
> instrument to the actual harmonic birth amplitudes. The rank-one law matches
> exactly; at the first three-bin parent the blind product has Born mass
> `3681/2113`, and no scalar rescaling preserves both normalizations. Its
> zero-sum Born-shell correction has exact scale `sqrt(2113/4465)` and yields a
> six-outcome CPTP projective process. `KFCausalBornShellGeneralLaw.lean` now
> proves the arbitrary finite-rank version and, crucially, centers over the
> physical successor support rather than all causets of that rank. A compatible
> all-rank scale profile gives a law that vanishes on forbidden births, has
> coherent sum and Born mass both one at every parent, and inherits normalized,
> strongly positive, exactly projective infinite-cylinder semantics. The
> squared radial modulus is unique off the uniform boundary. The actual
> harmonic transition is now proved to vanish on every non-extension child.
> Its centered squared norm is an explicit real Born excess; strict positivity
> constructs a square-root scale. A new quotient-safe true-relation count
> proves that isomorphic child fibers preserve precursor cardinality. The
> empty and full precursor fibers are therefore singletons, and their harmonic
> transitions are distinct at every positive rank (phase at rank one,
> magnitude thereafter). This proves all-parent nonuniformity and closes the
> exact frontier theorem: the canonical support-preserving harmonic scale and
> its coherently/Born normalized, projective, strongly positive cylinder law
> now exist unconditionally for both chiralities. The companion exact-`Q(i)`
> audit exhausts all 406 unlabeled parents through rank 6 with no counterexample.
> The canonical profile is now definitionally the explicit nonnegative real
> square-root scale rather than an arbitrary `Classical.choose` witness. Its
> value is reflection invariant, and the completed transitions for the two
> chiralities are exact complex conjugates, so the repair introduces no hidden
> absolute-handedness choice.
> Independently of the causal specialization, a strictly convex norm-shell
> theorem proves that the nonnegative radial completion is the unique closest
> fixed-norm point to the raw zero-sum amplitude. Thus ray preservation is
> forced by a least-Hilbert-disturbance principle.
> The support-relative specialization now constructs the physical-successor
> Euclidean carrier, proves its squared norm is exactly the Born excess, and
> proves the implemented square-root correction uniquely `L2`-closest among
> every supported coherent Born-one competitor.
> `KFCausalBornShellRelaxationDynamics.lean` replaces the interpretation of
> that minimizer as a bare postulate with an explicit local restoring law on
> the zero-sum carrier. The radius satisfies
> `r_(n+1) = r_n + (R-r_n)/2`, the radial defect is halved per tick, and its
> squared Lyapunov defect contracts by exactly `1/4`. The lift preserves the
> carrier ray, commutes with every real linear isometry, and converges in norm
> to the implemented physical Born correction. A rigidity theorem proves
> more generally that every time-homogeneous fixed-retention linear response
> is the affine semigroup `R + a^n(r_0-R)`; every `0 <= a < 1` has the same
> Born-shell attractor, so `a` changes only the relaxation clock. The endpoint,
> positive ray, and least-change completion are therefore consequences of
> this deeper dynamics rather than independent assumptions.
> A companion no-go proves that no linear operator on the same amplitude
> carrier can realize even one universal nonzero-target relaxation tick: the
> map necessarily breaks scalar homogeneity. It therefore cannot be presented
> as closed unitary/Schrodinger evolution. Its honest physical address is an
> effective dissipative or conditional dynamics of unnormalized causal
> amplitudes, or a reduced law induced by a larger environmental dilation.
> `KFCausalBornShellProximalDynamics.lean` derives the relaxation update one
> layer deeper. The midpoint is the unique global minimizer of the local action
> `(next-current)^2 + (next-target)^2`, equivalently the unique implicit-Euler
> solution whose displacement equals its remaining Born defect. For positive
> inertia and restoring weights, completing the square gives the unique update
> and proves that its retention is
> `inertia / (inertia + restoring)`, strictly between zero and one. Thus the
> full stable affine family follows from weighted proximal response, and equal
> microscopic penalties select the displayed half-defect clock.
> The same module proves that the radial mass is exactly—not merely a proxy
> for—the existing complex Born mass of every finite supported causal profile.
> The observable mass converges to one without crossing the Born shell, and
> its absolute error falls to at most `3/4` of its previous value per
> microscopic tick. The
> sharper `1/4` contraction applies to the squared radial Lyapunov defect.
> `KFCausalBornEquilibrationLaw.lean` supplies the unique continuous-time
> semigroup behind those updates. Its effective equation is
> `dr/dt = gamma * (R-r)`, with exact solution
> `r(t)=R+exp(-gamma*t)(r(0)-R)`. It is the negative gradient flow of the
> quadratic Born-shell potential, and its Lyapunov identity is exactly
> `dL/dt=-2*gamma*L`. Thus stability fixes the sign: positive `gamma` makes
> the Born shell globally attracting, zero is neutral, and negative `gamma`
> makes it repelling. Uniqueness is proved among all differentiable solutions.
> A logarithmic tick calibration embeds every discrete retention semigroup
> exactly, while implicit Euler recovers the weighted proximal update.
> On the actual finite causal amplitude, the flow preserves physical support,
> coherent normalization, and carrier-coordinate covariance; the existing
> full complex Born mass is exactly its radial mass and converges to one
> without crossing the shell.
> A uniform branching parent still has no scalar radial repair in general, and
> the remaining physical postulate is now narrower: why microscopic causal
> growth generates this isotropic dissipative gradient flow, or which
> environment/record interaction induces it. The sign of the rate is selected
> by stability, but its magnitude and laboratory-time calibration are not
> derived from continuum experiment here. This is therefore a candidate
> effective natural law, not a microscopic unitary law or an established law
> of nature.
> `KFCausalBornRateAndDilation.lean` closes the two finite-level parameters of
> that effective law. Equal local action weights already force a half-defect
> per causal birth. Requiring the continuous flow to be the exact semigroup
> sampled after a birth of proper duration `tau_birth` then uniquely forces
> `gamma * tau_birth = log 2`; in birth-count units, `gamma = log 2`.
> The four-dimensional interval-counting clock supplies `tau_birth` from one
> counted event and the sprinkling density, yielding the positive physical
> rate `gamma = log 2 / tau_birth`. This is not convention-free: the same
> midpoint read as an implicit-Euler approximation instead forces
> `gamma * tau_birth = 1`, and Lean proves `log 2 != 1`. Thus the discrete
> growth law fixes its retention exactly, while choosing exact-flow versus
> numerical-step clock semantics remains a physical calibration decision.
> The same module constructs an explicit reversible system-bath dilation.
> A two-mode rotation with system coefficient `exp(-gamma*t)` conserves total
> radial-defect energy, is exactly invertible, and projects to the continuous
> equilibration law; the apparently lost defect is stored in the bath.
> Repetition with one fresh vacuum mode per birth reproduces the discrete
> half-defect semigroup exactly. This supplies a finite collision-model origin
> for the open dynamics, but does not derive a unique Hamiltonian, the fresh-
> bath/reset assumption, an infinite reservoir, or the absolute sprinkling
> density.
> `KFCausalBornAutonomousDilationNoGo.lean` proves that the fresh-bath clause is
> necessary for this finite dilation, not optional wording. Reusing one bath
> mode twice gives system coefficient `c^2-s^2`, while two vacuum collisions
> give `c^2`. For every strict contraction and nonzero defect these differ. In
> continuous time the individually reversible rotations with
> `c(t)=exp(-gamma*t)` therefore fail the time-addition law whenever
> `gamma,t>0`; they are not one autonomous two-mode Hamiltonian group.
> `KFCausalBornCarrierRepeatedInteraction.lean` lifts the construction to every
> real carrier. The carrier rotation is invertible, fresh vacuum collisions
> give `c^n` times the full defect vector, and system energy plus accumulated
> bath-mode defect energy is exactly conserved. On the actual physical
> successor zero-sum carrier, the reduced trajectory equals the centered vector
> of `finiteSupportBornRelaxedAmplitude` at every tick. The construction is
> coordinate-equivariant and can leave a separately supplied protected label
> untouched. Its honest boundary is sharper than before: the Born-shell
> equilibrium depends on the initial ray, so this is a ray-conditioned
> repeated-interaction model, not a universal state-independent CPTP
> instrument. The existing linear-homogeneity no-go is re-exported as a
> capstone. At this stage causal growth still has to derive the fresh
> orthogonal modes, the protected product factorization, and a
> `D(Omega,Omega)`-preserving conditional instrument.
> `KFCausalBornGrowthFreshModes.lean` closes the first item at its honest
> kinematic scope. Ranked histories factor each next step as old prefix times
> one birth, and labeled one-element extension reserves `Fin.last n` for the
> newborn while old birth slots embed through `Fin.castSucc`. The final slot is
> proved to be the unique complement of all old slots. Their standard Hilbert
> kets are orthonormal, so every physical causal step canonically grows the
> minimal record bath from `Fin n -> E` to `Fin (n+1) -> E` by one orthogonal
> carrier mode, independent of causal shape and event labels. The collision
> leaves every old record unchanged, writes `-s*c^k` times the initial defect
> permanently in birth slot `k`, is reversible on its image, and conserves the
> exact system-plus-full-record norm. Its system reduction is exactly the
> existing supported causal Born trajectory. Thus the fresh-mode/reset
> assumption is replaced by causal memory growth. What remains dynamical is
> why the Born defect couples to this canonical record tower with the selected
> rotation, plus derivation of the protected product factor and normalized
> conditional quantum instrument.
> `KFCausalBornFreshModeCompatibility.lean` separates two previously conflated
> stationarity questions. An arbitrary rank-dependent retention/leakage
> schedule has exact product-form system decay, permanent per-birth records,
> and exact total-energy conservation whenever every local block is lossless.
> The constant collision is only one specialization, and even it maps
> `E × (Fin n → E)` to a strictly larger rank-`n+1` carrier. Paper 3's aging
> theorem instead constrains stationary per-precursor amplitudes in the
> microscopic coherent Markov/action-phase law. Thus there is no formal
> contradiction and no derivation of microscopic aging: identifying the two
> coefficients would require a rank-dependent schedule. The carrier here is a
> finite direct product/direct-sum construction, not a system-environment
> tensor factor, partial trace, or state-independent CPTP instrument.
> `KFCausalBornNormalizationTransfer.lean` audits the newly registered
> Born-normalized theory. Local `sum |a|^2 = 1` makes path Born weights an exact
> cylinder martingale and kills normalization-flow churn pointwise. Exact
> binary witnesses prove that coherent and Born normalization imply neither
> one another; the funding, hbar-window, aging, necessity, dust, and selection
> results therefore require re-derivation because their complex wave equation
> is absent in the Born-only theory. The canonical harmonic Born-shell law is
> already an unconditional all-rank inhabitant of their intersection. It has
> both a diagonal Born martingale and the prior normalized strongly positive
> coherent cylinder functional. The convex measure-level interpolation between
> them is normalized and projective at every dephasing strength, nonnegative
> on `[0,1]`, and retains residual interference by the exact factor
> `1-lambda`. This closes the finite-cylinder normalization question, not the
> tail-event, record-instrument, or microscopic-selection problems; see
> `BORN_NORMALIZATION_TRANSFER_AUDIT.md`.
> `KFCausalDoubleConservationLaw.lean` upgrades the bi-normalized intersection
> from a sufficient construction to a local rigidity theorem. For every finite
> successor fiber, preservation of every incoming coherent amplitude and every
> incoming Born mass is equivalent to `sum a_e=1` and `sum |a_e|^2=1`. On an
> arbitrary finite carrier, preservation of every incoming operator amplitude
> and its full quadratic form is equivalent to `sum K_e=I` and
> `sum K_e^dagger K_e=I`. The theorem assumes neither a tensor-product
> environment nor a partial trace. The canonical all-rank harmonic scalar law,
> the first causal-birth holonomy pair, and the corrected six-outcome process
> all satisfy this double-conservation criterion. This establishes a precise
> candidate microscopic conservation law, conditional on demanding both forms
> of local information preservation; causal order still has to select the
> operators and explain why nature imposes both demands.
> `KFCausalRecordedRefinementDilation.lean` resolves the next structural layer.
> The birth operators stack canonically into a finite recorded dilation
> `V : H -> H x Outcome`. The theorem `V^dagger V=I` iff
> `sum K_e^dagger K_e=I` makes Born completeness exactly reversible record
> creation on the image. A canonical coherent record codiagonal `E` obeys
> `E V=sum K_e`, so `E V=I` iff coherent exhaustivity. Their conjunction is
> therefore equivalent to double conservation, and supplies two exact recovery
> maps for every incoming carrier amplitude. Exact one-dimensional binary
> witnesses prove that isometry does not imply counital recovery and counital
> recovery does not imply isometry. The existing rank-one and six-outcome
> causal-holonomy laws instantiate both without new fitted coefficients. This
> is initially an abstract finite outcome-indexed record architecture.
> `KFCausalNativeSuccessorRecord.lean` removes that particular abstraction at
> one-step causal-growth scope. At every parent the record labels are exactly
> the nonempty subtype of genuine unlabeled one-element children in
> `physicalCausalSuccessors`; no `Fin k` enumeration is supplied. Forgetting
> the child is the unique map to the terminal one-point type, retaining the
> parent coordinate gives the unique record projection, and its unit-weight
> complex linearization gives the unique native codiagonal. The corresponding
> dilation is isometric and counital exactly under double conservation, with
> exact recovery maps for arbitrary incoming carrier amplitudes. Restricting
> the canonical harmonic causal law to the native physical-successor subtype
> preserves both coherent and Born normalization and realizes the construction
> at every rank. Causal order has therefore supplied the finite record carrier
> and recombination map.
> `KFCausalNativeSuccessorInstrument.lean` closes the finite channel question
> and corrects the meaning of “forgetting.” Any Born-complete operator family
> on the intrinsic physical-child subtype canonically defines a
> `KrausRepresentation` after an internal `Fintype.equivFin` reindexing; its
> induced map is proved equal to the enumeration-free native sum and is CPTP.
> Tracing the native record out of the recorded Stinespring state recovers that
> channel exactly and preserves trace, Hermiticity, and positivity. By contrast,
> whenever two distinct records exist, the coherent codiagonal fails the
> single-Kraus completeness equation, so it cannot be a trace-preserving record
> erasure. It remains the amplitude-level map implementing exhaustive cylinder
> recombination. The canonical harmonic child operators give an all-rank CPTP
> native instrument, but their reduced rank-one channel is exactly the identity
> for every parent, rank, and chirality. The exact child Born weights survive in
> the resolved operations; no causal or chiral discriminator survives record
> erasure. Thus a finite native instrument now exists without external labels,
> while nontrivial reduced dynamics still requires a higher-rank operator law;
> uniqueness of that law and a laboratory interpretation are not derived.
> `KFCausalNativeResolutionLaw.lean` closes the smallest sharp higher-rank
> ansatz and names the resulting candidate microscopic law. At each causal
> parent, the carrier basis is the finite set of genuine unlabeled children.
> Requiring only the sharp native Born effects `K_c^dagger K_c=|c><c|`
> first derives exclusive response by positivity and already implies aggregate
> Born completeness. Together with universal coherent conservation this
> uniquely forces `K_c = |c><c|`. Thus matrix-support locality and
> nondemolition are derived rather than assumed. Independently, record
> sufficiency plus nondemolition uniquely forces the same channel without
> assuming linearity, positivity, or a Kraus representation.
> The induced native causal resolution channel is CPTP, preserves every
> diagonal successor weight, erases every cross-successor coherence, is
> idempotent, and commutes with every relabeling. Two distinct physical
> children provide an exact witness that it is not the identity. This derives
> a nontrivial all-rank local operator law without a transition coefficient.
> The scope is deliberately narrower than a discovered law of nature:
> the sharp native Born effect is the new microscopic principle, and identifying
> the native record carrier with a protected laboratory record remains open. If
> chirality is stored as off-diagonal coherence in this same carrier, the law
> erases it; protection therefore requires a separate/diagonal chiral record
> or a derived embedding into the full observable algebra.
> `KFCausalNativeRecordDynamics.lean` moves the probability postulate one
> layer deeper. Let `V` be the recorded refinement, `P_c` the incoming native
> child projector, and `Q_c` the corresponding projector on the created
> record. Losslessness `V^dagger V=I` plus causal identity transport
> `Q_c V=V P_c` derives `K_c^dagger K_c=P_c`; adding coherent recovery
> `E V=I` uniquely forces `K_c=P_c`. The resulting dynamics is repeatable and
> gives the exact quantum outcome rule
> `Pr(c|rho)=Re Tr(rho K_c^dagger K_c)=Re rho[c,c]`; prepared native children
> therefore resolve deterministically. Its fixed points are exactly the
> record-diagonal algebra. A fully explicit
> Pauli-Y rotated binary instrument obeys Born completeness, coherent
> conservation, and relabeling covariance but is not native-sharp, proving
> that the transport/alignment law is independent of all three. Native
> resolution also merges the two same-carrier orientation projectors, so a
> physical chirality sector must be separately protected or compatibly
> embedded. The remaining bridge is therefore singular and precise: derive
> the record-identity intertwiner in the laboratory-relevant observable
> algebra.
> `KFCausalCylinderRecordTransport.lean` derives that intertwiner from actual
> sequential growth for every realized finite cylinder. The canonical map
> sends `|h>` only to amplitude-weighted children `|h,b>`, so prefix retention
> forces `Q_c V=V P_c` independently of phases and normalization. With local
> Born normalization the same map is an isometry and the refined record pulls
> back sharply: `V^dagger Q_c V=P_c`. Matching singleton histories have weight
> one and distinct histories weight zero; the canonical harmonic causal law
> realizes the construction at every rank. This closes native alignment for
> facts after they occur. It does not install mutually exclusive future-child
> projectors before a birth, identify the cylinder algebra with a laboratory
> record, or protect same-carrier chirality.
> `KFCausalBundleProtectedChirality.lean` proves the finite direct-sum escape.
> Adding the intrinsic rank-two sheet fiber to each history block preserves
> the sequential-growth cylinder equation at every rank. The ordinary
> full-`S_3` commutant is scalar, but the sign-twisted commutant is exactly one
> dimensional: every operator reversing under both adjacent transpositions is
> proportional to `J=[[1,-2],[2,-1]]`. The observable `iJ` is Hermitian for the
> intrinsic Gram metric and squares to `3I`. When the causal orientation `Xi`
> flips on each odd transport, `Xi iJ` intertwines exactly with bundle growth.
> History-block pinching is idempotent and trace-preserving and fixes this
> internal observable, so causal records and relational chirality are
> mathematically compatible without assuming a global tensor-product
> factorization. The cylinder support law is derived from growth; assigning
> the two odd holonomies to actual physical causal/CSpec edges, deriving the
> orientation flip there, and promoting the pinching to a physical CPTP
> laboratory instrument remain explicit bridges. No Standard-Model or
> continuum chirality claim follows from this finite theorem.
> `KFCausalCSpecDeterminantChirality.lean` closes the finite microscopic edge
> law that the abstract bundle theorem left conditional. The orientation
> `Xi` is the determinant/sign representation of the same continuation-
> recovered three-sheet CSpec permutation that transports the rank-two
> carrier; it is therefore generated recursively rather than supplied as an
> independent field. Every history has `Xi^2=1`, the first witnessed unfilled
> loop computes `Xi=-1`, and the paired representations derive the exact
> relational-chirality intertwiner at every rank. The history-fiber
> projectors form a complete Kraus family, so record pinching is a genuine
> finite CPTP channel: it erases exactly cross-history coherences and fixes
> all within-history observables, including the derived chirality block. The
> result applies to the constructed finite global CSpec atlas. It does not
> prove that arbitrary physical causal-set growth generates that atlas,
> promote trace preservation to event-level `D(Omega,Omega)` preservation,
> or identify the finite chirality observable with a continuum weak current.
> `KFCausalDeterminantPhysicalBoundary.lean` resolves the first two caveats,
> but not by promoting the universal claim. The first physical child of the
> empty causet is a singleton; its actual causal order has no Hasse cover edge,
> so its intrinsic diamond-direction quotient is empty. Therefore physical
> sequential growth is **not** three-sheeted at every stage, and determinant
> chirality is necessarily a law of a regular three-direction locus rather
> than a universal fiber over all causets. The same audit proves the exact
> normalization criterion for the finite CPTP history-block channel:
> `D(Omega,Omega)` is preserved iff the sum of erased cross-history entries is
> zero. Exact block decoherence is sufficient. The existing two-antichain
> theorem shows why the condition is substantive: no trace-preserving
> record-diagonalizing channel can preserve its total-event normalization.
> `KFCausalRegularPhaseEntry.lean` then proves physical onset rather than
> postulating it. The eight Boolean cells are enumerated by three-bit masks;
> every prefix inclusion is a genuine maximal-element birth, and the rank-eight
> endpoint is order-isomorphic to the Boolean tangent cube. Cardinality proves
> that eight is the unique exact-cube rank. A ninth birth cannot leave the
> *whole* causet equal to the cube, but every legal birth preserves the cube as
> an embedded suborder because sequential growth never changes old relations.
> Thus the regular structure has a proved onset and an all-future protected
> causal memory, without claiming that every later event is locally regular.
> `KFCausalDeterminantWeakCurrent.lean` closes the finite algebraic current
> identification. Since the derived complex determinant orientation squares
> to one, it is exactly `+1` or `-1`; its real part is therefore a nonzero weak
> projector sign. Every CSpec atlas history gives either the standard
> nontrivial purely left charged-current vertex or its nontrivial right mirror.
> The trivial/even sector is left in the fixed convention and the witnessed odd
> loop is the right mirror. No independent `Xi` input remains in this finite
> map. `KFCausalCSpecPhysicalGrowthRealization.lean` proves a stronger and more
> honest finite bridge than identifying the earlier eight-event path by fiat:
> every finite causal order has a linear extension whose initial segments are
> legal maximal-element births. The native 140-event global CSpec atlas is
> therefore the endpoint of an actual physical unlabeled growth history, that
> history has nonzero uniform-law amplitude, and the endpoint contains a native
> Boolean-cube seed while retaining the witnessed full-`S_3` determinant
> sector. This is an existence/support theorem. It does not show that the
> rank-eight path alone determines the atlas, nor that the uniform or harmonic
> dynamics preferentially selects this endpoint.
> `KFCausalCSpecPhysicalChiralGrowthRealization.lean` now isolates the complete
> chiral upgrade: if the 140 atlas-birth raw coherent aggregates are nonzero,
> then the same physical atlas path has nonzero complete-chiral path amplitude
> and realizes the determinant weak sector. Lean also proves each atlas birth is
> already physical, nonphysical births are killed by the complete chiral support
> gate, and the normalized-transition nonzero gate is equivalent to the raw
> numerator gate because the complete-chiral parent partitions are zero-free.
> The next obstruction is now reduced to a finite integer-polynomial
> certificate: `CompleteChiralAtlasRealAggregatePolynomialNonzero` implies the
> raw aggregate gate, so proving 140 concrete real-part aggregate polynomials
> nonzero closes this branch. Lean now sharpens that again through
> `CompleteChiralAtlasRealAggregateCoeffNonzero`: it is enough to exhibit one
> nonzero signed real coefficient in each of the 140 polynomials, unless one
> aggregate is purely imaginary and needs the analogous imaginary-part
> certificate. The newest signed-fiber theorem expands those coefficients as
> explicit signed sums over the labeled transition fibers, turning the finite
> gate into a direct signed-count noncancellation target.
> `KFCausalCSpecContinuumChiralityQualification.lean` isolates the remaining
> continuum assumptions. The finite weak vertex has an exact pointwise lift to
> a nontrivial chiral field on any nonempty base, and every order embedding
> transports order reversal. In 3+1 dimensions the existing continuum term
> flips under time reversal only when its integral is supplied as
> orientation-odd. An explicit constant functional is orientation-even, so
> orientation oddness is not derivable from an arbitrary continuum functional.
> A Lorentzian spin bundle, Dirac equation and action, continuum convergence,
> weak-coupling normalization, and absolute vacuum-sector selection remain
> open.
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

1,019 Lean files in `UnifiedTheory/`, **zero sorry and zero custom axioms** in
core mathematical content. Latest full root build: 8,770 jobs successful
(August 2026).
Foundational axioms only: `propext`, `Classical.choice`, `Quot.sound`.
