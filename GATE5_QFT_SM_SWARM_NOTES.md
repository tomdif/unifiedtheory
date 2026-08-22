# Gate 5 QFT/SM Swarm Notes

Agent: Gate5-QFTSM

Scope: QFT and Standard Model infrared limit. This note is analysis only. No
Lean build was run, no `.lake` state was modified, and nothing was committed or
pushed.

## Strongest Existing Results

### Recovered finite geometry

File: `UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean`

The strongest geometry object is
`PhysicalHauptvermutungRecoveredStage`. It packages:

- `total = 0`;
- every local physical Hauptvermutung distortion is zero;
- `cSpecBridgeTotalDistortion scale edge candidate = 0`;
- every bridge incidence recovers the candidate transport.

The important consequences are:

- `PhysicalHauptvermutungRecoveredStage.candidate_eq_canonical`;
- `PhysicalHauptvermutungRecoveredStage.candidate_transport`;
- `physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage`;
- `physicalHauptvermutungExactRecoveryCertificate_exists_recovered_after`;
- `physicalHauptvermutungExactRecoveryCertificate_exists_observable_zero_after`.

Interpretation: once the exact-recovery certificate is supplied, the repo has a
finite stage at which the local CSpec transport is canonical and all tracked
finite geometry defects vanish.

### Finite Hilbert and Born rule

Files:

- `UnifiedTheory/LayerC/SMHilbertInstantiation.lean`
- `UnifiedTheory/LayerC/SMTensorDecomposition.lean`
- `UnifiedTheory/LayerC/SMBornRuleGeneralN.lean`
- `UnifiedTheory/LayerC/SMQMBridgeCapstone.lean`

Unconditional pieces:

- `singleGenDim = 16`;
- `singleGenDim = dim_spinor_SO10`;
- `singleGenDim = 2 ^ 4`;
- `Fin singleGenDim` has a four-qubit index equivalence;
- SU(5)/SM sector cardinalities add to `16`;
- `SubstrateState n` maps to a density matrix;
- `born_rule_general_n` proves per-outcome Born weights;
- `born_rule_general_n_normalized` proves probabilities sum to one;
- `SMQM_bridge_master_2026` bundles the atomic Hilbert/QM bridge.

Boundary: the SU(5)/SO(10) matter labels are dimensional/index-level. Full
representation theory and physical matter identification are not derived here.

### Finite gauge algebra

Files:

- `UnifiedTheory/LayerC/SMGaugeFiniteRep.lean`
- `UnifiedTheory/LayerC/SMGaugeDynamics.lean`

Unconditional pieces:

- explicit `Z2` weak phase-flip unitary rep on `C^2`;
- explicit `Z3` color cyclic unitary rep on `C^3`;
- covariant subalgebras and trace invariance;
- gauge-invariant observables form a unital star-subalgebra;
- Higgs/electroweak breaking counts are proved at the arithmetic level;
- `Q = T3 + Y` is formalized and checked on SM charge examples.

Boundary: continuous SU(2), SU(3), Yang-Mills dynamics, the full Lagrangian,
and the Higgs mechanism as field dynamics are named targets, not proved.

### Finite quantum measure and chirality

Files:

- `UnifiedTheory/Audit/KFCausalQuantumMeasure.lean`
- `UnifiedTheory/Audit/KFOrientationPathQuantum.lean`
- `UnifiedTheory/Audit/KFHopfSpinorBlochBridge.lean`
- `UnifiedTheory/Audit/KFHopfPhaseQuotient.lean`
- `UnifiedTheory/Audit/KFHopfUnitSphereQuotient.lean`
- `UnifiedTheory/Audit/KFHopfFiberExactness.lean`
- `UnifiedTheory/Audit/KFHopfSurjectivity.lean`
- `UnifiedTheory/Audit/KFHopfQuotientInverse.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfFiber.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfQuotientFiber.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornObservable.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornAxisObservable.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornTomography.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornSeparation.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornPhaseClassSeparation.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfBornPhaseClassReconstruction.lean`
- `UnifiedTheory/Audit/KFHopfProjectiveQubitState.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfProjectiveQubitState.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfProjectiveQubitCarrier.lean`
- `UnifiedTheory/Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierField.lean`
- `UnifiedTheory/Audit/KFCausalBundleProtectedChirality.lean`
- `UnifiedTheory/Audit/KFCausalCSpecDeterminantChirality.lean`
- `UnifiedTheory/Audit/KFCausalSetSourceQuantumEnsemble.lean`

Unconditional pieces:

- Born-from-growth amplitude and decoherence functional;
- hermiticity, strong positivity, Sorkin level-2 sum rule;
- diagonal classical measure plus interference decomposition;
- algebraic Hopf bridge from normalized two-component spinors to unit Bloch
  vectors, with common unit-phase invariance and direct agreement with
  `WignerHardQubit.blochVector`;
- algebraic common-phase quotient: unit-phase related spinors form a setoid,
  spinor norm is preserved, and Bloch coordinates descend to quotient classes;
- normalized unit-sphere quotient: normalized phase classes carry a
  well-defined unit Bloch-sphere observable;
- Hopf fiber exactness: equal unit Bloch observables are exactly
  common-`U(1)` phase related normalized spinors, so the algebraic quotient map
  has no extra identifications;
- Hopf surjectivity: every unit Bloch point has a normalized spinor
  representative, so the normalized algebraic phase quotient is bijective;
- Hopf quotient inverse: unit Bloch coordinates determine a chosen normalized
  phase class with both inverse laws proved;
- local recovered-stage Hopf fiber interface: normalized stage/site spinors
  have unit Bloch observables and local `U(1)` phase choices are invisible to
  the repo Bloch vector;
- recovered-stage projective Hopf fiber interface: local fields determine
  normalized phase classes and gauge-invariant unit Bloch-sphere quotient
  observables;
- recovered-stage local Pauli Born interface: quotient Bloch observables
  determine valid X/Y/Z plus-minus probability pairs, invariant under local
  `U(1)` gauge rotation;
- arbitrary-axis local Born interface: every unit Bloch measurement axis gives
  a valid gauge-invariant plus-minus probability pair, with coordinate axes
  reducing to the Pauli-X/Y/Z cases;
- local Born tomography: Pauli Born expectations reconstruct the local quotient
  Bloch observable and arbitrary-axis expectations are dot products;
- local Born observational completeness: Pauli Born data, all-axis Born data,
  and the recovered quotient Bloch observable are equivalent local data;
- projective local Born completeness: the same Born data separates the
  recovered normalized Hopf phase class itself;
- projective local Born tomography: Pauli Born expectations reconstruct the
  recovered normalized phase class, invariant under local `U(1)` rotation;
- finite projective-qubit state API: normalized Hopf phase classes have
  Bloch/Born observables, Pauli Born expectations reconstruct the state, and
  Pauli/all-axis Born data are equivalent to state equality;
- recovered-stage projective-qubit state bridge: every local stage/site phase
  class is identified with the state API, with matching local Bloch/Born data,
  projective-state reconstruction, gauge invariance, and Born-data separation;
- recovered-stage projective-qubit carrier: local state, Bloch point, and Born
  family are bundled as one carrier with reconstruction, gauge invariance, and
  carrier equality separated by Pauli/all-axis Born data;
- recovered-stage projective-qubit carrier field: a whole stage is one carrier
  per site, with pointwise Pauli/all-axis Born data equivalent to field equality
  and local `U(1)` gauge invariance across the stage;
- exact finite spin-half/path Pauli algebra and unitary holonomy evolution;
- protected finite relational chirality under record pinching;
- determinant-line CSpec chirality transport;
- harmonic source ensemble with explicit quantum interference.

Boundary: infinite cylinder extension, continuum field observables, physical
phase selection, and derivation of amplitudes from the full microscopic
dynamics remain open or separately named.

### Multi-link Hilbert space

File: `UnifiedTheory/LayerB/Phase_A1_MultiLinkHilbert.lean`

Unconditional pieces:

- `multiLinkConfig L = Fin L -> G_SO10`;
- product Haar measure `multiLinkHaar L`;
- `linkHilbert L = Lp R 2 (multiLinkHaar L)`;
- single-link to multi-link linear isometries;
- lifted six axes remain orthogonal.

Boundary: Wilson Hamiltonian, spectral properties, continuum gauge fields, and
QFT dynamics are not constructed there.

## Existing Physical Identification Assumptions

The main assumptions/gaps are not hidden:

- `PhysicalHauptvermutungExactRecoveryCertificate` must still be produced from
  the actual causal-growth law.
- `FullContinuumQGBridge.infraredGRAndQFTRecovered` is a named field, not a
  theorem.
- `HorizonAQFTModel` targets package analytic AQFT/horizon assumptions.
- `SM_Lagrangian_Target` and `Higgs_Mechanism_Dynamical_Target` are named
  targets.
- `SO10Forcing_Target` in `SMPartialForcing.lean` is a named forcing target.
- `SMTensorDecomposition.lean` proves dimension/index identities, not full Lie
  representation theory.
- `SMBornRuleGeneralN.lean` is currently a real-amplitude bridge; the complex
  phase channel is not the full finite causal-growth phase dynamics.

## Missing Bridge

The missing Gate 5 bridge is:

```text
exact recovered CSpec stage
  -> finite local Hilbert fiber over each recovered site/chart/edge
  -> local observable algebra/net
  -> states from causal quantum measure or substrate amplitudes
  -> gauge/chirality action on the fibers
  -> scaling family of local algebras
  -> continuum AQFT/Dirac/Yang-Mills/SM limit
```

The repo already has the left side and several right-side finite algebra
pieces. What is absent is a formal interface saying that a recovered finite
geometry carries the finite Hilbert fibers on which the SM/QM algebra acts.

## Concrete Path

1. Add a finite interface from recovered CSpec stages to Hilbert fibers.
   This should be finite and unconditional: no continuum claims.

2. Prove local Born normalization on every recovered fiber using
   `SMBornRuleGeneralN.sm_born_rule_general_n_bridge`.

3. Add local finite observable algebras:
   `i : site -> Matrix (Fin singleGenDim) (Fin singleGenDim) C`.
   First theorem: pointwise star-subalgebra closure.

4. Attach finite gauge actions locally:
   use `z2PhaseFlipRep_isUnitaryRep` and `z3CyclicRep_isUnitaryRep` on the
   corresponding qubit/qutrit factors. Do not claim continuous gauge fields.

5. Add transport compatibility:
   use `PhysicalHauptvermutungRecoveredStage.candidate_transport` to prove the
   recovered incidence transport is canonical before transporting local fiber
   labels.

6. Add a finite net interface:
   define local regions as `Finset site`, local algebras as finite products or
   matrix tensor placeholders, prove isotony first.

7. Only after the finite net exists, add a scaling family and name the analytic
   continuum target: Wightman/Hadamard or AQFT local net, Dirac operator,
   Yang-Mills connection, renormalization.

## Smallest Next Formal Target

Proposed file:

`UnifiedTheory/Audit/KFCausalCSpecQFTSMInterface.lean`

Smallest useful structure:

```lean
structure RecoveredCSpecHilbertFiber
    {site : Type*} [Fintype site]
    {countWindow curvatureBias spectralLocality : site -> R}
    {scale total : R}
    {edge : site -> E4}
    {candidate : site -> Equiv.Perm Direction} where
  recovered :
    PhysicalHauptvermutungRecoveredStage
      countWindow curvatureBias spectralLocality scale total edge candidate
  localState :
    site -> SMBornRuleGeneralN.SubstrateState
      SMHilbertInstantiation.singleGenDim
```

Smallest useful theorem:

```lean
theorem RecoveredCSpecHilbertFiber.transport_and_born
    (F : RecoveredCSpecHilbertFiber ...) :
    (forall i, candidate i = fourState.perm (edge i))
      and
    (forall i k,
      Re Tr(rho_i * |k><k|) = (F.localState i).amp k ^ 2)
      and
    (forall i,
      sum_k Re Tr(rho_i * |k><k|) = 1)
```

Why this is the right smallest step:

- It consumes the new exact-recovery object instead of bypassing it.
- It consumes the existing finite Hilbert/Born bridge instead of restating it.
- It creates the missing formal object: a recovered finite geometry carrying
  local quantum fibers.
- It does not overclaim continuum QFT or the full Standard Model.
- It gives the next agents a concrete place to attach finite local algebras,
  gauge reps, chirality projectors, and later AQFT scaling targets.
