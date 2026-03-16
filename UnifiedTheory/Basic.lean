/-
  UnifiedTheory — Derived Geometric Unification
  ==============================================

  Trusted base: {propext, Classical.choice, Quot.sound} only.
  Zero custom axioms. Zero sorrys. Entire codebase machine-checked.

  ═══════════════════════════════════════════════════════
  CAPSTONE: complete_metric_connection (Capstone.lean)
  ═══════════════════════════════════════════════════════

  From two geometric primitives (LorentzianMetric + StructureConstants):

  GRAVITY (exact):
    (G1) div(G) = 0 — Bianchi identity from ∂ commutativity
    (G2) Null cone determines conformal class

  GAUGE (exact):
    (C1) Curvature F = dA + [A,A] is antisymmetric
    (C2) Abelian limit recovers Maxwell
    (C3) Gauge stress-energy traceless in d=4 (UNIQUELY)

  MATTER (exact):
    (M1) Charge additivity: Q(h₁+h₂) = Q(h₁)+Q(h₂)
    (M2) Annihilation: Q(h+(-h)) = 0

  QUANTUM (exact):
    (Q1) Born rule: obs(z) = |z|² = Q²+P²
    (Q2) Decoherence: phase averaging kills interference

  ═══════════════════════════════════════════════════════
  DERIVED CHAIN (DerivedUnification.lean, MetricDefects.lean)
  ═══════════════════════════════════════════════════════

  fully_derived_unification: LorentzianMetric m → 4 branches, zero parameters
  metric_to_everything: full chain metric → charge → quantum → classical
  fully_exact_chain: entire chain is exact (ExactRegime.lean)

  ═══════════════════════════════════════════════════════
  GAUGE TRACE THEOREM (MetricGaugeCoupling.lean)
  ═══════════════════════════════════════════════════════

  gauge_traceless_4d: tr(T_gauge) = (1-d/4)|F|² = 0 in d=4
  four_is_unique_traceless: d=4 is the unique dimension for this
  traceless_but_sourceful: |F|²>0 but tr(T)=0 — traceless ≠ inert

  K/P split interpretation:
    K = trace-visible scalar/source channel
    P = trace-free channel containing gauge stress-energy
    z = Q+iP packages trace-visible and trace-free components

  ═══════════════════════════════════════════════════════
  AUDIT CLASSIFICATION
  ═══════════════════════════════════════════════════════

  EXACT (theorem, no approximation):
    - All algebraic structure (K/P, bridge, neutrality, charge algebra)
    - Bianchi identity (unconditional identity, not a field equation)
    - Null cone determination
    - Curvature antisymmetry and linearity
    - Gauge trace formula tr(T) = (1-d/4)|F|²
    - Born rule, interference, decoherence (ℂ/ℝ² arithmetic)

  STRUCTURAL (correct formalization of standard mathematics):
    - Scaling exponent from dimension (rpow/log algebra)
    - Rank-1 projection from nonzero functional
    - Killing form symmetry (Tr(AB) = Tr(BA))
    - Cauchy functional equation

  DEFINITIONAL (modeling choices, explicitly stated):
    - z = Q + iP (identification of K/P pair with ℂ)
    - Perturbation space = Matrix (not symmetric-only)

  OUTSIDE SCOPE (not formalized):
    - Field equation G = 0 as a condition (we prove div(G) = 0, an identity)
    - Which perturbations are "physical" solutions
    - Dynamics / propagation / field evolution
    - Lovelock uniqueness (that G+Λg is the ONLY divergence-free tensor)
    - Full manifold differential geometry (we work in normal coordinates)
    - Specific gauge group selection (g_dim is a free parameter)

  ═══════════════════════════════════════════════════════
  LEGACY INVENTORY (original files below)
  ═══════════════════════════════════════════════════════

  ═══════════════════════════════════════════════════════
  PRIMITIVE REDUCTION: 5 → 3 → 2 → 1 (ALL PROVEN)
  ═══════════════════════════════════════════════════════

  Original 5 primitives → 1 structured primitive (Lorentzian metric).
  Eliminated: scaling (from dimension), null vanishing (from gravity chain),
  source functional (from linear operator), dressing nontriviality (from dim≥2).

  ═══════════════════════════════════════════════════════
  CAUSAL FOUNDATION (ALL PROVEN)
  ═══════════════════════════════════════════════════════

  CausalFoundation.lean
    CausalSet structure, dimension fractions
    metric_from_conformal_and_volume

  CausalBridge.lean
    link_tau_vanishes                link proper time → 0 as ρ → ∞
    null_cone_from_dense_links       bounded-dt links have nullity → 0
    null_zero_volume                 null separation → zero Alexandrov volume
    null_implies_link                zero volume → zero events → link
    near_null_small_volume           near-null → small volume
    null_link_equivalence            null ↔ link (forward + backward)
    poisson_uniqueness               additive + positive → linear (Cauchy)
    null_cone_recovery_unconditional unconditional null cone determination

  VolumeFromCounting.lean
    volume_ratio_parameter_free      Vol(R1)/Vol(R2) = N(R1)/N(R2)
    calibration_determines_all       one reference fixes all volumes
    counting_volume_unique           counting volume is unique
    proper_time_roundtrip            tau recoverable from counting
    volume_from_counting             summary theorem

  DiscreteMalament.lean
    conformal_from_null_cone_1plus1  same null cone → b=0, c=-a
    conformal_factor_exists          g2 = lambda * eta
    malament_uniqueness              two metrics, same null cone → conformal
    dense_links_trace_null_cone      causal links approximate null directions
    discrete_malament_1plus1         causal order → conformal metric
    stage3_closed_1plus1             algebraic Malament theorem

  NullConeGeneral.lean
    null_cone_general                null-cone theorem (general n+1 dim)
    offdiag_vanish                   off-diagonal vanishing (Pythagorean trick)

  SparseSum.lean
    double_sum_two_support_sym       2-support sparse sum reduction
    double_sum_three_support_sym     3-support sparse sum reduction

  ═══════════════════════════════════════════════════════
  LAYER A: ALGEBRAIC BACKBONE (ALL PROVEN)
  ═══════════════════════════════════════════════════════

  RenormRigidity.lean
    renormOp_powerLaw                R_l(B_a) = l^(a-2) * B_a
    renorm_fixedPoint_iff            R_l(B_a) = B_a iff a = 2

  PrimitiveReduction.lean
    renorm_fixedPoint_d              alpha = d-1 in d spatial dimensions
    fixedPoint_3plus1                alpha = 2 in 3+1
    fixedPoint_2plus1                alpha = 1 in 2+1
    fixedPoint_1plus1                alpha = 0 in 1+1
    vacuum_implies_null_vanishing    Einstein vacuum → null vanishing

  NullConeTensor.lean
    null_cone_coeffs                 null-vanishing → b=0, c=-a
    null_determines_up_to_trace      exists c0, S = c0 * eta

  BFSourceDressing.lean
    SourceDressingDecomp.decompose   v = piK(v) + piP(v)

  DerivedBFSplit.lean
    sourceProj_idem                  piK is idempotent
    source_vanishes_on_dressing      phi(piP(v)) = 0
    source_on_K                      phi(piK(v)) = phi(v)
    decompFromFunctional             K/P split from source functional

  BianchiIdentity.lean
    once_contracted                  first contraction of Bianchi
    contracted_bianchi               2 * div(Ric) = dScalar
    einstein_div_free                div(G) = 0

  MetricToRiemann.lean
    R_antisym1, R_antisym2           Riemann symmetries from metric
    dR_antisym1, dR_antisym2         dR symmetries from metric
    bianchi2                         second Bianchi from metric
    riemannFromMetric                all RiemannData fields proven

  LovelockEinstein.lean
    lovelock_bianchi_constraint      div-free → d = -c/2
    lovelock_decomposition           c*R + (-c/2)*S*g + e*g = c*G + e*g
    lovelock_endpoint                exists a b, E = a*G + b*g

  SourceFromMetric.lean
    sourceFromOperator               phi = psi composed L
    source_vanishes_on_kernel        ker(L) in ker(phi)
    gauge_is_dressing                gauge modes have zero source
    decompositionFromOperator        full K/P from linear operator
    reduction_3_to_2                 source functional from operator

  SinglePrimitive.lean
    kernel_nontrivial                dim >= 2 → nonzero functional has nontrivial kernel
    dressing_guaranteed              K/P split always has nontrivial dressing
    reduction_2_to_1                 one primitive suffices

  ═══════════════════════════════════════════════════════
  LAYER B: MATTER + QUANTUM (ALL PROVEN)
  ═══════════════════════════════════════════════════════

  ParentU.lean                       Parent structure definition
  UnifiedBranch.lean                 ParentU → Einstein branch
  DefectSector.lean                  Defect data structures
  DefectBridge.lean                  Source-focusing bridge M1-M4
  MatterBranch.lean                  Einstein + matter assembly
  DefectEquivalence.lean             Defect classification + dichotomy
  LinearDefects.lean                 Charge algebra from linearity
  DefectComposition.lean             Charge, conjugation, annihilation
  ChargeSectors.lean                 Sector decomposition + bound states
  MultiParticle.lean                 N-body conservation
  FarField.lean                      Far-field reduction + screening
  StructuralTheorems.lean            Enclosure, interaction signs, uniqueness
  QuantumDefects.lean                Interference, Born rule, phase invariance
  ComplexFromDressing.lean           z = Q+iP from K/P split
  ComplexUniqueness.lean             Born rule is unique SO(2)-invariant
  Decoherence.lean                   Phase averaging → classical

  ═══════════════════════════════════════════════════════
  LAYER C: CONCRETE REALIZATIONS (PROVEN/VERIFIED)
  ═══════════════════════════════════════════════════════

  ConcreteModel.lean                 Lean-certified U_star
  ConcreteMultiBody.lean             Many-body instance

  ═══════════════════════════════════════════════════════
  COMPLETE CHAIN
  ═══════════════════════════════════════════════════════

  Causal set → dimension → null cone → conformal metric
    + counting → volume → full metric
    → Riemann → Bianchi → Einstein + Lambda
    → source functional → K/P split → dressing nontrivial
    → complex amplitudes → Born rule → interference → decoherence
    → charge algebra → annihilation → bound states → far-field
    → everything

  Every link: machine-checked, propext/choice/quot.sound only.
  Zero custom axioms. Zero sorrys.
  Causal foundation complete: null cone general (n+1), causal bridge (Poisson + rpow).
-/
