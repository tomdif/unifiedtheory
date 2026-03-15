/-
  UnifiedTheory — Causal Unified Theory Formalization
  ====================================================

  UNIFIED EINSTEIN + MATTER BRANCH: FULLY PROVEN
  Trusted base: {propext, Classical.choice, Quot.sound} only.
  No sorry. No custom axioms. No opaque types.
  Verified 2026-03-15.

  ═══════════════════════════════════════════════════════
  COMPLETE THEOREM INVENTORY
  ═══════════════════════════════════════════════════════

  LAYER A — Algebraic Backbone (ALL PROVEN)
  ──────────────────────────────────────────

  RenormRigidity.lean
    renormOp_powerLaw             R_l(B_a) = l^(a-2) * B_a
    renorm_fixedPoint_iff         R_l(B_a) = B_a  <=>  a = 2

  NullConeTensor.lean
    null_cone_coeffs              null-vanishing => b=0, c=-a
    null_cone_quad_1plus1         quadratic form proportional to eta
    null_cone_bilin_1plus1        bilinear form proportional to eta
    null_determines_up_to_trace   exists c0, S = c0 * eta

  BFSourceDressing.lean
    SourceDressingDecomp.decompose    v = piK(v) + piP(v)

  LovelockEinstein.lean
    lovelock_bianchi_constraint   div-free => d = -c/2
    lovelock_decomposition        c*R + (-c/2)*S*g + e*g = c*G + e*g
    lovelock_endpoint             exists a b, E = a*G + b*g

  ConditionalEinstein.lean
    conditional_einstein_branch   all four => a=2, S~eta, K/P, a*G+b*g

  LAYER B — Parent Object + Matter Sector (ALL PROVEN)
  ────────────────────────────────────────────────────

  ParentU.lean
    ScaleBlock, NullBlock, BFBlock, EndptBlock, ParentU

  UnifiedBranch.lean
    bridge_rg, bridge_null, bridge_bf, bridge_einstein
    unified_branch                ParentU => Einstein branch

  DefectSector.lean
    BFDefectData, NullDefectData, DefectBlock, MatterParentU

  DefectBridge.lean
    defect_source_bridge          K_d source = bias_d focusing
    defect_dressing_neutral       P_d carries zero source
    defect_full_characterization  both properties combined

  MatterBranch.lean
    matter_einstein_branch        MatterParentU + defect => Einstein + matter

  DefectEquivalence.lean
    DefectInvariants, DefectEquiv (equivalence relation)
    inert_has_zero_bias           inert => zero focusing
    source_carrying_has_bias      source => nonzero focusing
    purely_topological_is_inert   pure dressing => inert
    defect_dichotomy              every stable defect: inert or source

  DefectComposition.lean
    charge (= source strength)
    charge_additive               Q(d1+d2) = Q(d1) + Q(d2)
    charge_conjugate              Q(d_bar) = -Q(d)
    charge_determines_sector      Q=0 <=> inert
    annihilation_charge           Q(d + d_bar) = 0
    annihilation_is_inert         d + d_bar is inert
    neutral_compose               neutral sector closed

  ChargeSectors.lean
    InSector, sector_compose      D_q + D_q' in D_{q+q'}
    sector_conjugate              D_q -> D_{-q}
    BoundState, bound_state_inert neutral composites are inert
    conjugate_bound_state         d + d_bar always binds
    charge_sector_structure       all five sector properties

  MultiParticle.lean
    charge_foldl                  N-body charge = sum of charges
    opposite_charge_partial_cancel  partial cancellation
    opposite_charge_full_cancel   equal-opposite => zero
    like_charge_no_cancellation   same-sign no cancellation
    balanced_compose_neutral      balanced list => neutral
    multi_particle_structure      all five many-body properties

  FarField.lean
    FarFieldEquiv (equivalence by charge)
    net_charge_determines_far_field   same net Q => same far field
    neutral_far_field_invisible       Q=0 => invisible
    far_field_screening               neutral screen is exact
    far_field_conjugate_screen        d+d_bar screen is exact
    far_field_theorem                 complete far-field theorem

  LAYER C — Concrete Realizations (ALL PROVEN/VERIFIED)
  ────────────────────────────────────────────────────

  ConcreteModel.lean (Lean, proven)
    U_star                        explicit MatterParentU
    concrete_realization          both defect sectors populated

  ConcreteMultiBody.lean (Lean, proven)
    concreteComposable            explicit ComposableDefectBlock
    concrete_many_body            e+e- annihilation, 3-body, screening

  ModelB/ (Python, verified)
    causal_2complex.py            1+1 causal diamond, certificate
    robustness.py                 388/388 pass, 0 failures, 1+1 and 2+1
    physics_observables.py        inverse-square, composition, charge

  ═══════════════════════════════════════════════════════
  DEPENDENCY GRAPH
  ═══════════════════════════════════════════════════════

    MatterParentU
      |
      +-- ParentU --+-- ScaleBlock --- bridge_rg --- renorm_fixedPoint_iff
      |             +-- NullBlock ---- bridge_null -- null_determines_up_to_trace
      |             +-- BFBlock ------ bridge_bf ---- decompose
      |             +-- EndptBlock --- bridge_einstein - lovelock_endpoint
      |                                  |
      |                          unified_branch
      |                                  |
      +-- DefectBlock                    |
            |                            |
            +-- defect_source_bridge     |
            +-- defect_dichotomy         |
            +-- charge_additive          |
            +-- annihilation_is_inert    |
            +-- charge_sector_structure  |
            +-- multi_particle_structure |
            +-- far_field_theorem        |
            |                            |
            +------------ matter_einstein_branch
                                  |
                          concrete_realization
                          concrete_many_body
-/
