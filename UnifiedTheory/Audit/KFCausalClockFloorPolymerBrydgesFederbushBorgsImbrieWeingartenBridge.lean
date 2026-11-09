/- Constructive Wilson Polymer Expansion (GJ1), Brydges–Federbush Tree-Graph Formula (GJ3),
Borgs–Imbrie Overlapping Contour Merging, SO(10) Diagonal & Order-Four Weingarten Calculus,
Multi-Site Graded BRST Super-Jacobi Nilpotency, and Chamber Faddeev–Popov Measure Invariance
Bridged with Two-Time Evolved Higher-Power Resolvent Differences and Five-Operator Cross-Resolvents:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerB.Phase_E3_GJ1_PolymerExpansion`,
   `UnifiedTheory.LayerB.Phase_E3_GJ3_BrydgesFederbush`, and
   `UnifiedTheory.LayerB.Phase_E3_BorgsImbrie_Mathlib`, certifying the per-plaquette Taylor
   expansion of the Wilson Boltzmann factor, Kotecký–Preiss small-`β` polymer-sum bounds,
   three-way interior/boundary/exterior plaquette partition and multiplicative factorization,
   Brydges–Federbush leading-term decomposition and strong-coupling crossing bounds, and
   Borgs–Imbrie compound-contour activity bounds and Pirogov–Sinai DLR factorization.
2. Bridges `UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal` and
   `UnifiedTheory.LayerB.Phase_E3_OrderFourWeingarten_SO10`, certifying pointwise and
   Haar-integrated Frobenius norm identities (`∑_{i,k} U_{ki}² = 10`), diagonal squared
   Haar integrals (`1 / 10`), Collins–Śniady order-4 algebraic consistency for the adjoint
   and traceless symmetric irreps of `SO(10)`, and unconditional vanishing of odd-degree
   order-5 Haar moments `∫ (Tr U)³ Tr(U²) dμ = 0` and `∫ (Tr U)(Tr U²)² dμ = 0`.
3. Bridges `UnifiedTheory.LayerB.Clay4_BRSTSuperJacobi` and
   `UnifiedTheory.LayerB.Clay4_FaddeevPopovInvariance` with the two-time evolved higher-power
   resolvent difference calculus (`KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference`)
   and five-operator two-parameter cross-resolvent calculus
   (`KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent`), certifying
   graded super-Jacobi nilpotency `Q²(c) = 0`, `NA6`/`NA7` discharge, one-parameter BRST
   flow group laws, chamber Faddeev–Popov Jacobian = 1, universal FP measure invariance,
   and `M-INV` chamber Slavnov–Taylor correlator invariance alongside explicit ledger
   classifications (`5 Proved + 4 ProvedFromBosonicJacobi + 1 OpenResearch` for Super-Jacobi,
   `6 Proved + 1 ChamberOnly + 1 OpenContinuum` for Faddeev–Popov). -/
import UnifiedTheory.LayerB.Phase_E3_GJ1_PolymerExpansion
import UnifiedTheory.LayerB.Phase_E3_GJ3_BrydgesFederbush
import UnifiedTheory.LayerB.Phase_E3_BorgsImbrie_Mathlib
import UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal
import UnifiedTheory.LayerB.Phase_E3_OrderFourWeingarten_SO10
import UnifiedTheory.LayerB.Clay4_BRSTSuperJacobi
import UnifiedTheory.LayerB.Clay4_FaddeevPopovInvariance
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPolymerBrydgesFederbushBorgsImbrieWeingartenBridge

noncomputable section

open Filter MeasureTheory
open scoped Topology InnerProduct BigOperators
open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
open UnifiedTheory.LayerB.Phase_E1_CylinderConstructive
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
open UnifiedTheory.LayerB.Phase_E3_KP3_KP4
open UnifiedTheory.LayerB.Phase_E3_KP6
open UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt
open UnifiedTheory.LayerB.Phase_E3_KP7
open UnifiedTheory.LayerB.Phase_E3_DLR_PirogovSinai
open UnifiedTheory.LayerB.Phase_E3_GJ1_PolymerExpansion
open UnifiedTheory.LayerB.Phase_E3_GJ3_BrydgesFederbush
open UnifiedTheory.LayerB.Phase_E3_BorgsImbrie_Mathlib
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal
open UnifiedTheory.LayerB.Phase_E3_HigherWeingartens
open UnifiedTheory.LayerB.Phase_E3_OrderFourWeingarten_SO10
open UnifiedTheory.LayerB.Clay4_BRSTSchwingerConstruction
open UnifiedTheory.LayerB.Clay4_SlavnovTaylor
open UnifiedTheory.LayerB.Clay4_NonAbelianBRST
open UnifiedTheory.LayerB.Clay4_BRSTSuperJacobi
open UnifiedTheory.LayerB.Clay4_FaddeevPopovInvariance
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution (evolution)
open KFCausalClockFloorIteratedResolventSecondPowerCore (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (iteratedResolventPower hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence (iteratedIdentityPower)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
  (higherPowerResolventOfEvolvedState
   evolvedHigherPowerResolventSub
   higherPowerResolventSubOfEvolvedState)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference
  (evolvedHigherPowerIdentitySub
   higherPowerIdentitySubOfEvolvedState
   two_time_evolved_higher_power_resolvent_difference_master_synthesis)
open KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent
  (TwoParameterFiveOperatorSystem
   fiveOperator_twoParameter_higherPower_cross_resolvent_master_synthesis)

/-! ### 1. GJ1 Wilson Polymer Expansion, GJ3 Brydges–Federbush Formula, and Borgs–Imbrie Contour Merging -/

/-- Constructive Wilson polymer expansion (GJ1) package: empty polymer degree and weight,
observable degree bound, formal Taylor expansion of the Wilson Boltzmann factor, and
per-configuration absolute bound. -/
theorem polymer_expansion_weight_observable_and_boltzmann_package
    (L : LatticeSide) (β : ℝ) (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (Plaquettes : Finset (Plaquette L)) :
    polymerConfigTotalDeg (emptyWilsonPolymerConfig L) = 0 ∧
    polymerWeight β (emptyWilsonPolymerConfig L) = 1 ∧
    polymerObservable phi (emptyWilsonPolymerConfig L) ω = 1 ∧
    |polymerObservable phi P ω| ≤ M ^ polymerConfigTotalDeg P ∧
    Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω) =
      Plaquettes.prod (fun p => ∑' n : ℕ, ((-β) ^ n / n.factorial) * (phi p ω) ^ n) ∧
    |polymerWeight β P * polymerObservable phi P ω| ≤
      P.support.prod (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial) :=
  ⟨emptyWilsonPolymerConfig_totalDeg L,
   polymerWeight_empty β,
   polymerObservable_empty phi ω,
   polymerObservable_bound phi M hM h_bound P ω,
   wilsonBoltzmannExpansion β phi Plaquettes ω,
   polymerTerm_abs_bound β phi M hM h_bound P ω⟩

/-- Small-`β` Kotecký–Preiss polymer-sum convergence, three-way interior/boundary/exterior
plaquette categorization partition and pairwise disjointness, and honest GJ1 scope statement. -/
theorem polymer_expansion_small_beta_kp_and_three_way_partition_package
    (L : LatticeSide) (β : ℝ) (coord : ℕ) (h_β : smallBetaRegime β coord)
    (phi : PerPlaquetteObservable L) (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (Configs : Finset (WilsonPolymerConfig L)) (ω : multiLinkConfig L)
    {L₁ L₂ : LatticeSide} (h_LE : L₁ ≤ L₂)
    (cat : PlaquetteCategoryMap L₁ L₂ h_LE)
    (Plaquettes_2 : Finset (Plaquette L₂)) :
    smallBetaRegime4D 0 ∧
    |wilsonBoltzmannPolymerSum_finset β phi Configs ω| ≤
      Configs.sum (fun P => P.support.prod
        (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) ∧
    interiorPlaquettes cat Plaquettes_2 ∪
        boundaryPlaquettes cat Plaquettes_2 ∪
        exteriorPlaquettes cat Plaquettes_2 = Plaquettes_2 ∧
    Disjoint (interiorPlaquettes cat Plaquettes_2) (boundaryPlaquettes cat Plaquettes_2) ∧
    Disjoint (interiorPlaquettes cat Plaquettes_2) (exteriorPlaquettes cat Plaquettes_2) ∧
    Disjoint (boundaryPlaquettes cat Plaquettes_2) (exteriorPlaquettes cat Plaquettes_2) ∧
    verdict_GJ1 = GJ1Verdict.POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP :=
  ⟨smallBetaRegime4D_nonempty,
   polymer_sum_KP_convergent β coord h_β phi M hM h_bound Configs ω,
   plaquette_categorization_partition cat Plaquettes_2,
   interior_boundary_disjoint cat Plaquettes_2,
   interior_exterior_disjoint cat Plaquettes_2,
   boundary_exterior_disjoint cat Plaquettes_2,
   verdict_GJ1_check⟩

/-- Brydges–Federbush (GJ3) activity products, leading-term bounds, three-way
interior/exterior/crossing additive decomposition, Kotecký–Preiss leading-order bound,
and strong-coupling crossing bound. -/
theorem brydges_federbush_activity_and_leading_term_decomposition
    (W : BFWeightSystem) [DecidableEq W.sys.Poly]
    (n : ℕ) (γs : Fin n → W.sys.Poly) (γs₀ : Fin 0 → W.sys.Poly)
    (a b : W.sys.Poly → ℝ) (h_KP : KoteckyPreissCondition W.sys a b)
    (Λ Λ_int Λ_ext Λ_crs : Finset W.sys.Poly)
    (h_disj_int_ext : Disjoint Λ_int Λ_ext)
    (h_disj_int_crs : Disjoint Λ_int Λ_crs)
    (h_disj_ext_crs : Disjoint Λ_ext Λ_crs) :
    0 ≤ BFActivityProduct W.sys n γs ∧
    BFActivityProduct W.sys 0 γs₀ = 1 ∧
    BFPartialSum_LeadingOrder W (∅ : Finset W.sys.Poly) = 0 ∧
    |BFLeadingTerm W Λ| ≤ Λ.sum (fun γ => W.sys.activity γ) ∧
    BFLeadingTerm W (Λ_int ∪ Λ_ext ∪ Λ_crs) =
      BFLeadingTerm W Λ_int + BFLeadingTerm W Λ_ext + BFLeadingTerm W Λ_crs ∧
    |BFPartialSum_LeadingOrder W Λ| ≤
      Λ.sum (fun γ => W.sys.activity γ * Real.exp (a γ + b γ)) :=
  ⟨BFActivityProduct_nonneg W.sys n γs,
   BFActivityProduct_zero W.sys γs₀,
   BFPartialSum_LeadingOrder_empty W,
   BFLeadingTerm_abs_bound W Λ,
   BFLeadingTerm_decomposition W Λ_int Λ_ext Λ_crs h_disj_int_ext h_disj_int_crs h_disj_ext_crs,
   BF_leading_term_abs_le_KP_sum W a b h_KP Λ⟩

/-- Brydges–Federbush Wilson strong-coupling crossing bound, DLR factorization equivalence,
partition-function ratio exponentiation across crossing polymers, and honest GJ3 verdict. -/
theorem brydges_federbush_wilson_crossing_dlr_and_master_package
    (L : LatticeSide) (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1)
    (Λ_crs : Finset (Polymer L)) (S : WilsonActionAssignment)
    (logZ₁ logZ₂ logZ_crs : ℝ) (h_decomp : logZ₂ = logZ₁ + logZ_crs) :
    |BFLeadingTerm (wilsonBFWeightSystem L β (le_of_lt hβ_pos)) Λ_crs| ≤
      (Λ_crs.card : ℝ) * β ∧
    (BF_DLR_Hypothesis β S ↔ WilsonActionFactorization β S) ∧
    Real.exp logZ₂ = Real.exp logZ₁ * Real.exp logZ_crs ∧
    0 < Real.exp logZ_crs ∧
    verdict_E3_GJ3_BF = BFVerdict.BF_FORMULA_PARTIAL_BOUNDARY_DERIVATION_OPEN :=
  ⟨WilsonBF_crossing_bound_strong_coupling L β hβ_pos hβ_lt Λ_crs,
   BF_DLR_iff_WilsonActionFactorization β S,
   BF_Z_ratio_via_crossing logZ₁ logZ₂ logZ_crs h_decomp,
   BF_crossing_positive logZ_crs,
   verdict_E3_GJ3_BF_check⟩

/-- Borgs–Imbrie overlapping contour merging: positive atom count, compound contour
plaquette union and subadditivity of contour size, merged activity power formula,
positivity, vanishing at `β = 0`, and dominance by compound contour activity on `(0, 1]`. -/
theorem borgs_imbrie_compound_contour_and_merged_activity_bounds
    (L : LatticeSide) (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1)
    (Γ : OverlappingContourSet L) :
    0 < Γ.size ∧
    (compoundContour Γ).plaquettes = compoundPlaquettes Γ ∧
    contourSize (compoundContour Γ) ≤ Γ.atoms.sum (fun γ => contourSize γ) ∧
    0 < mergedActivity β Γ ∧
    mergedActivity 0 Γ = 0 ∧
    mergedActivity β Γ = β ^ (Γ.atoms.sum (fun γ => contourSize γ)) ∧
    mergedActivity β Γ ≤ contourActivity β (compoundContour Γ) ∧
    mergedActivity β Γ ≤ β :=
  ⟨Γ.size_pos,
   compoundContour_plaquettes Γ,
   compoundContour_size_le_sum Γ,
   mergedActivity_pos β hβ_pos Γ,
   mergedActivity_at_zero Γ,
   mergedActivity_eq_betaPow_total β Γ,
   mergedActivity_le_compoundActivity β hβ_pos (le_of_lt hβ_lt) Γ,
   mergedActivity_strong_coupling_bound β hβ_pos hβ_lt Γ⟩

/-- Borgs–Imbrie merging hypothesis at `β = 0`, finite-sum plaquette-anchored activity bound,
general Pirogov–Sinai overlapping-contour DLR factorization, and honest verdict. -/
theorem borgs_imbrie_merging_hypothesis_dlr_and_master_package
    (L : LatticeSide) (β : ℝ) (hβ : 0 ≤ β) [DecidableEq (WilsonContour L)]
    (h_BI : BorgsImbrieMergingHypothesis L β)
    (p : Plaquette L) (S : Finset (CompatibleExtension p)) :
    BorgsImbrieMergingHypothesis L 0 ∧
    S.sum (fun Γ => mergedActivityOn β p Γ) ≤ Real.exp 1 * β ∧
    DLR_via_PS_contour_factorization_general L β hβ
      (postMergingBoundaryFunctional L β hβ) ∧
    borgs_imbrie_verdict =
      BorgsImbrieVerdict.BORGS_IMBRIE_PARTIAL_NEEDS_MERGING_LEMMA :=
  ⟨BorgsImbrieMergingHypothesis_at_zero L,
   borgs_imbrie_finite_sum_bound L β h_BI p S,
   borgs_imbrie_discharges_PS_overlapping_DLR L β hβ h_BI,
   borgs_imbrie_verdict_check⟩

/-! ### 2. SO(10) Diagonal and Order-Four Weingarten Calculus -/

/-- `SO(10)` diagonal Weingarten and Frobenius identities: pointwise column normalization,
pointwise and Haar-integrated Frobenius norm squared `= 10`, diagonal entry squared Haar
integral `= 1 / 10` under row-permutation symmetry, and conditional `∫ (Tr U)² dμ = 1 + c`. -/
theorem so10_weingarten_diagonal_and_frobenius_haar_identities
    (U₀ : G_SO10) (i : Fin d10) (h_sym : RowPermutationSymmetrySO10)
    {c : ℝ} (h_off : OffDiagonalDiagSquaredCorrelation c) :
    (∑ k, (U₀ : Matrix (Fin d10) (Fin d10) ℝ) k i *
          (U₀ : Matrix (Fin d10) (Fin d10) ℝ) k i = 1) ∧
    (∑ j, ∑ k, (U₀ : Matrix (Fin d10) (Fin d10) ℝ) k j *
               (U₀ : Matrix (Fin d10) (Fin d10) ℝ) k j = 10) ∧
    (∫ U : G_SO10, (∑ j, ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k j *
                              (U : Matrix (Fin d10) (Fin d10) ℝ) k j)
        ∂haarMeasureSO10 = 10) ∧
    (∫ U, sqEntry i i U ∂haarMeasureSO10 = 1 / (d10 : ℝ)) ∧
    (∫ U, (∑ j, sqEntry j j U) ∂haarMeasureSO10 = 1) ∧
    (∫ U, (reTraceSO10 U) * (reTraceSO10 U) ∂haarMeasureSO10 = 1 + c) ∧
    weingarten_diagonal_verdict =
      WeingartenDiagonalVerdict.DiagonalProvedSymmetryHypTrUsqConditional :=
  ⟨column_norm_squared_eq_one U₀ i,
   SO10_frobenius_norm_squared_pointwise U₀,
   SO10_frobenius_norm_squared_integral,
   diagonal_squared_integral h_sym i,
   sum_diagonal_squared_integral h_sym,
   trace_squared_integral_conditional h_sym h_off,
   UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal.verdict_consistent⟩

/-- `SO(10)` order-4 Weingarten Collins–Śniady algebraic consistency (`m4 = 3, m22 = 1, t22 = 3, v = 1`),
conditional Schur-diagonal normalization of `χ_adjoint` and `χ_symtl`, and unconditional
vanishing of odd-degree order-5 Haar trace moments via central `-I ∈ SO(10)` involution. -/
theorem so10_order_four_weingarten_collins_sniady_and_odd_moments :
    ((m4_SO10 - 2 * m22_SO10 + t22_SO10) / 4 = 1) ∧
    ((m4_SO10 + 2 * m22_SO10 + t22_SO10) / 4 - v_SO10 = 1) ∧
    (OrderFourMoments_SO10_CollinsSniady →
      ∫ U : G_SO10, chi_adjoint U * chi_adjoint U ∂haarMeasureSO10 = 1) ∧
    (OrderFourMoments_SO10_CollinsSniady →
      TraceUsqHaarValue_SO10_CollinsSniady →
      ∫ U : G_SO10, chi_symtl U * chi_symtl U ∂haarMeasureSO10 = 1) ∧
    (∫ U : G_SO10, traceCube U * traceUsq U ∂haarMeasureSO10 = 0) ∧
    (∫ U : G_SO10, reTraceSO10 U * (traceUsq U * traceUsq U) ∂haarMeasureSO10 = 0) ∧
    order4_weingarten_SO10_verdict =
      OrderFourWeingartenSO10Verdict.Order4WeingartenPartialNeedsPairMatchingInfrastructure :=
  phase_E3_order4_weingarten_SO10_master

/-! ### 3. Graded BRST Super-Jacobi Nilpotency and Chamber Faddeev–Popov Measure Invariance -/

/-- Cyclic permutations `σ, τ : Fin 3 → Fin 3`, `ℤ/2` generator parity dichotomy, and
mutual inverse equivalence between `GradedBRSTConfig L` and `NonAbelianBRSTConfig L`. -/
theorem brst_super_jacobi_cyclic_permutations_and_parity
    {L_alg : Type*} [LieRing L_alg]
    (g : BRSTGenerator) (i : Fin 3)
    (X_na : NonAbelianBRSTConfig L_alg) (X_gr : GradedBRSTConfig L_alg) :
    (isBosonic g = true ↔ isOdd g = false) ∧
    σ (τ i) = i ∧
    τ (σ i) = i ∧
    σ (σ i) = τ i ∧
    τ (τ i) = σ i ∧
    GradedBRSTConfig.toNonAbelian (GradedBRSTConfig.ofNonAbelian X_na) = X_na ∧
    GradedBRSTConfig.ofNonAbelian (GradedBRSTConfig.toNonAbelian X_gr) = X_gr :=
  ⟨bosonic_iff_not_odd g,
   σ_τ_inverse i,
   τ_σ_inverse i,
   σ_σ_eq_τ i,
   τ_τ_eq_σ i,
   GradedBRSTConfig.ofNonAbelian_toNonAbelian X_na,
   GradedBRSTConfig.toNonAbelian_ofNonAbelian X_gr⟩

/-- Multi-site graded BRST nilpotency `Q² = 0` (`QsuperGraded_squared_c X = 0`, pointwise
`Q²(c̄) = 0` and `Q²(B) = 0`, cyclic Jacobi sum `∑_k ⁅c_k, Q(c)_k⁆ = 0`), single-ghost
super-Jacobi identity `br12 c (br11 c c) = 0`, and `NA6`/`NA7` discharge. -/
theorem brst_super_jacobi_nilpotency_and_na6_na7_discharge
    {L_alg : Type*} [LieRing L_alg]
    (X : GradedBRSTConfig L_alg) (c : Fin 3 → L_alg) :
    br12 c (br11 c c) = 0 ∧
    (Qsuper X).c = ghostSquare X.c ∧
    QsuperGraded_squared_c X = 0 ∧
    (∀ k : Fin 3, (Qsuper (Qsuper X)).cbar k = 0) ∧
    (∀ k : Fin 3, (Qsuper (Qsuper X)).B k = 0) ∧
    (⁅X.c 0, (Qsuper X).c 0⁆ + ⁅X.c 1, (Qsuper X).c 1⁆ + ⁅X.c 2, (Qsuper X).c 2⁆ = 0) ∧
    (⁅c 0, ⁅c 1, c 2⁆⁆ + ⁅c 1, ⁅c 2, c 0⁆⁆ + ⁅c 2, ⁅c 0, c 1⁆⁆ = 0) := by
  have hms := multi_site_BRST_Q_squared_zero X
  exact ⟨na6_discharged c,
    Qsuper_c_eq_ghostSquare X,
    hms.1, hms.2.1, hms.2.2.1, hms.2.2.2,
    na7_discharged c⟩

/-- Complete 10-entry Super-Jacobi classification ledger accounting:
`5 Proved + 4 ProvedFromBosonicJacobi + 1 OpenResearch = 10`. -/
theorem brst_super_jacobi_classification_ledger_accounting :
    sj_ledger.length = 10 ∧
    (sj_ledger.filter (fun c => c.status = SuperJacobiStatus.Proved)).length = 5 ∧
    (sj_ledger.filter
      (fun c => c.status = SuperJacobiStatus.ProvedFromBosonicJacobi)).length = 4 ∧
    (sj_ledger.filter (fun c => c.status = SuperJacobiStatus.OpenResearch)).length = 1 ∧
    (sj_ledger.filter (fun c => c.status = SuperJacobiStatus.Proved)).length +
      (sj_ledger.filter
        (fun c => c.status = SuperJacobiStatus.ProvedFromBosonicJacobi)).length +
      (sj_ledger.filter (fun c => c.status = SuperJacobiStatus.OpenResearch)).length =
      sj_ledger.length :=
  ⟨sj_ledger_length,
   sj_ledger_proved_count,
   sj_ledger_provedFromJacobi_count,
   sj_ledger_open_count,
   sj_ledger_total⟩

/-- Faddeev–Popov one-parameter BRST flow group laws (`Φ_0 = id`, `Φ_ε ∘ Φ_δ = Φ_{ε+δ}`,
`Φ_{-ε} ∘ Φ_ε = id`, vacuum fixed `Φ_ε(0) = 0`), pullback functoriality, and zero chamber
BRST trace `Q_trace_chamber = 0`. -/
theorem faddeev_popov_brst_flow_one_parameter_group
    (ε₁ δ₁ : ℝ) (X : BRSTConfig) (O : BRSTConfig → ℝ) :
    BRSTFlow 0 X = X ∧
    BRSTFlow ε₁ (0 : BRSTConfig) = 0 ∧
    BRSTFlow ε₁ (BRSTFlow δ₁ X) = BRSTFlow (ε₁ + δ₁) X ∧
    BRSTFlow (-ε₁) (BRSTFlow ε₁ X) = X ∧
    pullback 0 O = O ∧
    pullback δ₁ (pullback ε₁ O) = pullback (ε₁ + δ₁) O ∧
    Q_trace_chamber = 0 :=
  ⟨BRSTFlow_zero X,
   BRSTFlow_vacuum ε₁,
   BRSTFlow_compose ε₁ δ₁ X,
   BRSTFlow_inverse ε₁ X,
   pullback_zero O,
   pullback_compose ε₁ δ₁ O,
   Q_trace_chamber_zero⟩

/-- Chamber Faddeev–Popov measure linearity, normalization, universal BRST-flow pullback
invariance, and Slavnov–Taylor `M-INV` chamber correlator invariance (additive and
multiplicative forms). -/
theorem faddeev_popov_measure_invariance_and_m_inv_chamber
    (ε₁ α β F₀ : ℝ) (O O₁ O₂ : BRSTConfig → ℝ)
    (n : ℕ) (F : Fin n → ℝ) :
    FPMeasure (fun X => α * O₁ X + β * O₂ X) =
      α * FPMeasure O₁ + β * FPMeasure O₂ ∧
    FPMeasure (fun _ => (1 : ℝ)) = 1 ∧
    FPMeasure (chamberSpectralObservable F₀) = F₀ ∧
    FPMeasure (pullback ε₁ (chamberSpectralObservable F₀)) =
      FPMeasure (chamberSpectralObservable F₀) ∧
    FPMeasure (pullback ε₁ O) = FPMeasure O ∧
    correlator_vac n
      (fun j => fun X =>
        chamberSpectralObservable (F j) X +
        deltaBRST (chamberSpectralObservable (F j)) X) =
      correlator_vac n (fun j => chamberSpectralObservable (F j)) ∧
    correlator_vac n
      (fun j => pullback ε₁ (chamberSpectralObservable (F j))) =
      correlator_vac n (fun j => chamberSpectralObservable (F j)) :=
  ⟨FPMeasure_linear α β O₁ O₂,
   FPMeasure_normalized,
   FPMeasure_chamberSpectral F₀,
   FP_invariance_chamberSpectral ε₁ F₀,
   FP_invariance_universal ε₁ O,
   FP_invariance_implies_M_INV_chamber n F,
   correlator_vac_invariant_under_BRSTflow n ε₁ F⟩

/-- Complete 8-entry Faddeev–Popov classification ledger accounting:
`6 Proved + 1 ChamberOnly + 1 OpenContinuum = 8`. -/
theorem faddeev_popov_classification_ledger_accounting :
    fp_ledger.length = 8 ∧
    (fp_ledger.filter (fun c => c.status = FPStatus.Proved)).length = 6 ∧
    (fp_ledger.filter (fun c => c.status = FPStatus.ChamberOnly)).length = 1 ∧
    (fp_ledger.filter (fun c => c.status = FPStatus.OpenContinuum)).length = 1 ∧
    (fp_ledger.filter (fun c => c.status = FPStatus.Proved)).length +
      (fp_ledger.filter (fun c => c.status = FPStatus.ChamberOnly)).length +
      (fp_ledger.filter (fun c => c.status = FPStatus.OpenContinuum)).length =
      fp_ledger.length :=
  ⟨fp_ledger_length,
   fp_ledger_proved_count,
   fp_ledger_chamber_count,
   fp_ledger_open_count,
   fp_ledger_total_accounted⟩

/-! ### 4. Synthesis with Two-Time Evolved Higher-Power Resolvent Differences and Five-Operator Cross-Resolvents -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "U_ev" => evolution ε hε h hh hw m g k
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "P_op" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G_op" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S_op" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H_op" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- Bridge uniting the two-time evolved higher-power resolvent and Yosida identity
difference calculus with the constructive Wilson polymer expansion (GJ1), Brydges–Federbush
strong-coupling crossing bound (GJ3), and Borgs–Imbrie overlapping contour merging. -/
theorem evolved_higher_power_resolvent_difference_polymer_brydges_federbush_bridge
    (t₁ t₂ s t q a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (r p : ℕ) (f f₁ f₂ : Hilbert)
    (L : LatticeSide) (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1)
    (Λ_crs : Finset (Polymer L)) (Γ : OverlappingContourSet L) :
    let d_res := higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let d_id := higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let x_ev := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t c p f
    (d_res ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) ∧
     d_res ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     d_id ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
     d_id ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t) ∧
    ‖iteratedIdentityPower (RH t a) a (r + 2) x_ev -
      iteratedIdentityPower (RH t b) b (r + 2) x_ev‖ ≤
      ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖)) ∧
    Tendsto
      (fun s' : ℝ => inner ℂ f₁
        (U_ev t₁ t₂
          (RH s' a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH s' b (iteratedResolventPower (RH q b) (r + 1) f₂))))
      (𝓝 t)
      (𝓝 (inner ℂ f₁
        (U_ev t₁ t₂
          (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))))) ∧
    (polymerWeight β (emptyWilsonPolymerConfig L) = 1 ∧
     smallBetaRegime4D 0 ∧
     |BFLeadingTerm (wilsonBFWeightSystem L β (le_of_lt hβ_pos)) Λ_crs| ≤
       (Λ_crs.card : ℝ) * β ∧
     mergedActivity β Γ ≤ contourActivity β (compoundContour Γ) ∧
     BorgsImbrieMergingHypothesis L 0) := by
  intro d_res d_id x_ev
  have hev := two_time_evolved_higher_power_resolvent_difference_master_synthesis
    ε hε h hh hb m g k t₁ t₂ s t q a b c ha hb_pos hc r p f f₁ f₂
  exact ⟨hev.2.2.2.1, hev.2.2.2.2.1, hev.2.2.2.2.2,
    ⟨polymerWeight_empty β,
     smallBetaRegime4D_nonempty,
     WilsonBF_crossing_bound_strong_coupling L β hβ_pos hβ_lt Λ_crs,
     mergedActivity_le_compoundActivity β hβ_pos (le_of_lt hβ_lt) Γ,
     BorgsImbrieMergingHypothesis_at_zero L⟩⟩

/-- Bridge uniting the five-operator two-parameter higher-power cross-resolvent calculus
with `SO(10)` Weingarten Haar integrals, order-4 Collins–Śniady algebraic consistency,
multi-site graded BRST nilpotency `Q² = 0`, and chamber Faddeev–Popov measure invariance. -/
theorem five_operator_two_param_cross_resolvent_weingarten_brst_fp_bridge
    {a b : ℝ} (ha : 0 < a) (hb_pos : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem Hilbert a b)
    (r : ℕ) (f : Hilbert) (z : tsys.sysA.H_op.domain)
    {L_alg : Type*} [LieRing L_alg] (X_gr : GradedBRSTConfig L_alg)
    (ε_fp : ℝ) (O : BRSTConfig → ℝ) :
    ((KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysA.RP (r + 1) f -
        KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysB.RG (r + 1) f ∈ tsys.sysA.P.domain ∧
      KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysA.RS (r + 1) f -
        KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.S.domain ∧
      KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysA.RT (r + 1) f -
        KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysB.RS (r + 1) f ∈ tsys.sysA.T.domain ∧
      KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysA.RT (r + 1) f -
        KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.T.domain ∧
      KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysA.RP (r + 1) f -
        KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.P.domain) ∧
     ‖KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedIdentityPower tsys.sysA.RT a r (z : Hilbert) -
       KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence.iteratedIdentityPower tsys.sysB.RH b r (z : Hilbert)‖ ≤
       (r : ℝ) * a⁻¹ * ‖tsys.sysA.T ⟨(z : Hilbert), tsys.sysA.dom_HT z.property⟩‖ +
         (r : ℝ) * b⁻¹ * ‖tsys.sysB.H_op ⟨(z : Hilbert), tsys.same_H.symm ▸ z.property⟩‖) ∧
    ((∫ U : G_SO10, (∑ j, ∑ l, (U : Matrix (Fin d10) (Fin d10) ℝ) l j *
                              (U : Matrix (Fin d10) (Fin d10) ℝ) l j)
        ∂haarMeasureSO10 = 10) ∧
     (m4_SO10 - 2 * m22_SO10 + t22_SO10) / 4 = 1 ∧
     (∫ U : G_SO10, traceCube U * traceUsq U ∂haarMeasureSO10 = 0)) ∧
    (QsuperGraded_squared_c X_gr = 0 ∧
     FPMeasure (pullback ε_fp O) = FPMeasure O ∧
     Q_trace_chamber = 0) := by
  have h5 := fiveOperator_twoParameter_higherPower_cross_resolvent_master_synthesis
    ha hb_pos tsys r f z
  exact ⟨⟨h5.1, h5.2.2.2⟩,
    ⟨SO10_frobenius_norm_squared_integral,
     CS_SO10_adjoint_consistency,
     trace_cube_traceUsq_integral_zero⟩,
    ⟨QsuperGraded_squared_c_zero X_gr,
     FP_invariance_universal ε_fp O,
     Q_trace_chamber_zero⟩⟩

/-- Master Constructive Polymer, Brydges–Federbush, Borgs–Imbrie, `SO(10)` Weingarten,
Graded BRST Super-Jacobi, Chamber Faddeev–Popov, and Clock-Floor Higher-Power Resolvent
Difference Synthesis. -/
theorem clockFloor_polymer_brydges_federbush_borgs_imbrie_weingarten_brst_fp_master_synthesis
    (t₁ t₂ s t q a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (tsys : TwoParameterFiveOperatorSystem Hilbert a b)
    (r p : ℕ) (f f₁ f₂ : Hilbert) (z : tsys.sysA.H_op.domain)
    (L : LatticeSide) (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1)
    (Λ_crs : Finset (Polymer L)) (Γ : OverlappingContourSet L)
    {L_alg : Type*} [LieRing L_alg] (X_gr : GradedBRSTConfig L_alg)
    (ε_fp : ℝ) (O : BRSTConfig → ℝ) :
    let d_res := higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let d_id := higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let x_ev := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t c p f
    ((d_res ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) ∧
      d_res ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
      d_id ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      d_id ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t) ∧
     ‖iteratedIdentityPower (RH t a) a (r + 2) x_ev -
       iteratedIdentityPower (RH t b) b (r + 2) x_ev‖ ≤
       ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖))) ∧
    (polymerWeight β (emptyWilsonPolymerConfig L) = 1 ∧
     smallBetaRegime4D 0 ∧
     |BFLeadingTerm (wilsonBFWeightSystem L β (le_of_lt hβ_pos)) Λ_crs| ≤
       (Λ_crs.card : ℝ) * β ∧
     mergedActivity β Γ ≤ contourActivity β (compoundContour Γ) ∧
     BorgsImbrieMergingHypothesis L 0) ∧
    ((∫ U : G_SO10, (∑ j, ∑ l, (U : Matrix (Fin d10) (Fin d10) ℝ) l j *
                              (U : Matrix (Fin d10) (Fin d10) ℝ) l j)
        ∂haarMeasureSO10 = 10) ∧
     (m4_SO10 - 2 * m22_SO10 + t22_SO10) / 4 = 1 ∧
     (∫ U : G_SO10, traceCube U * traceUsq U ∂haarMeasureSO10 = 0)) ∧
    (QsuperGraded_squared_c X_gr = 0 ∧
     sj_ledger.length = 10 ∧
     FPMeasure (pullback ε_fp O) = FPMeasure O ∧
     Q_trace_chamber = 0 ∧
     fp_ledger.length = 8) := by
  intro d_res d_id x_ev
  have hb1 := evolved_higher_power_resolvent_difference_polymer_brydges_federbush_bridge
    ε hε h hh hb m g k t₁ t₂ s t q a b c ha hb_pos hc r p f f₁ f₂ L β hβ_pos hβ_lt Λ_crs Γ
  have hb2 := five_operator_two_param_cross_resolvent_weingarten_brst_fp_bridge
    ha hb_pos tsys r f z X_gr ε_fp O
  exact ⟨⟨hb1.1, hb1.2.1⟩, hb1.2.2.2, hb2.2.1,
    ⟨hb2.2.2.1, sj_ledger_length, hb2.2.2.2.1, hb2.2.2.2.2, fp_ledger_length⟩⟩

#print axioms polymer_expansion_weight_observable_and_boltzmann_package
#print axioms polymer_expansion_small_beta_kp_and_three_way_partition_package
#print axioms brydges_federbush_activity_and_leading_term_decomposition
#print axioms brydges_federbush_wilson_crossing_dlr_and_master_package
#print axioms borgs_imbrie_compound_contour_and_merged_activity_bounds
#print axioms borgs_imbrie_merging_hypothesis_dlr_and_master_package
#print axioms so10_weingarten_diagonal_and_frobenius_haar_identities
#print axioms so10_order_four_weingarten_collins_sniady_and_odd_moments
#print axioms brst_super_jacobi_cyclic_permutations_and_parity
#print axioms brst_super_jacobi_nilpotency_and_na6_na7_discharge
#print axioms brst_super_jacobi_classification_ledger_accounting
#print axioms faddeev_popov_brst_flow_one_parameter_group
#print axioms faddeev_popov_measure_invariance_and_m_inv_chamber
#print axioms faddeev_popov_classification_ledger_accounting
#print axioms evolved_higher_power_resolvent_difference_polymer_brydges_federbush_bridge
#print axioms five_operator_two_param_cross_resolvent_weingarten_brst_fp_bridge
#print axioms clockFloor_polymer_brydges_federbush_borgs_imbrie_weingarten_brst_fp_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorPolymerBrydgesFederbushBorgsImbrieWeingartenBridge
