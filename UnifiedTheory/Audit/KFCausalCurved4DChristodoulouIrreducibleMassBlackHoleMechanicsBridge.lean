import UnifiedTheory.Audit.KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
import UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
import UnifiedTheory.LayerB.BekensteinBound

/-! # 4D Christodoulou-Ruffini Irreducible Mass, Penrose Rotational Extraction,
Universal Bekenstein Bound, and Black Hole Mechanics Bridge

This module (`UnifiedTheory.Audit.KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge`)
connects the Christodoulou-Ruffini Kerr irreducible mass and Penrose energy-extraction
framework (`LayerB.ChristodoulouIrreducibleMass`) together with the Bekenstein universal
entropy-to-energy bound (`LayerB.BekensteinBound`) to the curved 4D Schwarzschild-Birkhoff-Hawking,
tidal Weyl/Kretschmann, Hawking-Penrose trapped-surface, and Malament causal-order bridges:

1. **Christodoulou-Ruffini Irreducible Mass & Kerr Horizon Area (`LayerB.ChristodoulouIrreducibleMass`)**:
   - Sub-extremality `kerrSubextremal M J : J^2 ≤ M^4`, extremal Kerr `kerrExtremal M J : J^2 = M^4`,
     and discriminant non-negativity `0 ≤ M^4 - J^2`.
   - Closed-form squared irreducible mass `irreducibleMassSq M J = (M^2 + √(M^4 - J^2)) / 2`
     satisfying `M^2 / 2 ≤ irreducibleMassSq M J ≤ M^2` and `M / √2 ≤ irreducibleMass M J ≤ M`.
   - Kerr horizon area `kerrHorizonArea M J = 16 * π * irreducibleMassSq M J = 8 * π * (M^2 + √(M^4 - J^2))`,
     reducing to `horizonArea M = 16 * π * M^2` in the Schwarzschild limit `J = 0` and to
     `8 * π * M^2 = horizonArea M / 2` in the extremal limit `J^2 = M^4`.
   - Exact Christodoulou-Ruffini mass-energy decomposition
     `M^2 = irreducibleMassSq M J + J^2 / (4 * irreducibleMassSq M J)` for sub-extremal `M ≠ 0`.
   - Penrose rotational energy extraction ceiling `0 ≤ M - irreducibleMass M J ≤ M * (1 - 1 / √2)`,
     vanishing at `J = 0` and saturated at `J^2 = M^4`, together with the Hawking area-theorem
     consequence `M₁ - M₂ ≤ M₁ * (1 - 1 / √2)`.

2. **Kerr Bekenstein-Hawking Entropy & Universal Bekenstein Bound (`LayerB.BekensteinBound`)**:
   - Defines `kerrBekensteinHawkingEntropy M J = kerrHorizonArea M J / 4 = 4 * π * irreducibleMassSq M J`
     and proves the two-sided envelope
     `bekensteinHawkingEntropy M / 2 ≤ kerrBekensteinHawkingEntropy M J ≤ bekensteinHawkingEntropy M`.
   - Proves that every Kerr black hole of mass `M` and spin `J` is Bekenstein-compliant at the
     Schwarzschild configuration `(R = 2M, E = M)`, with saturation iff `J = 0`.
   - Connects the Bekenstein bound `bekensteinBound R E = 2 * π * R * E`, holographic form
     `bekensteinBound (2M) E = horizonArea M * E / (4M)`, and bit-information form
     `bekensteinBoundBits R E = bekensteinBound R E / log 2` to the 4D Schwarzschild Kretschmann
     horizon invariants, Hawking temperature, Smarr law, Sorkin de Sitter entropy,
     interior trapped surfaces, and Malament 4D conformal uniqueness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerB.BekensteinHawking
  (schwarzschildRadius horizonArea bekensteinHawkingEntropy bekensteinHawkingFromArea)
open UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
  (kerrSubextremal kerrExtremal M_pow_four_nonneg schwarzschild_subextremal
   extremal_M_ne_zero kerr_discriminant_nonneg sqrt_disc_le_M_sq
   irreducibleMassSq irreducibleMass irreducibleMassSq_nonneg irreducibleMass_nonneg
   irreducibleMassSq_le_M_sq irreducibleMassSq_ge_half_M_sq
   irreducibleMassSq_J_zero irreducibleMass_J_zero_of_M_nonneg
   Penrose_zero_for_schwarzschild
   irreducibleMassSq_extremal irreducibleMass_extremal_of_M_nonneg
   kerrHorizonArea kerrHorizonArea_eq_irreducible kerrHorizonArea_expanded
   kerrHorizonArea_J_zero kerrHorizonArea_nonneg
   irreducibleMassSq_pos_of_M_ne_zero mass_energy_decomposition
   Penrose_extraction_bound_sq irreducibleMass_ge_M_over_sqrt2
   Penrose_extraction_bound Penrose_extraction_nonneg Penrose_extraction_extremal
   area_theorem_extraction_bound universal_Penrose_bound christodoulou_capstone)
open UnifiedTheory.LayerB.BekensteinBound
  (bekensteinBound bekensteinBound_nonneg bekensteinBound_pos
   bekensteinBound_mono_R bekensteinBound_mono_E
   bekensteinBound_smul_R bekensteinBound_smul_E
   IsBekensteinCompliant zero_entropy_compliant
   schwarzschild_saturates_bound schwarzschild_saturates_bound'
   schwarzschild_bound_eq BH_is_bekenstein BH_saturates_bekenstein
   superBHEntropy_collapses saturation_iff_BH compliant_at_BH_iff
   holographic_form holographic_form_factored holographic_at_E_eq_M
   bekensteinBoundBits log_two_pos log_two_ne_zero bits_form BH_bits_at_saturation
   holographic_principle compliant_iff_quarter_area bekenstein_bound_capstone)
open UnifiedTheory.LayerB.SchwarzschildSolution
  (R_tt R_rr R_thetatheta R_phiphi)
open UnifiedTheory.LayerB.BirkhoffUniqueness
  (IsVacuumSphericallySymmetric StaticGauge schwarzschildAnsatz)
open UnifiedTheory.LayerB.HawkingTemperature
  (hawkingTemperature surfaceGravity evaporationLifetime)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs)
open UnifiedTheory.LayerA.Ostrogradsky (ostrogradsky_hamiltonian)
open UnifiedTheory.LayerA.GaugeConnection (StructureConstants ConnectionData)
open UnifiedTheory.LayerA.CosmologicalConstant (sorkinLambda)
open UnifiedTheory.LayerA.CosmologicalConstantN (BHArea)
open UnifiedTheory.LayerA.NullConeConformal (minkQuadGen)
open UnifiedTheory.LayerA.GeneralMalament (stage3_closed_3plus1)
open UnifiedTheory.LayerC.HawkingPenroseSingularity
  (conjugatePointTime Penrose_Singularity_Target)
open KFCausalConformal4DDiamondBenchmark (sign)
open KFCausalCurved4DLinearizedMetricDecomposition
  (conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit
  (weylTensor4D weylTensor4D_conformalPart_eq_zero weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DLovelockCosmologicalConstantSynthesis
  (SatisfiesEinsteinSorkinYangMills4D)
open KFCausalCurved4DVariationalEinsteinOstrogradskyStabilityBridge
  (einsteinLovelockYangMillsResidual4D
   ostrogradsky_stability_to_einstein_bridge
   einsteinSorkinYangMills4D_iff_variational_stationarity)
open KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
  (schwarzschildKretschmann
   schwarzschild_ricci_components_all_vanish
   schwarzschildKretschmann_at_horizon
   schwarzschildKretschmann_horizon_times_area_sq
   schwarzschildKretschmann_horizon_times_entropy_sq
   schwarzschild_birkhoff_hawking_thermodynamics_4D_master_bridge)
open KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
  (schwarzschildInteriorTrappedSurface
   schwarzschild_interior_trapped_surface_expansions_neg
   schwarzschild_interior_trapped_surface_conjugate_times
   curved_4D_hawking_penrose_malament_master_synthesis)

/-! ### 1. Christodoulou-Ruffini Irreducible Mass, Kerr Horizon Area & Penrose Process -/

/-- **Kerr Sub-Extremality & Discriminant Properties**:
`0 ≤ M^4`, `kerrSubextremal M 0` holds unconditionally, `0 ≤ M^4 - J^2` for sub-extremal
Kerr, `√(M^4 - J^2) ≤ M^2`, and `kerrExtremal M J` with `J ≠ 0` forces `M ≠ 0`. -/
theorem kerr_subextremal_and_discriminant_properties
    (M J : ℝ) (hsub : kerrSubextremal M J) :
    0 ≤ M ^ 4 ∧
    kerrSubextremal M 0 ∧
    0 ≤ M ^ 4 - J ^ 2 ∧
    Real.sqrt (M ^ 4 - J ^ 2) ≤ M ^ 2 ∧
    (kerrExtremal M J → J ≠ 0 → M ≠ 0) :=
  ⟨M_pow_four_nonneg M,
   schwarzschild_subextremal M,
   kerr_discriminant_nonneg hsub,
   sqrt_disc_le_M_sq M J,
   fun hext hJ => extremal_M_ne_zero hext hJ⟩

/-- **Christodoulou Squared Irreducible Mass Bounds**:
`0 ≤ irreducibleMassSq M J`, `M^2 / 2 ≤ irreducibleMassSq M J ≤ M^2`, and
`M ≠ 0 → 0 < irreducibleMassSq M J`. -/
theorem christodoulou_irreducibleMassSq_nonneg_and_bounds (M J : ℝ) :
    0 ≤ irreducibleMassSq M J ∧
    M ^ 2 / 2 ≤ irreducibleMassSq M J ∧
    irreducibleMassSq M J ≤ M ^ 2 ∧
    (M ≠ 0 → 0 < irreducibleMassSq M J) :=
  ⟨irreducibleMassSq_nonneg M J,
   irreducibleMassSq_ge_half_M_sq M J,
   irreducibleMassSq_le_M_sq M J,
   fun hM => irreducibleMassSq_pos_of_M_ne_zero hM⟩

/-- **Christodoulou Linear Irreducible Mass Bounds (`M / √2 ≤ M_irr ≤ M`)**:
For `M ≥ 0` and any `J : ℝ`, `0 ≤ irreducibleMass M J`, `M / √2 ≤ irreducibleMass M J`,
and `irreducibleMass M J ≤ M`. -/
theorem christodoulou_irreducibleMass_nonneg_and_bounds
    (M J : ℝ) (hM : 0 ≤ M) :
    0 ≤ irreducibleMass M J ∧
    M / Real.sqrt 2 ≤ irreducibleMass M J ∧
    irreducibleMass M J ≤ M := by
  have hpen := Penrose_extraction_nonneg hM J
  exact ⟨irreducibleMass_nonneg M J,
    irreducibleMass_ge_M_over_sqrt2 hM J,
    by linarith⟩

/-- **Schwarzschild Limit (`J = 0`) of Christodoulou Irreducible Mass**:
When `J = 0` and `M ≥ 0`, `irreducibleMassSq M 0 = M^2`, `irreducibleMass M 0 = M`,
and `M - irreducibleMass M 0 = 0` (zero rotational energy available for Penrose extraction). -/
theorem christodoulou_schwarzschild_limit_identities
    (M : ℝ) (hM : 0 ≤ M) :
    irreducibleMassSq M 0 = M ^ 2 ∧
    irreducibleMass M 0 = M ∧
    M - irreducibleMass M 0 = 0 :=
  ⟨irreducibleMassSq_J_zero M,
   irreducibleMass_J_zero_of_M_nonneg hM,
   Penrose_zero_for_schwarzschild hM⟩

/-- **Extremal Kerr Limit (`J^2 = M^4`) of Christodoulou Irreducible Mass**:
When `kerrExtremal M J` and `M ≥ 0`, `irreducibleMassSq M J = M^2 / 2`,
`irreducibleMass M J = M / √2`, and `M - irreducibleMass M J = M * (1 - 1 / √2)`. -/
theorem christodoulou_extremal_limit_identities
    (M J : ℝ) (hext : kerrExtremal M J) (hM : 0 ≤ M) :
    irreducibleMassSq M J = M ^ 2 / 2 ∧
    irreducibleMass M J = M / Real.sqrt 2 ∧
    M - irreducibleMass M J = M * (1 - 1 / Real.sqrt 2) :=
  ⟨irreducibleMassSq_extremal hext,
   irreducibleMass_extremal_of_M_nonneg hext hM,
   Penrose_extraction_extremal hext hM⟩

/-- **Kerr Horizon Area Formulas & Non-Negativity**:
`kerrHorizonArea M J = 16 * π * irreducibleMassSq M J = 8 * π * (M^2 + √(M^4 - J^2)) ≥ 0`. -/
theorem kerr_horizon_area_formulas_and_nonneg (M J : ℝ) :
    kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J ∧
    kerrHorizonArea M J = 8 * Real.pi * (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) ∧
    0 ≤ kerrHorizonArea M J :=
  ⟨kerrHorizonArea_eq_irreducible M J,
   kerrHorizonArea_expanded M J,
   kerrHorizonArea_nonneg M J⟩

/-- **Kerr Horizon Area in Schwarzschild (`J = 0`) and Extremal (`J^2 = M^4`) Limits**:
`kerrHorizonArea M 0 = horizonArea M = 16 * π * M^2`, while for `kerrExtremal M J`,
`kerrHorizonArea M J = 8 * π * M^2 = horizonArea M / 2`. -/
theorem kerr_horizon_area_schwarzschild_and_extremal_limits
    (M J : ℝ) (hext : kerrExtremal M J) :
    kerrHorizonArea M 0 = horizonArea M ∧
    kerrHorizonArea M J = 8 * Real.pi * M ^ 2 ∧
    kerrHorizonArea M J = horizonArea M / 2 := by
  refine ⟨kerrHorizonArea_J_zero M, ?_, ?_⟩
  · rw [kerrHorizonArea_eq_irreducible, irreducibleMassSq_extremal hext]
    ring
  · rw [kerrHorizonArea_eq_irreducible, irreducibleMassSq_extremal hext]
    unfold horizonArea schwarzschildRadius
    ring

/-- **Christodoulou-Ruffini Mass-Energy Decomposition**:
For sub-extremal Kerr with `M ≠ 0`,
`M^2 = irreducibleMassSq M J + J^2 / (4 * irreducibleMassSq M J)`. -/
theorem christodoulou_mass_energy_rotational_decomposition
    (M J : ℝ) (hsub : kerrSubextremal M J) (hM : M ≠ 0) :
    0 < irreducibleMassSq M J ∧
    M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) :=
  ⟨irreducibleMassSq_pos_of_M_ne_zero hM,
   mass_energy_decomposition hsub hM⟩

/-- **Penrose Process Rotational Energy Extraction Bounds (Squared & Linear)**:
For `M ≥ 0` and any `J : ℝ`, `M^2 - irreducibleMassSq M J ≤ M^2 / 2` and
`0 ≤ M - irreducibleMass M J ≤ M * (1 - 1 / √2)`. -/
theorem penrose_process_extraction_squared_and_linear_bounds
    (M J : ℝ) (hM : 0 ≤ M) :
    M ^ 2 - irreducibleMassSq M J ≤ M ^ 2 / 2 ∧
    0 ≤ M - irreducibleMass M J ∧
    M - irreducibleMass M J ≤ M * (1 - 1 / Real.sqrt 2) :=
  ⟨Penrose_extraction_bound_sq,
   Penrose_extraction_nonneg hM J,
   Penrose_extraction_bound hM J⟩

/-- **Penrose Process Extremal Saturation & Schwarzschild Vanishing**:
Penrose extractable energy vanishes at `J = 0` (`M - irreducibleMass M 0 = 0`) and
saturates the universal bound `M * (1 - 1 / √2)` at `kerrExtremal M J`. -/
theorem penrose_process_extremal_saturation_and_schwarzschild_zero
    (M J : ℝ) (hext : kerrExtremal M J) (hM : 0 ≤ M) :
    M - irreducibleMass M 0 = 0 ∧
    M - irreducibleMass M J = M * (1 - 1 / Real.sqrt 2) :=
  ⟨Penrose_zero_for_schwarzschild hM,
   Penrose_extraction_extremal hext hM⟩

/-- **Hawking Area Theorem Implication for Penrose Energy Extraction**:
If `irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂` with `0 ≤ M₁` and `0 ≤ M₂`, then
`M₁ - M₂ ≤ M₁ - irreducibleMass M₁ J₁ ≤ M₁ * (1 - 1 / √2)`. -/
theorem hawking_area_theorem_implies_penrose_extraction_bound
    (M₁ J₁ M₂ J₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h_area : irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂) :
    M₁ - M₂ ≤ M₁ - irreducibleMass M₁ J₁ ∧
    M₁ - M₂ ≤ M₁ * (1 - 1 / Real.sqrt 2) :=
  ⟨area_theorem_extraction_bound h_area hM₂,
   universal_Penrose_bound hM₁ h_area hM₂⟩

/-- Complete Christodoulou irreducible-mass capstone from `LayerB.ChristodoulouIrreducibleMass`. -/
theorem christodoulou_irreducible_mass_master_capstone :
    (∀ M J : ℝ,
        irreducibleMassSq M J = (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) / 2) ∧
    (∀ M J : ℝ, kerrSubextremal M J → irreducibleMassSq M J ≤ M ^ 2) ∧
    (∀ M J : ℝ, M ^ 2 / 2 ≤ irreducibleMassSq M J) ∧
    (∀ M : ℝ, irreducibleMassSq M 0 = M ^ 2) ∧
    (∀ M : ℝ, 0 ≤ M → irreducibleMass M 0 = M) ∧
    (∀ M J : ℝ, kerrExtremal M J → irreducibleMassSq M J = M ^ 2 / 2) ∧
    (∀ M J : ℝ, kerrExtremal M J → 0 ≤ M →
        irreducibleMass M J = M / Real.sqrt 2) ∧
    (∀ M J : ℝ, kerrSubextremal M J → 0 ≤ M →
        0 ≤ M - irreducibleMass M J) ∧
    (∀ M J : ℝ, kerrSubextremal M J → 0 ≤ M →
        M - irreducibleMass M J ≤ M * (1 - 1 / Real.sqrt 2)) ∧
    (∀ M J : ℝ,
        kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J) ∧
    (∀ M : ℝ, kerrHorizonArea M 0 = horizonArea M) ∧
    (∀ M J : ℝ, kerrSubextremal M J → M ≠ 0 →
        M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J)) ∧
    (∀ M₁ J₁ M₂ J₂ : ℝ,
        kerrSubextremal M₁ J₁ → 0 ≤ M₁ →
        irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂ →
        kerrSubextremal M₂ J₂ → 0 ≤ M₂ →
        M₁ - M₂ ≤ M₁ * (1 - 1 / Real.sqrt 2)) :=
  christodoulou_capstone

/-! ### 2. Kerr Bekenstein-Hawking Entropy & Second Law Equivalence -/

/-- **Kerr Bekenstein-Hawking Entropy**:
Quarter of the Kerr horizon area, `S_Kerr(M, J) = A_Kerr(M, J) / 4 = 4 * π * M_irr^2`. -/
def kerrBekensteinHawkingEntropy (M J : ℝ) : ℝ :=
  kerrHorizonArea M J / 4

/-- Explicit formula `kerrBekensteinHawkingEntropy M J = 4 * π * irreducibleMassSq M J`
and non-negativity for all `(M, J)`. -/
theorem kerrBekensteinHawkingEntropy_formula_and_nonneg (M J : ℝ) :
    kerrBekensteinHawkingEntropy M J = 4 * Real.pi * irreducibleMassSq M J ∧
    kerrBekensteinHawkingEntropy M J =
      2 * Real.pi * (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) ∧
    0 ≤ kerrBekensteinHawkingEntropy M J := by
  refine ⟨?_, ?_, ?_⟩
  · unfold kerrBekensteinHawkingEntropy kerrHorizonArea
    ring
  · unfold kerrBekensteinHawkingEntropy
    rw [kerrHorizonArea_expanded]
    ring
  · unfold kerrBekensteinHawkingEntropy
    exact div_nonneg (kerrHorizonArea_nonneg M J) (by norm_num)

/-- **Kerr Bekenstein-Hawking Entropy in Schwarzschild (`J = 0`) and Extremal (`J^2 = M^4`) Limits**:
At `J = 0`, `kerrBekensteinHawkingEntropy M 0 = bekensteinHawkingEntropy M = 4 * π * M^2`;
at `kerrExtremal M J`, `kerrBekensteinHawkingEntropy M J = 2 * π * M^2 = bekensteinHawkingEntropy M / 2`. -/
theorem kerrBekensteinHawkingEntropy_schwarzschild_and_extremal
    (M J : ℝ) (hext : kerrExtremal M J) :
    kerrBekensteinHawkingEntropy M 0 = bekensteinHawkingEntropy M ∧
    kerrBekensteinHawkingEntropy M J = 2 * Real.pi * M ^ 2 ∧
    kerrBekensteinHawkingEntropy M J = bekensteinHawkingEntropy M / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold kerrBekensteinHawkingEntropy bekensteinHawkingEntropy
    rw [kerrHorizonArea_J_zero]
  · rw [(kerrBekensteinHawkingEntropy_formula_and_nonneg M J).1,
        irreducibleMassSq_extremal hext]
    ring
  · rw [(kerrBekensteinHawkingEntropy_formula_and_nonneg M J).1,
        irreducibleMassSq_extremal hext]
    unfold bekensteinHawkingEntropy horizonArea schwarzschildRadius
    ring

/-- **Two-Sided Schwarzschild Envelope for Kerr Bekenstein-Hawking Entropy**:
For every `(M, J)`,
`bekensteinHawkingEntropy M / 2 ≤ kerrBekensteinHawkingEntropy M J ≤ bekensteinHawkingEntropy M`. -/
theorem kerrBekensteinHawkingEntropy_two_sided_schwarzschild_bounds (M J : ℝ) :
    bekensteinHawkingEntropy M / 2 ≤ kerrBekensteinHawkingEntropy M J ∧
    kerrBekensteinHawkingEntropy M J ≤ bekensteinHawkingEntropy M := by
  have hlow := irreducibleMassSq_ge_half_M_sq M J
  have hhigh := irreducibleMassSq_le_M_sq M J
  have h4pi : (0 : ℝ) ≤ 4 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hS : bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 := by
    unfold bekensteinHawkingEntropy horizonArea schwarzschildRadius
    ring
  rw [(kerrBekensteinHawkingEntropy_formula_and_nonneg M J).1, hS]
  refine ⟨?_, mul_le_mul_of_nonneg_left hhigh h4pi⟩
  have h1 := mul_le_mul_of_nonneg_left hlow h4pi
  linarith

/-- **Second Law Equivalence (`δM_irr^2 ≥ 0 ↔ δA_Kerr ≥ 0 ↔ δS_Kerr ≥ 0`)**:
Non-decreasing squared irreducible mass is equivalent to non-decreasing Kerr horizon
area and equivalent to non-decreasing Kerr Bekenstein-Hawking entropy. -/
theorem kerr_area_nondecreasing_iff_entropy_nondecreasing (M₁ J₁ M₂ J₂ : ℝ) :
    (irreducibleMassSq M₁ J₁ ≤ irreducibleMassSq M₂ J₂ ↔
      kerrHorizonArea M₁ J₁ ≤ kerrHorizonArea M₂ J₂) ∧
    (kerrHorizonArea M₁ J₁ ≤ kerrHorizonArea M₂ J₂ ↔
      kerrBekensteinHawkingEntropy M₁ J₁ ≤ kerrBekensteinHawkingEntropy M₂ J₂) := by
  have h16pi : (0 : ℝ) < 16 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨?_, ?_⟩
  · unfold kerrHorizonArea
    exact ⟨fun h => mul_le_mul_of_nonneg_left h h16pi.le,
           fun h => le_of_mul_le_mul_left h h16pi⟩
  · unfold kerrBekensteinHawkingEntropy
    exact ⟨fun h => div_le_div_of_nonneg_right h (by norm_num),
           fun h => by linarith⟩

/-! ### 3. Universal Bekenstein Bound (`LayerB.BekensteinBound`) & Holographic Forms -/

/-- Positivity, monotonicity, and linear scaling of `bekensteinBound R E = 2 * π * R * E`. -/
theorem bekenstein_bound_positivity_monotonicity_and_scaling
    (R R₁ R₂ E E₁ E₂ c : ℝ) (hR : 0 < R) (hE : 0 < E)
    (hR_le : R₁ ≤ R₂) (hE_le : E₁ ≤ E₂) :
    0 ≤ bekensteinBound R E ∧
    0 < bekensteinBound R E ∧
    bekensteinBound R₁ E ≤ bekensteinBound R₂ E ∧
    bekensteinBound R E₁ ≤ bekensteinBound R E₂ ∧
    bekensteinBound (c * R) E = c * bekensteinBound R E ∧
    bekensteinBound R (c * E) = c * bekensteinBound R E :=
  ⟨bekensteinBound_nonneg hR.le hE.le,
   bekensteinBound_pos hR hE,
   bekensteinBound_mono_R hE.le hR_le,
   bekensteinBound_mono_E hR.le hE_le,
   bekensteinBound_smul_R c R E,
   bekensteinBound_smul_E c R E⟩

/-- Vacuum compliance and monotonicity of `IsBekensteinCompliant S R E`. -/
theorem bekenstein_compliance_zero_and_monotonicity
    (S₁ S₂ R₁ R₂ E₁ E₂ : ℝ) (hR₁ : 0 ≤ R₁) (hE₁ : 0 ≤ E₁)
    (hS : S₁ ≤ S₂) (hR : R₁ ≤ R₂) (hE : E₁ ≤ E₂)
    (hcomp : IsBekensteinCompliant S₂ R₁ E₁) :
    IsBekensteinCompliant 0 R₁ E₁ ∧
    IsBekensteinCompliant S₁ R₁ E₁ ∧
    IsBekensteinCompliant S₂ R₂ E₁ ∧
    IsBekensteinCompliant S₂ R₁ E₂ :=
  ⟨zero_entropy_compliant hR₁ hE₁,
   hcomp.mono hS,
   hcomp.mono_R hE₁ hR,
   hcomp.mono_E hR₁ hE⟩

/-- **Schwarzschild Saturation of the Bekenstein Bound**:
At `R = schwarzschildRadius M = 2 * M` and `E = M`, `bekensteinBound (2 * M) M = 4 * π * M^2 = bekensteinHawkingEntropy M`
and `IsBekensteinCompliant (bekensteinHawkingEntropy M) (schwarzschildRadius M) M`. -/
theorem schwarzschild_saturates_bekenstein_bound_identities (M : ℝ) :
    bekensteinBound (2 * M) M = bekensteinHawkingEntropy M ∧
    bekensteinBound (schwarzschildRadius M) M = bekensteinHawkingEntropy M ∧
    bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2 ∧
    IsBekensteinCompliant (bekensteinHawkingEntropy M) (schwarzschildRadius M) M ∧
    bekensteinHawkingEntropy M = bekensteinBound (schwarzschildRadius M) M :=
  ⟨schwarzschild_saturates_bound M,
   schwarzschild_saturates_bound' M,
   schwarzschild_bound_eq M,
   BH_is_bekenstein M,
   BH_saturates_bekenstein M⟩

/-- Any entropy `S > 4 * π * M^2` at `(R = 2 * M, E = M)` violates `IsBekensteinCompliant`. -/
theorem super_bekenstein_entropy_violates_compliance
    (S M : ℝ) (hS : 4 * Real.pi * M ^ 2 < S) :
    ¬ IsBekensteinCompliant S (2 * M) M :=
  superBHEntropy_collapses hS

/-- Equivalence of Bekenstein saturation/compliance at `(2 * M, M)` with `bekensteinHawkingEntropy M`. -/
theorem bekenstein_saturation_and_compliance_iff_schwarzschild_entropy (S M : ℝ) :
    (S = bekensteinBound (2 * M) M ↔ S = bekensteinHawkingEntropy M) ∧
    (IsBekensteinCompliant S (2 * M) M ↔ S ≤ bekensteinHawkingEntropy M) :=
  ⟨saturation_iff_BH S M, compliant_at_BH_iff S M⟩

/-- **Holographic Form of the Bekenstein Bound (`(A / 4) * (E / M)`)**:
For `M ≠ 0`, `bekensteinBound (2 * M) E = horizonArea M * E / (4 * M) = (horizonArea M / 4) * (E / M)`,
reducing at `E = M` to `horizonArea M / 4`. -/
theorem bekenstein_holographic_form_and_quarter_area_reduction
    (M E : ℝ) (hM : M ≠ 0) :
    bekensteinBound (2 * M) E = horizonArea M * E / (4 * M) ∧
    bekensteinBound (2 * M) E = (horizonArea M / 4) * (E / M) ∧
    bekensteinBound (2 * M) M = horizonArea M / 4 :=
  ⟨holographic_form hM,
   holographic_form_factored hM,
   holographic_at_E_eq_M hM⟩

/-- **Bit-Information Form of the Bekenstein Bound**:
`0 < Real.log 2`, `Real.log 2 ≠ 0`, `IsBekensteinCompliant S R E ↔ S / log 2 ≤ bekensteinBoundBits R E`,
and `bekensteinBoundBits (2 * M) M = bekensteinHawkingEntropy M / log 2`. -/
theorem bekenstein_bits_form_and_log_two_positivity (S R E M : ℝ) :
    0 < Real.log 2 ∧
    Real.log 2 ≠ 0 ∧
    (IsBekensteinCompliant S R E ↔ S / Real.log 2 ≤ bekensteinBoundBits R E) ∧
    bekensteinBoundBits (2 * M) M = bekensteinHawkingEntropy M / Real.log 2 :=
  ⟨log_two_pos, log_two_ne_zero, bits_form S R E, BH_bits_at_saturation M⟩

/-- **Holographic Principle Quarter-Area Equivalence**:
At `(R = 2 * M, E = M)`, `IsBekensteinCompliant S (2 * M) M ↔ S ≤ horizonArea M / 4`. -/
theorem bekenstein_holographic_principle_quarter_area_iff (S M : ℝ) :
    (IsBekensteinCompliant S (2 * M) M → S ≤ horizonArea M / 4) ∧
    (IsBekensteinCompliant S (2 * M) M ↔ S ≤ horizonArea M / 4) :=
  ⟨holographic_principle S M, compliant_iff_quarter_area S M⟩

/-- Complete Layer-B Bekenstein-bound master capstone. -/
theorem bekenstein_bound_layerB_master_capstone :
    (∀ R E : ℝ, bekensteinBound R E = 2 * Real.pi * R * E) ∧
    (∀ R E : ℝ, 0 ≤ R → 0 ≤ E → 0 ≤ bekensteinBound R E) ∧
    (∀ R E : ℝ, 0 < R → 0 < E → 0 < bekensteinBound R E) ∧
    (∀ R₁ R₂ E : ℝ, 0 ≤ E → R₁ ≤ R₂ →
        bekensteinBound R₁ E ≤ bekensteinBound R₂ E) ∧
    (∀ R E₁ E₂ : ℝ, 0 ≤ R → E₁ ≤ E₂ →
        bekensteinBound R E₁ ≤ bekensteinBound R E₂) ∧
    (∀ M : ℝ, bekensteinBound (2 * M) M = bekensteinHawkingEntropy M) ∧
    (∀ M : ℝ, bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2) ∧
    (∀ M : ℝ, IsBekensteinCompliant (bekensteinHawkingEntropy M)
                                       (schwarzschildRadius M) M) ∧
    (∀ S M : ℝ, 4 * Real.pi * M ^ 2 < S →
        ¬ IsBekensteinCompliant S (2 * M) M) ∧
    (∀ M E : ℝ, M ≠ 0 →
        bekensteinBound (2 * M) E = horizonArea M * E / (4 * M)) ∧
    (∀ S M : ℝ, IsBekensteinCompliant S (2 * M) M
                  → S ≤ horizonArea M / 4) ∧
    (∀ S R E : ℝ,
          IsBekensteinCompliant S R E
            ↔ S / Real.log 2 ≤ bekensteinBoundBits R E) :=
  bekenstein_bound_capstone

/-! ### 4. Cross-Module Bridges: Kerr Irreducible Mass, Bekenstein Bound, Kretschmann & Hawking Thermodynamics -/

/-- **Every Rotating Kerr Black Hole Satisfies the Schwarzschild Bekenstein Bound**:
Because rotation reduces horizon area (`M_irr^2 ≤ M^2`) at fixed total energy `M`,
every Kerr black hole `(M, J)` satisfies
`IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M` and
`kerrBekensteinHawkingEntropy M J ≤ horizonArea M / 4`. -/
theorem kerr_entropy_satisfies_schwarzschild_bekenstein_bound (M J : ℝ) :
    IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M ∧
    kerrBekensteinHawkingEntropy M J ≤ bekensteinBound (2 * M) M ∧
    kerrBekensteinHawkingEntropy M J ≤ horizonArea M / 4 := by
  have hbnd := (kerrBekensteinHawkingEntropy_two_sided_schwarzschild_bounds M J).2
  have hcomp : IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M :=
    (compliant_at_BH_iff (kerrBekensteinHawkingEntropy M J) M).mpr hbnd
  exact ⟨hcomp, hcomp, holographic_principle (kerrBekensteinHawkingEntropy M J) M hcomp⟩

/-- **Schwarzschild (`J = 0`) Kerr Limit ↔ Horizon Kretschmann Curvature Invariants**:
At `J = 0` for `M ≠ 0`, `schwarzschildKretschmann M (schwarzschildRadius M) = 3 / (4 * M^4)`,
`schwarzschildKretschmann M (schwarzschildRadius M) * (kerrHorizonArea M 0)^2 = 192 * π^2`,
`schwarzschildKretschmann M (schwarzschildRadius M) * (kerrBekensteinHawkingEntropy M 0)^2 = 12 * π^2`,
and `schwarzschildKretschmann M (schwarzschildRadius M) * (bekensteinBound (2 * M) M)^2 = 12 * π^2`. -/
theorem kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants
    (M : ℝ) (hM : M ≠ 0) :
    schwarzschildKretschmann M (schwarzschildRadius M) = 3 / (4 * M ^ 4) ∧
    schwarzschildKretschmann M (schwarzschildRadius M) * (kerrHorizonArea M 0) ^ 2 =
      192 * Real.pi ^ 2 ∧
    schwarzschildKretschmann M (schwarzschildRadius M) *
      (kerrBekensteinHawkingEntropy M 0) ^ 2 = 12 * Real.pi ^ 2 ∧
    schwarzschildKretschmann M (schwarzschildRadius M) *
      (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2 := by
  have hA := kerrHorizonArea_J_zero M
  have hS : kerrBekensteinHawkingEntropy M 0 = bekensteinHawkingEntropy M := by
    unfold kerrBekensteinHawkingEntropy bekensteinHawkingEntropy
    rw [hA]
  have hB := schwarzschild_saturates_bound M
  rw [hA, hS, hB]
  exact ⟨schwarzschildKretschmann_at_horizon M hM,
    schwarzschildKretschmann_horizon_times_area_sq M hM,
    schwarzschildKretschmann_horizon_times_entropy_sq M hM,
    schwarzschildKretschmann_horizon_times_entropy_sq M hM⟩

/-- **Schwarzschild (`J = 0`) Kerr Limit ↔ Hawking Temperature, Smarr Formula & Cubic Evaporation**:
At `J = 0` for `M > 0`, `2 * kerrBekensteinHawkingEntropy M 0 * hawkingTemperature M = M`,
`2 * bekensteinBound (2 * M) M * hawkingTemperature M = M`,
`hawkingTemperature M = surfaceGravity M / (2 * π) > 0`, and
`evaporationLifetime (k_scale * M) = k_scale^3 * evaporationLifetime M`. -/
theorem kerr_schwarzschild_limit_hawking_smarr_and_evaporation
    (M r θ ρ V k_scale : ℝ) (hM : 0 < M) (hr : r ≠ 0)
    (hM_lt : ∀ r₀ : ℝ, 0 < r₀ → r₀ > 2 * M)
    (hρ : 0 < ρ) (hV : 0 < V) :
    0 < hawkingTemperature M ∧
    hawkingTemperature M = surfaceGravity M / (2 * Real.pi) ∧
    2 * kerrBekensteinHawkingEntropy M 0 * hawkingTemperature M = M ∧
    2 * bekensteinBound (2 * M) M * hawkingTemperature M = M ∧
    evaporationLifetime (k_scale * M) = k_scale ^ 3 * evaporationLifetime M := by
  have hm := schwarzschild_birkhoff_hawking_thermodynamics_4D_master_bridge
    M r θ ρ V k_scale hM hr hM_lt hρ hV
  have hS : kerrBekensteinHawkingEntropy M 0 = bekensteinHawkingEntropy M := by
    unfold kerrBekensteinHawkingEntropy bekensteinHawkingEntropy
    rw [kerrHorizonArea_J_zero]
  have hB := schwarzschild_saturates_bound M
  rw [hS, hB]
  exact ⟨hm.2.2.2.1.2.2.1, hm.2.2.2.1.2.2.2.1,
    hm.2.2.2.1.2.2.2.2.1, hm.2.2.2.1.2.2.2.2.1, hm.2.2.2.1.2.2.2.2.2⟩

/-- **Sorkin Causal-Set De Sitter Horizon Entropy & Bekenstein Quarter-Area Bridge**:
Connects `bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))` (`16 * S_dS^2 = ρ * V`)
with the Schwarzschild Bekenstein saturation `bekensteinBound (2 * M) M = horizonArea M / 4`. -/
theorem kerr_sorkin_deSitter_bekenstein_entropy_bridge
    (M r θ ρ V k_scale : ℝ) (hM : 0 < M) (hr : r ≠ 0)
    (hM_lt : ∀ r₀ : ℝ, 0 < r₀ → r₀ > 2 * M)
    (hρ : 0 < ρ) (hV : 0 < V) :
    bekensteinBound (2 * M) M = horizonArea M / 4 ∧
    kerrBekensteinHawkingEntropy M 0 = horizonArea M / 4 ∧
    0 < bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V)) ∧
    16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V := by
  have hm := schwarzschild_birkhoff_hawking_thermodynamics_4D_master_bridge
    M r θ ρ V k_scale hM hr hM_lt hρ hV
  have hS : kerrBekensteinHawkingEntropy M 0 = horizonArea M / 4 := by
    unfold kerrBekensteinHawkingEntropy
    rw [kerrHorizonArea_J_zero]
  exact ⟨holographic_at_E_eq_M (ne_of_gt hM), hS,
    hm.2.2.2.2.1, hm.2.2.2.2.2⟩

/-- **Schwarzschild Interior Trapped Surface (`0 < r_int < 2M`) & Bekenstein Horizon Saturation Bridge**:
Every sphere `0 < r_int < schwarzschildRadius M` inside the Bekenstein-saturating
Schwarzschild horizon `schwarzschildRadius M = 2 * M` is a `TrappedSurface` with
strictly positive conjugate-point focusing times `2 * r_int^2 / (2M ∓ r_int)`. -/
theorem schwarzschild_trapped_surface_and_bekenstein_saturation_bridge
    (M r_int : ℝ) (hM : 0 < M) (hr_pos : 0 < r_int)
    (hr_lt : r_int < schwarzschildRadius M) :
    bekensteinBound (schwarzschildRadius M) M = bekensteinHawkingEntropy M ∧
    IsBekensteinCompliant (bekensteinHawkingEntropy M) (schwarzschildRadius M) M ∧
    (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus < 0 ∧
    (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_minus < 0 ∧
    0 < conjugatePointTime
      (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus ∧
    0 < conjugatePointTime
      (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_minus := by
  have htrap := schwarzschild_interior_trapped_surface_conjugate_times
    M r_int hM hr_pos hr_lt
  exact ⟨schwarzschild_saturates_bound' M,
    BH_is_bekenstein M,
    (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).trapped.1,
    (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).trapped.2,
    htrap.1, htrap.2.1⟩

/-- **Malament 4D Conformal Uniqueness, Weyl Invariance & Christodoulou Horizon Area Bridge**:
Combines `stage3_closed_3plus1`, `weylTensor4D (conformalPartMetricDerivs4D md) = 0`,
and `kerrHorizonArea M J = 16 * π * irreducibleMassSq M J`. -/
theorem malament_4D_conformal_weyl_and_christodoulou_area_bridge
    (md : MetricDerivs 4) (a b c d : Fin 4) (M J : ℝ) :
    (∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0) →
      ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
    weylTensor4D md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d ∧
    kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J ∧
    IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M :=
  ⟨stage3_closed_3plus1,
   weylTensor4D_conformalPart_eq_zero md a b c d,
   weylTensor4D_eq_tracelessPart md a b c d,
   kerrHorizonArea_eq_irreducible M J,
   (kerr_entropy_satisfies_schwarzschild_bekenstein_bound M J).1⟩

/-- **Variational Einstein-Ostrogradsky Stability & Black Hole Mechanics Bridge**:
Combines Ostrogradsky higher-derivative exclusion, 4D variational Einstein-Sorkin-Yang-Mills
stationarity, Christodoulou mass-energy decomposition, and the universal Penrose bound. -/
theorem variational_ostrogradsky_and_black_hole_mechanics_bridge
    (md : MetricDerivs 4) (ρ V κ : ℝ)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (M J M₂ J₂ : ℝ) (hsub : kerrSubextremal M J) (hM_pos : 0 < M) (hM₂ : 0 ≤ M₂)
    (h_area : irreducibleMass M J ≤ irreducibleMass M₂ J₂) :
    (∀ v_ost g_ost : ℝ, v_ost ≠ 0 →
      ¬∃ M_bnd : ℝ, ∀ p₁ : ℝ, M_bnd ≤ ostrogradsky_hamiltonian v_ost g_ost p₁) ∧
    (SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc₃ conn₃ ↔
      (∀ δg : Fin 4 → Fin 4 → ℝ,
        ∑ μ : Fin 4, ∑ ν : Fin 4,
          einsteinLovelockYangMillsResidual4D md (sorkinLambda ρ V) κ sc₃ conn₃ μ ν *
            δg μ ν = 0)) ∧
    M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) ∧
    M - M₂ ≤ M * (1 - 1 / Real.sqrt 2) ∧
    IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M :=
  ⟨ostrogradsky_stability_to_einstein_bridge,
   einsteinSorkinYangMills4D_iff_variational_stationarity md ρ V κ sc₃ conn₃,
   mass_energy_decomposition hsub (ne_of_gt hM_pos),
   universal_Penrose_bound hM_pos.le h_area hM₂,
   (kerr_entropy_satisfies_schwarzschild_bekenstein_bound M J).1⟩

/-- **Curved 4D Christodoulou Irreducible Mass, Bekenstein Bound & Black Hole Mechanics Master Synthesis**:
Unites:
1. Christodoulou-Ruffini irreducible mass formula (`M_irr^2 = (M^2 + √(M^4 - J^2)) / 2`),
   two-sided bounds (`M^2 / 2 ≤ M_irr^2 ≤ M^2`), Kerr horizon area (`A_Kerr = 16 * π * M_irr^2`),
   mass-energy decomposition (`M^2 = M_irr^2 + J^2 / (4 * M_irr^2)`), and Penrose extraction
   ceiling (`M₁ - M₂ ≤ M₁ * (1 - 1 / √2)`);
2. Universal Bekenstein bound (`bekensteinBound R E = 2 * π * R * E`), Schwarzschild
   saturation (`bekensteinBound (2 * M) M = bekensteinHawkingEntropy M = 4 * π * M^2`),
   Kerr Bekenstein compliance (`IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M`),
   holographic quarter-area identity (`IsBekensteinCompliant S (2 * M) M ↔ S ≤ horizonArea M / 4`),
   and bit-information equivalence (`IsBekensteinCompliant S R E ↔ S / log 2 ≤ bekensteinBoundBits R E`);
3. Hawking-Penrose focusing (`0 < conjugatePointTime θ₀ < -3 / θ₀`), Schwarzschild interior
   trapped surface (`0 < r_int < 2M`), exact Schwarzschild vacuum + Birkhoff uniqueness,
   horizon Kretschmann invariant (`K(2M) * (bekensteinBound (2M) M)^2 = 12 * π^2`),
   Smarr's law (`2 * bekensteinBound (2M) M * T_H = M`), Sorkin de Sitter entropy
   (`16 * S_dS^2 = ρ * V`), and Malament `3+1` conformal uniqueness. -/
theorem curved_4D_christodoulou_bekenstein_black_hole_mechanics_master_synthesis
    (md : MetricDerivs 4) (a b c d : Fin 4)
    (ρ V κ : ℝ) (hρ : 0 < ρ) (hV : 0 < V)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (θ₀ : ℝ) (hθ₀ : θ₀ < 0)
    (M J M₂ J₂ r_ext r_int θ_ang k_scale S R E : ℝ)
    (hsub : kerrSubextremal M J) (hM : 0 < M) (hM₂ : 0 ≤ M₂)
    (h_area : irreducibleMass M J ≤ irreducibleMass M₂ J₂)
    (hr_ext : r_ext ≠ 0) (hr_int_pos : 0 < r_int)
    (hr_int_lt : r_int < schwarzschildRadius M)
    (hM_lt : ∀ r₀ : ℝ, 0 < r₀ → r₀ > 2 * M) :
    -- (1) Christodoulou irreducible mass, Kerr area, mass decomposition & Penrose bound
    (M ^ 2 / 2 ≤ irreducibleMassSq M J ∧
      irreducibleMassSq M J ≤ M ^ 2 ∧
      kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J ∧
      kerrHorizonArea M 0 = horizonArea M ∧
      M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) ∧
      0 ≤ M - irreducibleMass M J ∧
      M - irreducibleMass M J ≤ M * (1 - 1 / Real.sqrt 2) ∧
      M - M₂ ≤ M * (1 - 1 / Real.sqrt 2)) ∧
    -- (2) Bekenstein bound, Schwarzschild saturation, Kerr compliance, holographic & bit forms
    (bekensteinBound (2 * M) M = bekensteinHawkingEntropy M ∧
      IsBekensteinCompliant (bekensteinHawkingEntropy M) (schwarzschildRadius M) M ∧
      IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M ∧
      (IsBekensteinCompliant S (2 * M) M ↔ S ≤ horizonArea M / 4) ∧
      (IsBekensteinCompliant S R E ↔ S / Real.log 2 ≤ bekensteinBoundBits R E)) ∧
    -- (3) Hawking-Penrose trapped surface, Kretschmann, Smarr, Sorkin de Sitter & Malament 3+1
    (0 < conjugatePointTime θ₀ ∧
      conjugatePointTime θ₀ < -3 / θ₀ ∧
      Penrose_Singularity_Target ∧
      (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_plus < 0 ∧
      (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_minus < 0 ∧
      (R_tt M r_ext = 0 ∧ R_rr M r_ext = 0 ∧
        R_thetatheta M r_ext = 0 ∧ R_phiphi M r_ext θ_ang = 0) ∧
      IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) ∧
      schwarzschildKretschmann M (schwarzschildRadius M) *
        (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2 ∧
      2 * bekensteinBound (2 * M) M * hawkingTemperature M = M ∧
      evaporationLifetime (k_scale * M) = k_scale ^ 3 * evaporationLifetime M ∧
      16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V ∧
      weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0) := by
  have hhp := curved_4D_hawking_penrose_malament_master_synthesis
    md a b c d ρ V κ sc₃ conn₃ θ₀ hθ₀ M r_ext r_int θ_ang
    hM hr_ext hr_int_pos hr_int_lt hM_lt
  have hsmarr := kerr_schwarzschild_limit_hawking_smarr_and_evaporation
    M r_ext θ_ang ρ V k_scale hM hr_ext hM_lt hρ hV
  have hdS := kerr_sorkin_deSitter_bekenstein_entropy_bridge
    M r_ext θ_ang ρ V k_scale hM hr_ext hM_lt hρ hV
  have hK := kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants
    M (ne_of_gt hM)
  exact ⟨⟨irreducibleMassSq_ge_half_M_sq M J,
      irreducibleMassSq_le_M_sq M J,
      kerrHorizonArea_eq_irreducible M J,
      kerrHorizonArea_J_zero M,
      mass_energy_decomposition hsub (ne_of_gt hM),
      Penrose_extraction_nonneg hM.le J,
      Penrose_extraction_bound hM.le J,
      universal_Penrose_bound hM.le h_area hM₂⟩,
    ⟨schwarzschild_saturates_bound M,
      BH_is_bekenstein M,
      (kerr_entropy_satisfies_schwarzschild_bekenstein_bound M J).1,
      compliant_iff_quarter_area S M,
      bits_form S R E⟩,
    ⟨hhp.2.1.2.1, hhp.2.1.2.2.2.1, hhp.2.1.2.2.2.2,
      hhp.2.2.1.1, hhp.2.2.1.2.1,
      hhp.2.2.1.2.2.2.2.1, hhp.2.2.1.2.2.2.2.2.1,
      hK.2.2.2, hsmarr.2.2.2.1, hsmarr.2.2.2.2,
      hdS.2.2.2, hhp.2.2.2.2.1⟩⟩

end

#print axioms kerr_subextremal_and_discriminant_properties
#print axioms christodoulou_irreducibleMassSq_nonneg_and_bounds
#print axioms christodoulou_irreducibleMass_nonneg_and_bounds
#print axioms christodoulou_schwarzschild_limit_identities
#print axioms christodoulou_extremal_limit_identities
#print axioms kerr_horizon_area_formulas_and_nonneg
#print axioms kerr_horizon_area_schwarzschild_and_extremal_limits
#print axioms christodoulou_mass_energy_rotational_decomposition
#print axioms penrose_process_extraction_squared_and_linear_bounds
#print axioms penrose_process_extremal_saturation_and_schwarzschild_zero
#print axioms hawking_area_theorem_implies_penrose_extraction_bound
#print axioms christodoulou_irreducible_mass_master_capstone
#print axioms kerrBekensteinHawkingEntropy_formula_and_nonneg
#print axioms kerrBekensteinHawkingEntropy_schwarzschild_and_extremal
#print axioms kerrBekensteinHawkingEntropy_two_sided_schwarzschild_bounds
#print axioms kerr_area_nondecreasing_iff_entropy_nondecreasing
#print axioms bekenstein_bound_positivity_monotonicity_and_scaling
#print axioms bekenstein_compliance_zero_and_monotonicity
#print axioms schwarzschild_saturates_bekenstein_bound_identities
#print axioms super_bekenstein_entropy_violates_compliance
#print axioms bekenstein_saturation_and_compliance_iff_schwarzschild_entropy
#print axioms bekenstein_holographic_form_and_quarter_area_reduction
#print axioms bekenstein_bits_form_and_log_two_positivity
#print axioms bekenstein_holographic_principle_quarter_area_iff
#print axioms bekenstein_bound_layerB_master_capstone
#print axioms kerr_entropy_satisfies_schwarzschild_bekenstein_bound
#print axioms kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants
#print axioms kerr_schwarzschild_limit_hawking_smarr_and_evaporation
#print axioms kerr_sorkin_deSitter_bekenstein_entropy_bridge
#print axioms schwarzschild_trapped_surface_and_bekenstein_saturation_bridge
#print axioms malament_4D_conformal_weyl_and_christodoulou_area_bridge
#print axioms variational_ostrogradsky_and_black_hole_mechanics_bridge
#print axioms curved_4D_christodoulou_bekenstein_black_hole_mechanics_master_synthesis

end UnifiedTheory.Audit.KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge
