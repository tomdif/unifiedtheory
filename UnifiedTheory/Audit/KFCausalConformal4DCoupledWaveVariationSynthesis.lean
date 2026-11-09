import UnifiedTheory.Audit.KFCausalConformal4DFullCoordinateOperator
import UnifiedTheory.Audit.KFCausalBDG4DActualTemporalVariation

/-! Unified zeroth-and-first-order continuum limit and affine Taylor-jet
synthesis combining the full four-coordinate conformal BDG operator with its
temporal curvature variation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DCoupledWaveVariationSynthesis
noncomputable section

open Set MeasureTheory Real Filter Topology
open KFCausalConformal4DFullCoordinateOperator (fullOperator full_operator_eq
  full_operator_covariant_limit)
open KFCausalConformal4DChronologicalCurvatureLimit (chronological_operator_eq)
open KFCausalConformal4DCovariantWaveTest (covariantWave scalarCurvature
  temporal_wave_curvature)
open KFCausalBDG4DCompactPhysicalTest (field)
open KFCausalBDG4DTemporalCurvatureLimit (physicalCorrection
  scalar_curvature_derivative)
open KFCausalBDG4DActualTemporalVariation (operator operator_hasDerivAt
  actual_derivative_tendsto actual_derivative_matches_curvature)

/-- Full 4D conformal chronological BDG operator at density `rho` and curvature
parameter `c`. -/
def actual4DOperator (rho c : ℝ) : ℝ :=
  fullOperator rho c

/-- Small-scale parameterization `ε ↦ actual4DOperator ε⁻¹ c` for `ε → 0⁺`. -/
def scaleActual4DOperator (ε c : ℝ) : ℝ :=
  actual4DOperator ε⁻¹ c

/-- Finite difference quotient of `actual4DOperator` with respect to the
temporal curvature parameter `c` with step `δ`. -/
def temporalVariationDifferenceQuotient (rho c δ : ℝ) : ℝ :=
  (actual4DOperator rho (c + δ) - actual4DOperator rho c) / δ

/-- Small-scale parameterization of the temporal variation difference quotient. -/
def scaleTemporalVariationDifferenceQuotient (ε c δ : ℝ) : ℝ :=
  temporalVariationDifferenceQuotient ε⁻¹ c δ

/-- Exact first derivative `d/dc actual4DOperator(rho, c)|_{c=0}` of the full
chronological 4D operator at flat background `c = 0`. -/
def temporalVariationDerivative (rho : ℝ) : ℝ :=
  deriv (fun c => actual4DOperator rho c) 0

/-- Small-scale parameterization of the exact temporal variation derivative. -/
def scaleTemporalVariationDerivative (ε : ℝ) : ℝ :=
  temporalVariationDerivative ε⁻¹

/-- Continuum zeroth-order target `□_g ϕ(0) - (1/2) R(0) ϕ(0)`. -/
def continuumWaveCurvatureValue (c : ℝ) : ℝ :=
  covariantWave (2 * c) 0 field 0 - scalarCurvature (2 * c) 0 / 2 * field 0

/-- Continuum first-order temporal variation target `-(1/2) R'(0)`. -/
def continuumTemporalVariationValue : ℝ :=
  -(1 / 2) * deriv (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0) 0

/-- First-order affine jet `R(c) + τ R'(0)` of the scalar curvature. -/
def scalarCurvatureAffineJet (c τ : ℝ) : ℝ :=
  KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 +
    τ * deriv (fun c' => KFCausalConformal4DDiamondBenchmark.scalar (2 * c') 0) 0

/-- Coupled wave-curvature affine jet
`(□_g ϕ(0) - (1/2) R(0) ϕ(0)) + τ (-(1/2) R'(0))`. -/
def coupledWaveCurvatureAffineJet (c τ : ℝ) : ℝ :=
  continuumWaveCurvatureValue c + τ * continuumTemporalVariationValue

/-- Discrete causal-diamond affine jet built from the full 4D operator and its
temporal derivative at `c = 0`. -/
def discreteJetFromDerivative (rho c τ : ℝ) : ℝ :=
  actual4DOperator rho c + τ * temporalVariationDerivative rho

/-- Discrete causal-diamond affine jet built from the full 4D operator and its
temporal difference quotient. -/
def discreteJetFromDifferenceQuotient (rho c δ τ : ℝ) : ℝ :=
  actual4DOperator rho c + τ * temporalVariationDifferenceQuotient rho c δ

theorem actual4DOperator_eq_operator (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    actual4DOperator rho c = operator rho c := by
  rw [actual4DOperator, full_operator_eq rho c hc, chronological_operator_eq rho c hc]

theorem actual4DOperator_eventuallyEq_operator (rho : ℝ) :
    (fun c => actual4DOperator rho c) =ᶠ[𝓝 (0 : ℝ)] operator rho := by
  filter_upwards [Icc_mem_nhds (by norm_num : -(1 / 54 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 54)] with c hc
  exact actual4DOperator_eq_operator rho c (abs_le.mpr hc)

theorem actual4DOperator_hasDerivAt_zero (rho : ℝ) :
    HasDerivAt (fun c => actual4DOperator rho c) (physicalCorrection rho) 0 :=
  (operator_hasDerivAt rho).congr_of_eventuallyEq
    (actual4DOperator_eventuallyEq_operator rho)

theorem temporalVariationDerivative_eq (rho : ℝ) :
    temporalVariationDerivative rho = deriv (operator rho) 0 := by
  rw [temporalVariationDerivative, (actual4DOperator_hasDerivAt_zero rho).deriv,
    (operator_hasDerivAt rho).deriv]

theorem continuumWaveCurvatureValue_eq (c : ℝ) :
    continuumWaveCurvatureValue c = 8 - 6 * c :=
  temporal_wave_curvature c

theorem scalar_curvature_at_origin (c : ℝ) :
    KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 = 12 * c := by
  rw [KFCausalConformal4DDiamondBenchmark.scalar_curvature]
  ring

theorem scalar_curvature_deriv_at_zero :
    deriv (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0) 0 = 12 :=
  scalar_curvature_derivative.deriv

theorem continuumTemporalVariationValue_eq :
    continuumTemporalVariationValue = -6 := by
  unfold continuumTemporalVariationValue
  rw [scalar_curvature_deriv_at_zero]
  ring

theorem actual4DOperator_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => actual4DOperator rho c) atTop
      (𝓝 (continuumWaveCurvatureValue c)) :=
  full_operator_covariant_limit c hc

theorem temporalVariationDerivative_tendsto :
    Tendsto temporalVariationDerivative atTop
      (𝓝 continuumTemporalVariationValue) := by
  have he : temporalVariationDerivative = fun rho => deriv (operator rho) 0 :=
    funext temporalVariationDerivative_eq
  rw [he]
  exact actual_derivative_matches_curvature

theorem temporalVariationDerivative_tendsto_neg_six :
    Tendsto temporalVariationDerivative atTop (𝓝 (-6)) := by
  rw [← continuumTemporalVariationValue_eq]
  exact temporalVariationDerivative_tendsto

theorem temporalVariationDifferenceQuotient_tendsto (c δ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun rho => temporalVariationDifferenceQuotient rho c δ) atTop
      (𝓝 continuumTemporalVariationValue) := by
  have h1 := full_operator_covariant_limit (c + δ) hcδ
  have h2 := full_operator_covariant_limit c hc
  rw [temporal_wave_curvature (c + δ)] at h1
  rw [temporal_wave_curvature c] at h2
  have hsub := (h1.sub h2).div_const δ
  have hval : (8 - 6 * (c + δ) - (8 - 6 * c)) / δ =
      continuumTemporalVariationValue := by
    rw [continuumTemporalVariationValue_eq]
    field_simp [hδ]
    ring
  rw [hval] at hsub
  exact hsub

theorem temporalVariationDifferenceQuotient_tendsto_neg_six (c δ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun rho => temporalVariationDifferenceQuotient rho c δ) atTop
      (𝓝 (-6)) := by
  rw [← continuumTemporalVariationValue_eq]
  exact temporalVariationDifferenceQuotient_tendsto c δ hc hcδ hδ

/-- Joint `Filter.Tendsto` into `ℝ × ℝ` of `(actual4DOperator, temporalVariationDifferenceQuotient)`
to `(□_g ϕ(0) - (1/2) R(0) ϕ(0), -(1/2) R'(0))`. -/
theorem joint_operator_and_difference_quotient_tendsto (c δ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun rho => (actual4DOperator rho c,
        temporalVariationDifferenceQuotient rho c δ)) atTop
      (𝓝 (continuumWaveCurvatureValue c, continuumTemporalVariationValue)) :=
  (actual4DOperator_tendsto c hc).prodMk_nhds
    (temporalVariationDifferenceQuotient_tendsto c δ hc hcδ hδ)

/-- Joint `Filter.Tendsto` into `ℝ × ℝ` of `(actual4DOperator, temporalVariationDifferenceQuotient)`
to the explicit numeric pair `(8 - 6c, -6)`. -/
theorem joint_operator_and_difference_quotient_tendsto_explicit (c δ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun rho => (actual4DOperator rho c,
        temporalVariationDifferenceQuotient rho c δ)) atTop
      (𝓝 (8 - 6 * c, -6)) := by
  rw [← continuumWaveCurvatureValue_eq c, ← continuumTemporalVariationValue_eq]
  exact joint_operator_and_difference_quotient_tendsto c δ hc hcδ hδ

/-- Small-scale `ε → 0⁺` joint convergence of
`(scaleActual4DOperator, scaleTemporalVariationDifferenceQuotient)` into `ℝ × ℝ`. -/
theorem joint_scale_operator_and_difference_quotient_tendsto (c δ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun ε => (scaleActual4DOperator ε c,
        scaleTemporalVariationDifferenceQuotient ε c δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (continuumWaveCurvatureValue c, continuumTemporalVariationValue)) ∧
    Tendsto (fun ε => (scaleActual4DOperator ε c,
        scaleTemporalVariationDifferenceQuotient ε c δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (8 - 6 * c, -6)) := by
  refine ⟨(joint_operator_and_difference_quotient_tendsto c δ hc hcδ hδ).comp
    tendsto_inv_nhdsGT_zero,
    (joint_operator_and_difference_quotient_tendsto_explicit c δ hc hcδ hδ).comp
      tendsto_inv_nhdsGT_zero⟩

/-- Joint `Filter.Tendsto` into `ℝ × ℝ` of `(actual4DOperator, temporalVariationDerivative)`
to `(□_g ϕ(0) - (1/2) R(0) ϕ(0), -(1/2) R'(0))` and `(8 - 6c, -6)`. -/
theorem joint_operator_and_derivative_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => (actual4DOperator rho c, temporalVariationDerivative rho)) atTop
      (𝓝 (continuumWaveCurvatureValue c, continuumTemporalVariationValue)) ∧
    Tendsto (fun rho => (actual4DOperator rho c, temporalVariationDerivative rho)) atTop
      (𝓝 (8 - 6 * c, -6)) := by
  have h1 := (actual4DOperator_tendsto c hc).prodMk_nhds
    temporalVariationDerivative_tendsto
  have h2 := h1
  rw [continuumWaveCurvatureValue_eq c, continuumTemporalVariationValue_eq] at h2
  exact ⟨h1, h2⟩

/-- Small-scale `ε → 0⁺` joint convergence of
`(scaleActual4DOperator, scaleTemporalVariationDerivative)` into `ℝ × ℝ`. -/
theorem joint_scale_operator_and_derivative_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun ε => (scaleActual4DOperator ε c,
        scaleTemporalVariationDerivative ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (continuumWaveCurvatureValue c, continuumTemporalVariationValue)) ∧
    Tendsto (fun ε => (scaleActual4DOperator ε c,
        scaleTemporalVariationDerivative ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (8 - 6 * c, -6)) := by
  have h := joint_operator_and_derivative_tendsto c hc
  exact ⟨h.1.comp tendsto_inv_nhdsGT_zero, h.2.comp tendsto_inv_nhdsGT_zero⟩

theorem scalarCurvatureAffineJet_eq (c τ : ℝ) :
    scalarCurvatureAffineJet c τ = 12 * c + 12 * τ := by
  unfold scalarCurvatureAffineJet
  rw [scalar_curvature_at_origin, scalar_curvature_deriv_at_zero]
  ring

theorem scalarCurvatureAffineJet_exact (c τ : ℝ) :
    scalarCurvatureAffineJet c τ =
      KFCausalConformal4DDiamondBenchmark.scalar (2 * (c + τ)) 0 := by
  rw [scalarCurvatureAffineJet_eq, scalar_curvature_at_origin]
  ring

theorem coupledWaveCurvatureAffineJet_eq (c τ : ℝ) :
    coupledWaveCurvatureAffineJet c τ = (8 - 6 * c) - 6 * τ := by
  unfold coupledWaveCurvatureAffineJet
  rw [continuumWaveCurvatureValue_eq, continuumTemporalVariationValue_eq]
  ring

theorem coupledWaveCurvatureAffineJet_shift (c τ : ℝ) :
    coupledWaveCurvatureAffineJet c τ = continuumWaveCurvatureValue (c + τ) := by
  rw [coupledWaveCurvatureAffineJet_eq, continuumWaveCurvatureValue_eq]
  ring

theorem discreteJetFromDerivative_tendsto (c τ : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => discreteJetFromDerivative rho c τ) atTop
      (𝓝 (coupledWaveCurvatureAffineJet c τ)) ∧
    Tendsto (fun rho => discreteJetFromDerivative rho c τ) atTop
      (𝓝 ((8 - 6 * c) - 6 * τ)) := by
  have h1 : Tendsto (fun rho => discreteJetFromDerivative rho c τ) atTop
      (𝓝 (coupledWaveCurvatureAffineJet c τ)) :=
    (actual4DOperator_tendsto c hc).add
      (temporalVariationDerivative_tendsto.const_mul τ)
  have h2 := h1
  rw [coupledWaveCurvatureAffineJet_eq] at h2
  exact ⟨h1, h2⟩

theorem discreteJetFromDifferenceQuotient_tendsto (c δ τ : ℝ)
    (hc : |c| ≤ 1 / 54) (hcδ : |c + δ| ≤ 1 / 54) (hδ : δ ≠ 0) :
    Tendsto (fun rho => discreteJetFromDifferenceQuotient rho c δ τ) atTop
      (𝓝 (coupledWaveCurvatureAffineJet c τ)) ∧
    Tendsto (fun rho => discreteJetFromDifferenceQuotient rho c δ τ) atTop
      (𝓝 ((8 - 6 * c) - 6 * τ)) := by
  have h1 : Tendsto (fun rho => discreteJetFromDifferenceQuotient rho c δ τ) atTop
      (𝓝 (coupledWaveCurvatureAffineJet c τ)) :=
    (actual4DOperator_tendsto c hc).add
      ((temporalVariationDifferenceQuotient_tendsto c δ hc hcδ hδ).const_mul τ)
  have h2 := h1
  rw [coupledWaveCurvatureAffineJet_eq] at h2
  exact ⟨h1, h2⟩

/-- The coupled wave-curvature affine jet `(8 - 6c) - 6τ` is uniquely
determined by the continuum limit of the causal-diamond jet operator. -/
theorem coupledWaveCurvatureAffineJet_unique (c τ L : ℝ) (hc : |c| ≤ 1 / 54)
    (hL : Tendsto (fun rho => discreteJetFromDerivative rho c τ) atTop (𝓝 L)) :
    L = coupledWaveCurvatureAffineJet c τ ∧ L = (8 - 6 * c) - 6 * τ := by
  have h1 := tendsto_nhds_unique hL (discreteJetFromDerivative_tendsto c τ hc).1
  exact ⟨h1, h1.trans (coupledWaveCurvatureAffineJet_eq c τ)⟩

/-- Uniqueness of the scalar curvature affine jet `12c + 12τ` recovered from
the pure wave value `8` and the continuum limit `L` of the causal-diamond jet. -/
theorem scalarCurvatureAffineJet_unique_from_wave_limit (c τ L : ℝ)
    (hc : |c| ≤ 1 / 54)
    (hL : Tendsto (fun rho => discreteJetFromDerivative rho c τ) atTop (𝓝 L)) :
    2 * (8 - L) = scalarCurvatureAffineJet c τ ∧
    2 * (8 - L) = 12 * c + 12 * τ := by
  have h := (coupledWaveCurvatureAffineJet_unique c τ L hc hL).2
  have h2 : 2 * (8 - L) = 12 * c + 12 * τ := by linarith
  exact ⟨h2.trans (scalarCurvatureAffineJet_eq c τ).symm, h2⟩

#print axioms actual4DOperator_eq_operator
#print axioms actual4DOperator_eventuallyEq_operator
#print axioms actual4DOperator_hasDerivAt_zero
#print axioms temporalVariationDerivative_eq
#print axioms continuumWaveCurvatureValue_eq
#print axioms scalar_curvature_at_origin
#print axioms scalar_curvature_deriv_at_zero
#print axioms continuumTemporalVariationValue_eq
#print axioms actual4DOperator_tendsto
#print axioms temporalVariationDerivative_tendsto
#print axioms temporalVariationDerivative_tendsto_neg_six
#print axioms temporalVariationDifferenceQuotient_tendsto
#print axioms temporalVariationDifferenceQuotient_tendsto_neg_six
#print axioms joint_operator_and_difference_quotient_tendsto
#print axioms joint_operator_and_difference_quotient_tendsto_explicit
#print axioms joint_scale_operator_and_difference_quotient_tendsto
#print axioms joint_operator_and_derivative_tendsto
#print axioms joint_scale_operator_and_derivative_tendsto
#print axioms scalarCurvatureAffineJet_eq
#print axioms scalarCurvatureAffineJet_exact
#print axioms coupledWaveCurvatureAffineJet_eq
#print axioms coupledWaveCurvatureAffineJet_shift
#print axioms discreteJetFromDerivative_tendsto
#print axioms discreteJetFromDifferenceQuotient_tendsto
#print axioms coupledWaveCurvatureAffineJet_unique
#print axioms scalarCurvatureAffineJet_unique_from_wave_limit

end
end UnifiedTheory.Audit.KFCausalConformal4DCoupledWaveVariationSynthesis
