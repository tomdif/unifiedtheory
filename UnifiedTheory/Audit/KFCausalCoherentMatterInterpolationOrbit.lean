/- The field-weighted interpolation is jointly continuous in charge angle
and interpolation parameter. All charge orbits use one fixed finite
coherent representation, retaining complex coefficients and cross terms. -/
import UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity
import UnifiedTheory.Audit.KFCausalCoherentMatterInterpolation
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterInterpolationOrbit
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_continuous)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters (sourceCoefficients_parameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
  (amplitudeConstant_continuous sourceCoefficients_continuous continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem weighted_input_joint_continuous (P : Weight) (k : Joint 2 4) :
    Continuous (fun p : ℝ × ℝ => KFCausalFieldShearPathGraphs.state ε h hε hb
      (coherentSeed a h ha hh (parameter p.2 k)) P p.1) := by
  have hk : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  exact KFCausalShearSourceOrbitContinuity.input_joint_continuous P
    (clockAmplitude ε a (clockFrequency k) (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a (clockFrequency k) (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a (clockFrequency k) (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (KFCausalImaginaryShearPathDomain.displacement_strip_bound ε h hε hb)
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (fun θ => sourceCoefficients h (parameter θ k)) ((sourceCoefficients_continuous h).comp hk)
    (sourceCoefficients h k) (fun θ => sourceCoefficients_parameter h hh θ k)

theorem weighted_first_joint_continuous (P : Weight) (k : Joint 2 4) :
    Continuous (fun p : ℝ × ℝ => KFCausalFieldShearPathGraphs.firstState ε h hε hb
      (coherentSeed a h ha hh (parameter p.2 k)) P p.1) := by
  have hk : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  exact (KFCausalShearSourceOrbitContinuity.first_joint_continuous P
    (clockAmplitude ε a (clockFrequency k) (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a (clockFrequency k) (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a (clockFrequency k) (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (KFCausalImaginaryShearPathDomain.displacement_strip_bound ε h hε hb)
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (fun θ => sourceCoefficients h (parameter θ k)) ((sourceCoefficients_continuous h).comp hk)
    (sourceCoefficients h k) (fun θ => sourceCoefficients_parameter h hh θ k)).const_smul (-Complex.I*(h:ℂ))

variable (l : Transverse →L[ℝ] ℝ) (i : Fin 2) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)

def field (θ t : ℝ) : Hilbert := KFCausalCoherentMatterInterpolation.field ε a h hε ha hh hb l i
  (fun j => parameter (2*Real.pi*θ) (k j)) z t
def shear (θ t : ℝ) : Hilbert := KFCausalCoherentMatterInterpolation.shear ε a h hε ha hh hb l i
  (fun j => parameter (2*Real.pi*θ) (k j)) z t
def derivativeField (θ t : ℝ) : Hilbert := KFCausalCoherentMatterInterpolation.derivativeField ε a h hε ha hh hb l i
  (fun j => parameter (2*Real.pi*θ) (k j)) z t

local notation "U" => field ε a h hε ha hh hb l i k z
local notation "J" => shear ε a h hε ha hh hb l i k z
local notation "D" => derivativeField ε a h hε ha hh hb l i k z

theorem curves_joint_continuous :
    Continuous (fun p : ℝ × ℝ => U p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => J p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => D p.1 p.2) := by
  have hr : Continuous (fun p : ℝ × ℝ => (p.2,2*Real.pi*p.1)) :=
    continuous_snd.prodMk (continuous_const.mul continuous_fst)
  have hc (j : Fin n) : Continuous (fun p : ℝ × ℝ => z j*amplitudeConstant h (parameter (2*Real.pi*p.1) (k j))) :=
    continuous_const.mul ((amplitudeConstant_continuous h).comp
      (parameter_continuous.comp (f := fun p : ℝ × ℝ => (2*Real.pi*p.1,k j))
        ((continuous_const.mul continuous_fst).prodMk continuous_const)))
  have hu (P : Weight) (j : Fin n) :=
    (weighted_input_joint_continuous ε a h hε ha hh hb P (k j)).comp hr
  have hv (P : Weight) (j : Fin n) :=
    (weighted_first_joint_continuous ε a h hε ha hh hb P (k j)).comp hr
  refine ⟨?_,?_,?_⟩
  · exact continuous_finset_sum Finset.univ (fun j _ => (hc j).smul (hu (fieldWeight l i) j))
  · exact continuous_finset_sum Finset.univ (fun j _ => (hc j).smul
      ((hv (fieldWeight l i) j).add ((hu (slopeWeight l i) j).const_smul (-Complex.I*(h:ℂ)))))
  · exact continuous_finset_sum Finset.univ (fun j _ => (hc j).smul (hu (slopeWeight l i) j))

variable (W : Hilbert →L[ℂ] Hilbert)

def expectation (θ t : ℝ) : ℝ := (inner ℂ (W (U θ t)) (W (J θ t))).re
def pathCost (θ : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ‖W (D θ t)‖^2

local notation "Q" => expectation ε a h hε ha hh hb l i k z W
local notation "C" => pathCost ε a h hε ha hh hb l i k z W

theorem expectation_joint_continuous : Continuous (fun p : ℝ × ℝ => Q p.1 p.2) :=
  Complex.continuous_re.comp ((W.continuous.comp (curves_joint_continuous ε a h hε ha hh hb l i k z).1).inner
    (W.continuous.comp (curves_joint_continuous ε a h hε ha hh hb l i k z).2.1))

theorem cost_joint_continuous : Continuous (fun p : ℝ × ℝ => ‖W (D p.1 p.2)‖^2) :=
  (W.continuous.comp (curves_joint_continuous ε a h hε ha hh hb l i k z).2.2).norm.pow 2

theorem pathCost_continuous : Continuous C := by
  change Continuous (fun θ => ∫ t in (0:ℝ)..1, ‖W (D θ t)‖^2)
  have hc := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun θ t : ℝ => ‖W (D θ t)‖^2)
    (cost_joint_continuous ε a h hε ha hh hb l i k z W) (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  simpa only [pathCost,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1)] using hc

theorem expectation_angle_integrable (t : ℝ) : Integrable (fun θ => Q θ t) angleMeasure :=
  (continuous_angle_memLp _ ((expectation_joint_continuous ε a h hε ha hh hb l i k z W).comp
    (continuous_id.prodMk continuous_const))).integrable (by norm_num)

theorem pathCost_angle_integrable : Integrable C angleMeasure :=
  (continuous_angle_memLp _ (pathCost_continuous ε a h hε ha hh hb l i k z W)).integrable (by norm_num)

theorem pathCost_nonnegative (θ : ℝ) : 0 ≤ C θ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)

#print axioms weighted_input_joint_continuous
#print axioms weighted_first_joint_continuous
#print axioms curves_joint_continuous
#print axioms expectation_joint_continuous
#print axioms cost_joint_continuous
#print axioms pathCost_continuous
#print axioms expectation_angle_integrable
#print axioms pathCost_angle_integrable
#print axioms pathCost_nonnegative
end
end UnifiedTheory.Audit.KFCausalCoherentMatterInterpolationOrbit
