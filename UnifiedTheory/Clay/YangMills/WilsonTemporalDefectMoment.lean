/- Exponential suppression of one temporal-gauge kinetic defect under the
actual stationary raw two-slice law. Its ground state and normalization are
those of the original full Wilson transfer. This background tail is not a
bound for arbitrary squared observables or for spatial plaquette defects. -/
import UnifiedTheory.Clay.YangMills.WilsonTemporalCutFloor
import Mathlib.Probability.Moments.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTemporalDefectMoment
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonGroundLocalComparison WilsonTemporalCutFloor
open WilsonSingleLinkStaples (character character_continuous)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def defect (e : SpatialVertex n × Fin 3) (z : Slice n × Slice n) : ℝ :=
  ‖((z.1 e)⁻¹ * z.2 e : Q) - (1 : ℍ)‖^2

omit [NeZero n] in
theorem defect_continuous (e : SpatialVertex n × Fin 3) : Continuous (defect n e) := by
  unfold defect
  fun_prop

def law (β : ℝ) (hβ : 0 ≤ β) : Measure (Slice n × Slice n) :=
  GroundStateDirichlet.edgeLaw (WilsonSlabOperator.measure n)
    (fun z => rawKernel character β 2 z.1 z.2) (ground n β hβ) ‖transfer n β‖

theorem law_probability (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (law n β hβ) :=
  GroundStateDirichlet.edgeLaw_probability (WilsonSlabOperator.measure n)
    (fun z => rawKernel character β 2 z.1 z.2)
    (rawKernel_continuous character character_continuous β 2)
    (fun z => (rawKernel_pos _ _ _ z.1 z.2).le) (ground n β hβ)
    (ground n β hβ).continuous (fun u => (ground_pos n β hβ u).le) ‖transfer n β‖
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    (ground_raw_equation n β hβ) (ground_square_integral n β hβ)

theorem law_integral (β : ℝ) (hβ : 0 ≤ β) (F : Slice n × Slice n → ℝ) :
    (∫ z, F z ∂law n β hβ) = ∫ z : Slice n × Slice n,
      (rawKernel character β 2 z.1 z.2 * ground n β hβ z.1 * ground n β hβ z.2 /
        ‖transfer n β‖) * F z ∂(WilsonSlabOperator.measure n).prod
          (WilsonSlabOperator.measure n) :=
  GroundStateDirichlet.edge_integral (WilsonSlabOperator.measure n)
    (fun z => rawKernel character β 2 z.1 z.2)
    (rawKernel_continuous character character_continuous β 2)
    (fun z => (rawKernel_pos _ _ _ z.1 z.2).le) (ground n β hβ)
    (ground n β hβ).continuous (fun u => (ground_pos n β hβ u).le) ‖transfer n β‖
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1 F

theorem cancellation (β : ℝ) (e : SpatialVertex n × Fin 3) (z : Slice n × Slice n) :
    rawKernel character β 2 z.1 z.2 * Real.exp (β * defect n e z) =
      cut n β e z.1 z.2 := by
  rw [← raw_factor n β e z.1 z.2]
  unfold SU2CrossingHaarFloor.kernel SU2GaussianMass.weight defect
  rw [mul_assoc, ← Real.exp_add, show
    -β * ‖(((z.1 e)⁻¹ * z.2 e : Q) : ℍ) - 1‖^2 +
      β * ‖(((z.1 e)⁻¹ * z.2 e : Q) : ℍ) - 1‖^2 = 0 by ring,
    Real.exp_zero, mul_one]

/-- The prefactor grows as beta^(3/2), with no spatial-volume dependence. -/
theorem exponential_moment (β : ℝ) (hβ : 3 / 4 ≤ β) (e : SpatialVertex n × Fin 3) :
    (∫ z, Real.exp (β * defect n e z) ∂law n β (by linarith)) ≤
      SU2GaussianMass.cap β := by
  rw [law_integral]
  have he (z : Slice n × Slice n) :
      (rawKernel character β 2 z.1 z.2 * ground n β (by linarith) z.1 *
        ground n β (by linarith) z.2 / ‖transfer n β‖) * Real.exp (β * defect n e z) =
      (ground n β (by linarith) z.1 * cut n β e z.1 z.2 *
        ground n β (by linarith) z.2) / ‖transfer n β‖ := by
    rw [show rawKernel character β 2 z.1 z.2 * ground n β (by linarith) z.1 *
        ground n β (by linarith) z.2 / ‖transfer n β‖ * Real.exp (β * defect n e z) =
      (ground n β (by linarith) z.1 *
        (rawKernel character β 2 z.1 z.2 * Real.exp (β * defect n e z)) *
          ground n β (by linarith) z.2) / ‖transfer n β‖ by ring, cancellation]
  simp only [he]
  rw [integral_div]
  exact (div_le_iff₀ (PositiveKernelGroundState.transfer_top_eigenvector n β
    (by linarith)).1).mpr (ground_removal n β hβ e)

theorem tail (β : ℝ) (hβ : 3 / 4 ≤ β) (e : SpatialVertex n × Fin 3) (t : ℝ) :
    (law n β (by linarith)).real {z | t ≤ defect n e z} ≤
      Real.exp (-β * t) * SU2GaussianMass.cap β := by
  letI := law_probability n β (by linarith)
  have hc : Continuous (fun z => Real.exp (β * defect n e z)) :=
    Real.continuous_exp.comp (continuous_const.mul (defect_continuous n e))
  have hi : Integrable (fun z => Real.exp (β * defect n e z)) (law n β (by linarith)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (ProbabilityTheory.measure_ge_le_exp_mul_mgf t (by linarith : 0 ≤ β) hi).trans
    (mul_le_mul_of_nonneg_left (exponential_moment n β hβ e) (Real.exp_pos _).le)

end
end UnifiedTheory.Clay.YangMills.WilsonTemporalDefectMoment
