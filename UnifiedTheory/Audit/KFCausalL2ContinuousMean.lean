/- A continuous pointwise mean of a continuous family of L2 vectors
automatically lies in L2. This removes a separate integrability premise
from the representative theorem used for exact source coefficients. -/
import UnifiedTheory.Audit.KFCausalL2IntegralRepresentative
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalL2ContinuousMean
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalProbabilityL2Mean (mean mean_integral mean_norm_le)
open KFCausalAveragedEnergyGraph (l2_norm_square)

theorem integral_square_bound (f : ℝ → ℂ) (hf : MemLp f 2 angleMeasure) :
    ‖∫ θ, f θ ∂angleMeasure‖^2 ≤ ∫ θ, ‖f θ‖^2 ∂angleMeasure := by
  have hn := mean_norm_le angleMeasure (hf.toLp f)
  rw [mean_integral,integral_congr_ae hf.coeFn_toLp] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  rw [l2_norm_square] at hs
  exact hs.trans_eq (integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖^2)))

theorem pointwise_mean_memLp (U : ℝ → Hilbert) (F : ℝ → Configuration → ℂ)
    (G : Configuration → ℂ) (hU : Continuous U)
    (hF : Continuous (fun z : ℝ × Configuration => F z.1 z.2))
    (hr : ∀ θ, U θ =ᵐ[volume] F θ) (hG : Continuous G)
    (hmean : ∀ x, (∫ θ, F θ x ∂angleMeasure) = G x) :
    MemLp G 2 volume := by
  have hj := KFCausalL2IntegralRepresentative.joint_memLp U F
    (continuous_angle_memLp U hU) hF.aestronglyMeasurable hr
  have hi := (memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).mp hj
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  apply hi.integral_prod_right.mono' (hG.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← hmean]
  exact integral_square_bound (fun θ => F θ x)
    (continuous_angle_memLp _ (hF.comp (continuous_id.prodMk continuous_const)))

theorem integral_coe (U : ℝ → Hilbert) (F : ℝ → Configuration → ℂ)
    (G : Configuration → ℂ) (hU : Continuous U)
    (hF : Continuous (fun z : ℝ × Configuration => F z.1 z.2))
    (hr : ∀ θ, U θ =ᵐ[volume] F θ) (hG : Continuous G)
    (hmean : ∀ x, (∫ θ, F θ x ∂angleMeasure) = G x) :
    ((∫ θ, U θ ∂angleMeasure) : Hilbert) =ᵐ[volume] G :=
  KFCausalL2IntegralRepresentative.integral_coe U F G hU hF hr
    (pointwise_mean_memLp U F G hU hF hr hG hmean) hmean

#print axioms integral_square_bound
#print axioms pointwise_mean_memLp
#print axioms integral_coe
end
end UnifiedTheory.Audit.KFCausalL2ContinuousMean
