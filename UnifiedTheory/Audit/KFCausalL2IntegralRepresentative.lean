/- Identify a Bochner mean of L2 states with a specified pointwise mean.
The proof uses product L2 integrability and weak Fubini; it does not
interchange point evaluation with the L2 integral. -/
import UnifiedTheory.Audit.KFCausalChargeResponseFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalL2IntegralRepresentative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

theorem joint_memLp (U : ℝ → Hilbert) (F : ℝ → Configuration → ℂ)
    (hU : MemLp U 2 angleMeasure)
    (hF : AEStronglyMeasurable (fun z : ℝ × Configuration => F z.1 z.2)
      (angleMeasure.prod volume))
    (hr : ∀ t, U t =ᵐ[volume] F t) :
    MemLp (fun z : ℝ × Configuration => F z.1 z.2) 2 (angleMeasure.prod volume) := by
  have hs (t : ℝ) : MemLp (F t) 2 volume := (Lp.memLp (U t)).ae_eq (hr t)
  apply (memLp_two_iff_integrable_sq_norm hF).mpr
  apply (integrable_prod_iff (hF.norm.pow 2)).mpr
  refine ⟨Filter.Eventually.of_forall (fun t =>
    (memLp_two_iff_integrable_sq_norm (hs t).aestronglyMeasurable).mp (hs t)),?_⟩
  have he (t : ℝ) : (∫ x : Configuration, ‖‖F t x‖^2‖) = ‖U t‖^2 := by
    simp only [norm_pow,norm_norm]
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (U t),L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) (U t) (U t))]
    apply integral_congr_ae
    filter_upwards [hr t] with x hx
    rw [hx]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (F t x)
  change Integrable (fun t => ∫ x : Configuration, ‖‖F t x‖^2‖) angleMeasure
  simp_rw [he]
  exact (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU

theorem integral_eq_toLp (U : ℝ → Hilbert) (F : ℝ → Configuration → ℂ)
    (G : Configuration → ℂ) (hU : MemLp U 2 angleMeasure)
    (hF : AEStronglyMeasurable (fun z : ℝ × Configuration => F z.1 z.2)
      (angleMeasure.prod volume))
    (hr : ∀ t, U t =ᵐ[volume] F t) (hG : MemLp G 2 volume)
    (hmean : ∀ᵐ x ∂volume, (∫ t, F t x ∂angleMeasure) = G x) :
    (∫ t, U t ∂angleMeasure) = hG.toLp G := by
  have hu := hU.integrable (by norm_num)
  have hj := joint_memLp U F hU hF hr
  apply ext_inner_left ℂ
  intro v
  have hp : Integrable (fun z : ℝ × Configuration => star (v z.2)*F z.1 z.2)
      (angleMeasure.prod volume) :=
    ((Lp.memLp v).comp_snd angleMeasure).star.integrable_mul hj
  rw [← integral_inner hu v,L2.inner_def]
  calc
    (∫ t, inner ℂ v (U t) ∂angleMeasure) =
        ∫ t, ∫ x : Configuration, star (v x)*F t x ∂volume ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hr t] with x hx
      simp only [hx,RCLike.inner_apply,Complex.star_def]
      ring
    _ = ∫ x : Configuration, ∫ t, star (v x)*F t x ∂angleMeasure ∂volume :=
      integral_integral_swap hp
    _ = ∫ x : Configuration, inner ℂ (v x) ((hG.toLp G) x) := by
      apply integral_congr_ae
      filter_upwards [hmean,hG.coeFn_toLp] with x hx hy
      rw [integral_const_mul,hx,hy]
      simp only [RCLike.inner_apply,Complex.star_def]
      ring

theorem integral_coe (U : ℝ → Hilbert) (F : ℝ → Configuration → ℂ)
    (G : Configuration → ℂ) (hU : Continuous U)
    (hF : Continuous (fun z : ℝ × Configuration => F z.1 z.2))
    (hr : ∀ t, U t =ᵐ[volume] F t) (hG : MemLp G 2 volume)
    (hmean : ∀ x, (∫ t, F t x ∂angleMeasure) = G x) :
    ((∫ t, U t ∂angleMeasure) : Hilbert) =ᵐ[volume] G := by
  rw [integral_eq_toLp U F G (continuous_angle_memLp U hU)
    hF.aestronglyMeasurable hr hG (Filter.Eventually.of_forall hmean)]
  exact hG.coeFn_toLp

#print axioms joint_memLp
#print axioms integral_eq_toLp
#print axioms integral_coe
end
end UnifiedTheory.Audit.KFCausalL2IntegralRepresentative
