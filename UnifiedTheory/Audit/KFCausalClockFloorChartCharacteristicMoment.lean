/- First moments differentiate the chart characteristic function. This
requires an integrable first moment, not a chart-operator-domain vector. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain
import UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorChartCharacteristicMoment
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain (density moment)

theorem phase_zero (ε : ℝ) (x : Configuration) : phase ε 0 x = 1 := by
  simp only [phase,zero_mul,Real.fourierChar_apply,mul_zero,Complex.ofReal_zero,Complex.exp_zero]

theorem phase_derivative (ε r : ℝ) (x : Configuration) :
    HasDerivAt (fun z => phase ε z x) (Complex.I*(2*Real.pi:ℝ)*(chart ε x.1:ℂ)*phase ε r x) r := by
  have he := ((((hasDerivAt_id r).mul_const (chart ε x.1)).const_mul (2*Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simp only [id_eq,one_mul] at he
  simpa only [phase,Real.fourierChar_apply,id_eq,one_mul] using
    he.congr_deriv (by push_cast; ring)

theorem characteristic_integral (ε r : ℝ) (f : Hilbert) :
    inner ℂ f (modulation ε r f) = ∫ x, phase ε r x*(‖f x‖^2:ℝ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modulation_coe ε r f] with x hx
  rw [hx]
  change inner ℂ (f x) (phase ε r x • f x) = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  rfl

theorem characteristic_derivative (ε : ℝ) (f : Hilbert) (hf : Integrable (density ε f)) :
    HasDerivAt (fun r => inner ℂ f (modulation ε r f))
      (Complex.I*(2*Real.pi:ℝ)*(moment ε f:ℂ)) 0 := by
  let F := fun r x => phase ε r x*(‖f x‖^2:ℝ)
  let G := fun r x => (Complex.I*(2*Real.pi:ℝ)*(chart ε x.1:ℂ)*phase ε r x)*(‖f x‖^2:ℝ)
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) volume :=
    (phase_measurable ε r).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable f).norm.pow 2))
  have hFi : Integrable (F 0) volume := by
    simpa only [F,phase_zero,one_mul] using
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).ofReal
  have hG0 : G 0 = fun x => (Complex.I*(2*Real.pi:ℝ))*(density ε f x:ℂ) := by
    funext x
    simp only [G,phase_zero,density,Complex.ofReal_mul,mul_assoc,one_mul]
  have hGm : AEStronglyMeasurable (G 0) volume := by
    rw [hG0]
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := G) (x₀ := (0:ℝ)) (s := Set.univ) (bound := fun x => (2*Real.pi)*‖density ε f x‖)
    Filter.univ_mem (Eventually.of_forall hFm) hFi hGm
    (Eventually.of_forall (fun x r _ => by
      simp only [G,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,phase_norm,density]
      norm_num [abs_mul,abs_of_pos Real.pi_pos,abs_of_nonneg (sq_nonneg ‖f x‖)]
      ring_nf
      exact le_rfl))
    (hf.norm.const_mul (2*Real.pi))
    (Eventually.of_forall (fun x r _ => (phase_derivative ε r x).mul_const (‖f x‖^2:ℝ)))
  have hg : (∫ x, G 0 x) = Complex.I*(2*Real.pi:ℝ)*(moment ε f:ℂ) := by
    rw [hG0,integral_const_mul,integral_complex_ofReal]
    rfl
  simpa only [characteristic_integral,F,hg] using hd.2

theorem moment_difference_of_slope (ε : ℝ) (f g : Hilbert)
    (hf : Integrable (density ε f)) (hg : Integrable (density ε g)) (hn : ‖f‖ = ‖g‖)
    (A : ℂ) (hA : Tendsto (fun r : ℝ => r⁻¹ •
      (inner ℂ f (modulation ε r f)-inner ℂ g (modulation ε r g))) (𝓝[≠] 0)
        (𝓝 (Complex.I*(2*Real.pi:ℝ)*A))) :
    A = (moment ε f:ℂ)-(moment ε g:ℂ) := by
  have hd := (characteristic_derivative ε f hf).sub (characteristic_derivative ε g hg)
  have he : inner ℂ f f-inner ℂ g g = 0 := by
    simp only [inner_self_eq_norm_sq_to_K,hn,sub_self]
  have hl := hd.tendsto_slope_zero
  simp only [Pi.sub_apply,zero_add,KFCausalClockFloorChartPhaseContinuity.modulation_zero,he,sub_zero] at hl
  have hz := tendsto_nhds_unique hA hl
  rw [← mul_sub] at hz
  exact mul_left_cancel₀
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity : (2:ℝ)*Real.pi ≠ 0))) hz

#print axioms phase_zero
#print axioms phase_derivative
#print axioms characteristic_integral
#print axioms characteristic_derivative
#print axioms moment_difference_of_slope
end
end UnifiedTheory.Audit.KFCausalClockFloorChartCharacteristicMoment
