/- Transfer actual centered polynomial factor integrability through the
proved coordinate map and spectator Gaussian products. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneUniformScore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination (density potential)

theorem centered_factor_memLp (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (P : Polynomial ℂ) (n : ℕ) :
    MemLp (fun q : Transverse => factor ε y α β 0 1 P pointField n q s) 2 volume := by
  have hc := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Transverse => s) (fun q => q) (fun _ => 0) (fun _ => 1)
    continuous_const continuous_id continuous_const continuous_const P pointField n
  apply (amplitudeEnvelope_memLp ε y α β hα hβ 0 P pointField n).of_le hc.aestronglyMeasurable
  filter_upwards [] with q
  simpa only [Real.norm_eq_abs,abs_of_nonneg (amplitudeEnvelope_nonnegative ε y α β 0 P pointField n q)]
    using factor_bound ε y α β hε hy hα hβ hw 0 0 le_rfl 1 (by simp) P pointField n q s

theorem centeredEnergy_sum (α β ε y s : ℝ) (P : Polynomial ℂ) (q : Transverse) :
    centeredEnergyDensity α β (scale ε y s) P q =
      ‖factor ε y α β 0 1 P pointField 0 q s‖^2+
        (1/2:ℝ)*‖factor ε y α β 0 1 P pointField 1 q s‖^2+
        (1/4:ℝ)*‖factor ε y α β 0 1 P pointField 2 q s‖^2 := by
  simp only [centeredEnergyDensity,potential,factor,KFCausalPolynomialKernelResponse.transverse,
    KFCausalPolynomialKernelResponse.weight,KFCausalGaussianKernelResponse.transverse,
    KFCausalRelativeGaussianDifferential.profile,one_mul,pow_zero,pow_one,
    norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem centeredEnergy_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (P : Polynomial ℂ) :
    Integrable (centeredEnergyDensity α β (scale ε y s) P) volume := by
  have hi (n : ℕ) : Integrable (fun q => ‖factor ε y α β 0 1 P pointField n q s‖^2) volume := by
    have hm := centered_factor_memLp α β ε y s hα hβ hw hε hy P n
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have he : centeredEnergyDensity α β (scale ε y s) P = fun q =>
      ‖factor ε y α β 0 1 P pointField 0 q s‖^2+
        (1/2:ℝ)*‖factor ε y α β 0 1 P pointField 1 q s‖^2+
        (1/4:ℝ)*‖factor ε y α β 0 1 P pointField 2 q s‖^2 :=
    funext (centeredEnergy_sum α β ε y s P)
  rw [he]
  exact ((hi 0).add ((hi 1).const_mul _)).add ((hi 2).const_mul _)

theorem reconstruct_integrable (r : ℂ) (hb : r.im ≠ 0) (f : Transverse → ℝ)
    (hf : Integrable f volume) : Integrable (fun u => f (reconstruct r u)) volume := by
  have he := (coordinateEquiv r hb).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
    |>.integrable_map_iff (μ := volume) (g := fun u => f (reconstruct r u))
  have hfun : ((coordinateEquiv r hb).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates r := funext (coordinateMap_apply r)
  rw [hfun,coordinates_volume r hb,integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < 1/(4*|r.im|))).ne'
    ENNReal.ofReal_ne_top] at he
  exact he.mpr (by simpa only [Function.comp_def,reconstruct_coordinates r hb] using hf)

theorem integrable_tail_product (n : ℕ) (f : ℝ → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hfg : Integrable (fun u : Fin (n+1) → ℝ => f (u 0)*g (fun i => u i.succ)) volume)
    (hf : (∫ x, f x) ≠ 0) : Integrable g volume := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hi := hp.integrable_comp_of_integrable hfg
  have hi' : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1*g p.2) volume := by
    simpa only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.cons_succ,Fin.zero_succAbove,cast_eq,Fin.cons_zero] using hi
  have hm := hi'.integral_prod_right
  simp only [integral_mul_const] at hm
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hf) g).mp hm

theorem actualDensity_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)
    (P : Polynomial ℂ) :
    Integrable (fun v : Fin 2 → ℝ => actualDensity α β ε y s P (v 0) (v 1)) volume := by
  let r := scale ε y s
  have hb : r.im ≠ 0 := scale_im_ne_zero ε y s hε hy hy0
  have hA : 0 < r.re^2-r.im^2 := scale_square_re_positive ε y s hε hy
  let f2 := fun x : ℝ => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2)
  let f1 := fun x : ℝ => Real.exp (-(α*(r.re^2-r.im^2))*x^2)
  let g2 := fun v : Fin 2 → ℝ => density 1 β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1)
  let g3 := fun u : Fin 3 → ℝ => f1 (u 0)*g2 (fun i => u i.succ)
  let g4 := fun u : Fin 4 → ℝ => f2 (u 0)*g3 (fun i => u i.succ)
  have h5 : Integrable (fun u : Transverse => f2 (u 0)*g4 (fun i => u i.succ)) volume := by
    have hi := reconstruct_integrable r hb (centeredEnergyDensity α β r P)
      (centeredEnergy_integrable α β ε y s hα hβ hw hε hy P)
    convert hi using 1
    funext u
    simp only [centeredEnergyDensity,gaussian_norm_reconstruct α β r hb,
      field_reconstruct r hb,neutral_position r hb,density_factorization]
    rfl
  have hf1 : (∫ x, f1 x) ≠ 0 := by
    dsimp [f1]
    rw [integral_gaussian]
    positivity
  have hf2 : (∫ x, f2 x) ≠ 0 := by
    dsimp [f2]
    rw [integral_gaussian]
    positivity
  have h2 := integrable_tail_product 2 f1 g2
    (integrable_tail_product 3 f2 g3 (integrable_tail_product 4 f2 g4 h5 hf2) hf2) hf1
  convert h2.const_mul (prefactor α r) using 1
  funext v
  unfold actualDensity g2 density
  dsimp [r]
  ring

#print axioms centered_factor_memLp
#print axioms centeredEnergy_sum
#print axioms centeredEnergy_integrable
#print axioms reconstruct_integrable
#print axioms integrable_tail_product
#print axioms actualDensity_integrable
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability
