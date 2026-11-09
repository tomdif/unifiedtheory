/- The normalized transverse Gaussian is concentrated jointly at zero
position and zero canonical momentum, tested by actual L2 phase-translation
unitaries. The small parameter is not a Hamiltonian cutoff. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound (quadraticSize)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

abbrev TransverseHilbert := Lp ℂ 2 (volume : Measure Transverse)

def gaussian (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : TransverseHilbert :=
  (physicalGaussian_memLp α β hα hβ).toLp (physicalGaussian α β)

theorem gaussian_norm_square (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖gaussian α β hα hβ‖^2 = gaussianMass α β :=
  (toLp_square_integral _ (physicalGaussian_memLp α β hα hβ)).trans (physicalGaussian_mass α β hα)

theorem gaussian_ne_zero (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : gaussian α β hα hβ ≠ 0 := by
  have hp := gaussianMass_positive α β hα hβ
  intro hz
  have he := gaussian_norm_square α β hα hβ
  rw [hz,norm_zero,zero_pow (by norm_num)] at he
  linarith only [hp,he]

theorem gaussian_translation_inner (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (v : Transverse) :
    inner ℂ (gaussian α β hα hβ) (translation volume v (gaussian α β hα hβ)) =
      (Real.exp (-quadraticSize α β v/2)*gaussianMass α β:ℝ) := by
  rw [L2.inner_def]
  apply Eq.trans _ (gaussian_overlap α β hα v)
  apply integral_congr_ae
  filter_upwards [(physicalGaussian_memLp α β hα hβ).coeFn_toLp,
    translation_coe volume v (gaussian α β hα hβ),
    (shift_preserves volume v).quasiMeasurePreserving.ae (physicalGaussian_memLp α β hα hβ).coeFn_toLp]
    with x hx ht hv
  change gaussian α β hα hβ x = physicalGaussian α β x at hx
  change gaussian α β hα hβ (x+v) = physicalGaussian α β (x+v) at hv
  rw [ht,hx,hv]
  exact RCLike.inner_apply' _ _

theorem gaussian_translation_square (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (v : Transverse) :
    ‖translation volume v (gaussian α β hα hβ)-gaussian α β hα hβ‖^2 =
      2*gaussianMass α β*(1-Real.exp (-quadraticSize α β v/2)) := by
  rw [norm_sub_rev,norm_sub_sq (𝕜 := ℂ),(translation volume v).norm_map,gaussian_translation_inner,
    gaussian_norm_square]
  simp only [RCLike.re_to_complex,Complex.ofReal_re]
  ring

def unitGaussian (hbar : ℝ) (hh : hbar ≠ 0) : TransverseHilbert :=
  let g := gaussian (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  (‖g‖⁻¹:ℝ) • g

theorem unitGaussian_norm (hbar : ℝ) (hh : hbar ≠ 0) : ‖unitGaussian hbar hh‖ = 1 := by
  rw [unitGaussian,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr
    (gaussian_ne_zero _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)))

def translationCost (v : Transverse) : ℝ := quadraticSize (1/2) (1/64) v

theorem translationCost_nonnegative (v : Transverse) : 0 ≤ translationCost v := by
  change 0 ≤ ∑ i : Fin 5, widths (1/2) (1/64) i * (v i)^2
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (widths_positive (1/2) (1/64) (by norm_num) (by norm_num) i).le (sq_nonneg _))

theorem ground_translation_cost (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    quadraticSize (groundWidth hbar) (neutralWidth hbar) (hbar • v) = |hbar| *translationCost v := by
  unfold translationCost quadraticSize neutralWidth groundWidth widths
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Pi.smul_apply,smul_eq_mul,add_zero,mul_pow]
  rw [← sq_abs hbar]
  field_simp
  ring

private theorem cancel_gaussian_mass (n M r : ℝ) (hM : 0 < M) (hn : n^2 = M) :
    n⁻¹^2*(2*M*(1-r)) = 2*(1-r) := by rw [inv_pow,hn]; field_simp

theorem unitGaussian_translation_square (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    ‖translation volume (hbar • v) (unitGaussian hbar hh)-unitGaussian hbar hh‖^2 =
      2*(1-Real.exp (-|hbar| *translationCost v/2)) := by
  let g := gaussian (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  have he : translation volume (hbar • v) (unitGaussian hbar hh)-unitGaussian hbar hh =
      (‖g‖⁻¹:ℝ) • (translation volume (hbar • v) g-g) := by
    have hs : translation volume (hbar • v) ((‖g‖⁻¹:ℝ) • g) =
        (‖g‖⁻¹:ℝ) • translation volume (hbar • v) g :=
      (translation volume (hbar • v)).map_smul_of_tower _ _
    exact hs ▸ (smul_sub (‖g‖⁻¹:ℝ) (translation volume (hbar • v) g) g).symm
  rw [he,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  have hn := gaussian_translation_square _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (hbar • v)
  have hc := ground_translation_cost hbar hh v
  have hq := gaussian_norm_square _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  rw [hn,hc,neg_mul]
  exact cancel_gaussian_mass ‖g‖ _ _ (gaussianMass_positive _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)) hq

theorem unitGaussian_translation_bound (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    ‖translation volume (hbar • v) (unitGaussian hbar hh)-unitGaussian hbar hh‖ ≤
      Real.sqrt (|hbar| *translationCost v) := by
  have he := Real.add_one_le_exp (-|hbar| *translationCost v/2)
  apply (Real.le_sqrt (norm_nonneg _) (mul_nonneg (abs_nonneg _) (translationCost_nonnegative v))).mpr
  rw [unitGaussian_translation_square]
  linarith only [he]

theorem unitGaussian_modulation_bound (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    ‖modulation volume (dot v) (dot_continuous v).measurable (unitGaussian hbar hh)-unitGaussian hbar hh‖ ≤
      Real.sqrt (2560*|hbar| *directionSize v) := by
  let g := gaussian (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  have hm := dot_gaussian_memLp _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) v
  let q := hm.toLp (fun x : Transverse => (dot v x:ℂ)*physicalGaussian (groundWidth hbar) (neutralWidth hbar) x)
  have hq : q =ᵐ[volume] fun x => (dot v x:ℂ)*g x := by
    filter_upwards [hm.coeFn_toLp,(physicalGaussian_memLp _ _ (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh)).coeFn_toLp] with x hx hg
    exact hx.trans (congrArg (fun z : ℂ => (dot v x:ℂ)*z) hg.symm)
  have hb := modulation_difference volume (dot v) (dot_continuous v).measurable g q hq
  have hmass := (toLp_square_integral _ hm).le.trans (ground_dot_mass_bound hbar hh v)
  have hn := gaussian_norm_square _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  have hg : 0 < ‖g‖^2 := hn.symm ▸ gaussianMass_positive _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
  have hqnorm : (‖g‖⁻¹*‖q‖)^2 ≤ 2560*|hbar| *directionSize v := by
    rw [mul_pow,inv_pow,← div_eq_inv_mul]
    apply (div_le_iff₀ hg).mpr
    exact hmass.trans_eq (congrArg (fun m : ℝ => (2560*|hbar| *directionSize v)*m) hn.symm)
  have hdiff : ‖modulation volume (dot v) (dot_continuous v).measurable (unitGaussian hbar hh)-unitGaussian hbar hh‖ ≤
      ‖g‖⁻¹*‖q‖ := by
    have he : modulation volume (dot v) (dot_continuous v).measurable (unitGaussian hbar hh)-unitGaussian hbar hh =
        (‖g‖⁻¹:ℝ) • (modulation volume (dot v) (dot_continuous v).measurable g-g) := by
      have hs : modulation volume (dot v) (dot_continuous v).measurable ((‖g‖⁻¹:ℝ) • g) =
          (‖g‖⁻¹:ℝ) • modulation volume (dot v) (dot_continuous v).measurable g :=
        (modulation volume (dot v) (dot_continuous v).measurable).map_smul_of_tower _ _
      exact hs ▸ (smul_sub (‖g‖⁻¹:ℝ) (modulation volume (dot v) (dot_continuous v).measurable g) g).symm
    rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
  exact hdiff.trans ((Real.le_sqrt (by positivity) (by unfold directionSize; positivity)).mpr hqnorm)

def errorBound (hbar : ℝ) (ξ η : Transverse) : ℝ :=
  Real.sqrt (|hbar| *translationCost η)+Real.sqrt (2560*|hbar| *directionSize ξ)

theorem phaseTranslation_bound (hbar : ℝ) (hh : hbar ≠ 0) (ξ η : Transverse) :
    ‖phaseTranslation volume (dot ξ) (dot_continuous ξ).measurable (hbar • η) (unitGaussian hbar hh)-unitGaussian hbar hh‖ ≤
      errorBound hbar ξ η :=
  (phaseTranslation_difference volume _ _ _ _).trans
    (add_le_add (unitGaussian_translation_bound hbar hh η) (unitGaussian_modulation_bound hbar hh ξ))

theorem errorBound_tendsto (ξ η : Transverse) : Tendsto (fun hbar : ℝ => errorBound hbar ξ η) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun hbar : ℝ => errorBound hbar ξ η) := by unfold errorBound; fun_prop
  simpa only [errorBound,abs_zero,zero_mul,mul_zero,Real.sqrt_zero,add_zero] using hc.tendsto 0

#print axioms gaussian_norm_square
#print axioms gaussian_ne_zero
#print axioms gaussian_translation_inner
#print axioms gaussian_translation_square
#print axioms unitGaussian_norm
#print axioms translationCost_nonnegative
#print axioms ground_translation_cost
#print axioms unitGaussian_translation_square
#print axioms unitGaussian_translation_bound
#print axioms unitGaussian_modulation_bound
#print axioms phaseTranslation_bound
#print axioms errorBound_tendsto

end
end UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit
