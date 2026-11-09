/- Differentiation of the actual compact retarded-cone integral. All local
domination is obtained from joint continuity on a fixed compact box. No
curvature/density limit interchange or chronological-diamond identification
is asserted. -/
import UnifiedTheory.Audit.KFCausalConformal4DRegularVolumeSmoothness
import UnifiedTheory.Audit.KFCausalBDG4DCompactProfile
import UnifiedTheory.Audit.KFCausalMinkowski4DVariationCone
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DCompactKernelDerivative
noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
open KFCausalConformal4DTemporalVariation KFCausalConformal4DRegularVolume
open KFCausalConformal4DRegularVolumeSmoothness KFCausalMinkowski4DMoments

def cutoff (p : ℝ × ℝ) : ℝ :=
  KFCausalBDG4DCompactProfile.profile (-p.1-p.2)*
    KFCausalBDG4DCompactProfile.profile (-p.1+p.2)

def cone : Set (ℝ × ℝ) := {p | p.1 < 0 ∧ 0 < p.2 ∧ p.2 < -p.1}

private def box : Set (ℝ × ℝ) := Icc (-3:ℝ) 3 ×ˢ Icc (-3:ℝ) 3

private theorem box_compact : IsCompact box := isCompact_Icc.prod isCompact_Icc

private theorem cutoff_continuous : Continuous cutoff := by
  unfold cutoff
  exact (KFCausalBDG4DCompactProfile.smooth.continuous.comp (by fun_prop)).mul
    (KFCausalBDG4DCompactProfile.smooth.continuous.comp (by fun_prop))

private theorem cutoff_zero (p : ℝ × ℝ) (hp : p ∉ box) : cutoff p=0 := by
  by_cases h1 : 3 ≤ |-p.1-p.2|
  · simp only [cutoff,(KFCausalBDG4DCompactProfile.outside_support _ h1).1,zero_mul]
  by_cases h2 : 3 ≤ |-p.1+p.2|
  · simp only [cutoff,(KFCausalBDG4DCompactProfile.outside_support _ h2).1,mul_zero]
  have h1' := abs_lt.mp (lt_of_not_ge h1)
  have h2' := abs_lt.mp (lt_of_not_ge h2)
  exact False.elim (hp ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩)

private theorem cutoff_compact : HasCompactSupport cutoff :=
  HasCompactSupport.intro box_compact cutoff_zero

private theorem cone_measurable : MeasurableSet cone := by
  exact (isOpen_lt continuous_fst continuous_const).measurableSet.inter
    ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd continuous_fst.neg).measurableSet)

theorem weighted_cutoff_integrable (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun p => g p*cutoff p) :=
  (hg.mul cutoff_continuous).integrable_of_hasCompactSupport cutoff_compact.mul_left

theorem cone_integral_eq_iterated (f : ℝ × ℝ → ℝ) (hf : Integrable f) :
    (∫ p in cone, f p) = ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), f (t,r) := by
  rw [← integral_indicator cone_measurable]
  have hi : Integrable (cone.indicator f) (volume.prod volume) :=
    hf.indicator cone_measurable
  change (∫ x, cone.indicator f x ∂volume.prod volume) = _
  rw [integral_prod _ hi,← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t < 0
  · rw [indicator_of_mem (show t ∈ Iio (0:ℝ) from ht),← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with r
    by_cases hr : r ∈ Ioo (0:ℝ) (-t)
    · simp [cone,ht,hr.1,hr.2]
    · simp only [mem_Ioo,not_and_or,not_lt] at hr
      rcases hr with hr | hr <;> simp [cone,ht,not_lt.mpr hr]
  · simp [cone,ht]

def integrand (rho c : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2^2*kernel rho c p.1 p.2*cutoff p

def slope (rho c : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2^2*kernelSlope rho c p.1 p.2*cutoff p

private theorem integrand_continuous (rho : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => integrand rho p.1 p.2) := by
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact kernel_continuous rho
  · exact cutoff_continuous.comp continuous_snd

private theorem slope_continuous (rho : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => slope rho p.1 p.2) := by
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact kernel_slope_continuous rho
  · exact cutoff_continuous.comp continuous_snd

theorem integrand_integrable (rho c : ℝ) : Integrable (integrand rho c) := by
  have hp : Continuous (fun p : ℝ × ℝ => (c,p)) := continuous_const.prodMk continuous_id
  have hk := (kernel_continuous rho).comp hp
  have hw := (continuous_snd.pow 2).mul hk
  exact weighted_cutoff_integrable (fun p : ℝ × ℝ => p.2^2*kernel rho c p.1 p.2) hw

theorem slope_integrable (rho c : ℝ) : Integrable (slope rho c) := by
  have hp : Continuous (fun p : ℝ × ℝ => (c,p)) := continuous_const.prodMk continuous_id
  have hk := (kernel_slope_continuous rho).comp hp
  have hw := (continuous_snd.pow 2).mul hk
  exact weighted_cutoff_integrable (fun p : ℝ × ℝ => p.2^2*kernelSlope rho c p.1 p.2) hw

private theorem integral_derivative (rho : ℝ) :
    HasDerivAt (fun c => ∫ p in cone, integrand rho c p) (∫ p in cone, slope rho 0 p) 0 := by
  obtain ⟨M,hM⟩ := ((isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).prod box_compact).exists_bound_of_continuousOn (slope_continuous rho).continuousOn
  have hb : Integrable (box.indicator (fun _ => M)) (volume.restrict cone) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff box_compact.measurableSet]
    exact integrableOn_const box_compact.measure_ne_top
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := integrand rho) (F' := slope rho)
    (Icc_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall (fun c =>
      (integrand_integrable rho c).integrableOn.aestronglyMeasurable))
    (integrand_integrable rho 0).integrableOn
    ((slope_integrable rho 0).integrableOn.aestronglyMeasurable) ?_ hb ?_).2
  · filter_upwards [] with p
    intro c hc
    by_cases hp : p ∈ box
    · rw [indicator_of_mem hp]
      exact hM (c,p) ⟨hc,hp⟩
    · simp only [slope,cutoff_zero p hp,mul_zero,norm_zero,indicator_of_notMem hp]
      exact le_rfl
  · filter_upwards [] with p
    intro c _
    exact ((kernel_hasDerivAt rho c p.1 p.2).const_mul (p.2^2)).mul_const (cutoff p)

def outerIntegral (rho c : ℝ) : ℝ :=
  ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
    r^2*density c t*f4D (rho*timelikeVolume c t r)*cutoff (t,r)

theorem outer_integral_eq_regular (rho c : ℝ) :
    outerIntegral rho c = ∫ p in cone, integrand rho c p := by
  rw [cone_integral_eq_iterated _ (integrand_integrable rho c)]
  apply setIntegral_congr_fun measurableSet_Iio
  intro t ht
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hq : 0<t^2-r^2 := by
    have ht' : t<0 := ht
    have hr' : 0<r ∧ r< -t := hr
    nlinarith
  dsimp only
  rw [timelike_eq_regular c t r hq]
  dsimp [integrand,kernel]
  ring

theorem outer_integral_hasDerivAt (rho : ℝ) :
    HasDerivAt (outerIntegral rho)
      (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), slope rho 0 (t,r)) 0 := by
  have he : outerIntegral rho = fun c => ∫ p in cone, integrand rho c p :=
    funext (outer_integral_eq_regular rho)
  rw [he,← cone_integral_eq_iterated _ (slope_integrable rho 0)]
  exact integral_derivative rho

#print axioms weighted_cutoff_integrable
#print axioms cone_integral_eq_iterated
#print axioms integrand_integrable
#print axioms slope_integrable
#print axioms outer_integral_eq_regular
#print axioms outer_integral_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalConformal4DCompactKernelDerivative
