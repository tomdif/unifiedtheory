/- Exact transport of the original compact curved-volume cone integral to
the flat kernel with the constructed smooth amplitude. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialPushforward
import UnifiedTheory.Audit.KFCausalConformal4DTransformedProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalConformal4DConePushforward
noncomputable section
open Real Set MeasureTheory
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DRadialJacobian KFCausalConformal4DRadialInverse
open KFCausalConformal4DRadialPushforward KFCausalConformal4DTransformedProfile
open KFCausalConformal4DCompactKernelDerivative
open KFCausalConformal4DTemporalVariation (density)

def domain (c : ℝ) : Set (ℝ×ℝ) :=
  {p | p∈cone ∧ p∈box ∧ radialMap c p∈targetBox}

private theorem cone_measurable : MeasurableSet cone :=
  (isOpen_lt continuous_fst continuous_const).measurableSet.inter
    ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd continuous_fst.neg).measurableSet)

private theorem radialMap_continuous (c : ℝ) : Continuous (radialMap c) := by
  have hi : Continuous (fun p : ℝ×ℝ => (c,p)) := continuous_const.prodMk continuous_id
  exact (((KFCausalConformal4DVolumeSmoothPolynomial.normalized_smooth.continuous.comp hi).sqrt).sqrt).smul
    continuous_id

theorem domain_measurable (c : ℝ) : MeasurableSet (domain c) :=
  cone_measurable.inter (box_open.measurableSet.inter
    (targetBox_open.preimage (radialMap_continuous c)).measurableSet)

theorem domain_image (c : ℝ) (hc : |c|≤1/54) :
    radialMap c '' domain c=cone∩targetBox := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(cone_iff c p (normalized_pos c p.1 p.2 hc hp.2.1.1.le hp.2.1.2.le)).2 hp.1,hp.2.2⟩
  · rintro ⟨hyc,hyt⟩
    let p := inverse c hc y
    have hp : p∈box := inverse_mem_box c hc y hyt
    have he : radialMap c p=y := inverse_right c hc y hyt
    refine ⟨p,⟨?_,hp,?_⟩,he⟩
    · apply (cone_iff c p (normalized_pos c p.1 p.2 hc hp.1.le hp.2.le)).1
      rwa [he]
    · rwa [he]

theorem cutoff_mem_domain (c : ℝ) (hc : |c|≤1/54) (p : ℝ×ℝ)
    (hp : p∈cone) (hn : cutoff p≠0) : p∈domain c := by
  have hb := cutoff_nonzero_bound p hn
  exact ⟨hp,⟨hb.1.trans_lt (by norm_num),hb.2.trans_lt (by norm_num)⟩,
    support_image_mem_target c hc p hb⟩

theorem amplitude_pullback (c : ℝ) (hc : |c|≤1/54) (p : ℝ×ℝ)
    (hp : p∈box) (hy : radialMap c p∈targetBox) :
    jacobianFactor c p.1 p.2*amplitude c hc (radialMap c p)=density c p.1*cutoff p := by
  rw [amplitude_eq c hc _ hy,inverse_left c hc p (box_subset_closedBox hp) hy]
  unfold coefficient
  have hn := (jacobian_factor_pos c p.1 p.2 hc hp.1.le hp.2.le).ne'
  field_simp

theorem outer_integral_transport (rho c : ℝ) (hc : |c|≤1/54) :
    outerIntegral rho c=∫ y in cone, flatKernel rho y*amplitude c hc y := by
  have hb : domain c⊆closedBox := fun _ hp => box_subset_closedBox hp.2.1
  have horig : (∫ p in cone, integrand rho c p)=∫ p in domain c, integrand rho c p := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero cone_measurable (fun _ hp => hp.1)
    intro p hp
    have hz : cutoff p=0 := by
      by_contra hn
      exact hp.2 (cutoff_mem_domain c hc p hp.1 hn)
    simp only [integrand,hz,mul_zero]
  have htarget : (∫ y in cone, flatKernel rho y*amplitude c hc y)=
      ∫ y in cone∩targetBox, flatKernel rho y*amplitude c hc y := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero cone_measurable inter_subset_left
    intro y hy
    have hn : y∉targetBox := fun hh => hy.2 ⟨hy.1,hh⟩
    simp only [amplitude,if_neg hn,mul_zero]
  rw [outer_integral_eq_regular,horig,htarget,← domain_image c hc,
    kernel_integral_image rho c hc (domain c) (domain_measurable c) hb]
  apply setIntegral_congr_fun (domain_measurable c)
  intro p hp
  dsimp only
  rw [mul_assoc,amplitude_pullback c hc p hp.2.1 hp.2.2]
  unfold integrand curvedKernel KFCausalConformal4DRegularVolumeSmoothness.kernel
  ring

theorem outer_integral_eq_flat_cone (rho c : ℝ) (hc : |c|≤1/54) :
    outerIntegral rho c=KFCausalMinkowski4DVariationCone.coneIntegral
      KFCausalMinkowski4DMoments.f4D (π*rho/24) (profile c hc) := by
  have hi : Integrable (fun y => flatKernel rho y*amplitude c hc y) := by
    apply Continuous.integrable_of_hasCompactSupport _ (amplitude_compact c hc).mul_left
    apply Continuous.mul _ (amplitude_smooth c hc).continuous
    unfold flatKernel KFCausalMinkowski4DMoments.f4D
    fun_prop
  rw [outer_integral_transport rho c hc,cone_integral_eq_iterated _ hi]
  unfold KFCausalMinkowski4DVariationCone.coneIntegral
  apply setIntegral_congr_fun measurableSet_Iio
  intro t _
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp only
  have he : nullMap (-t-r,-t+r)=(t,r) := by ext <;> dsimp [nullMap] <;> ring
  rw [profile,he]
  unfold flatKernel
  congr 2
  ring

#print axioms domain_measurable
#print axioms domain_image
#print axioms cutoff_mem_domain
#print axioms amplitude_pullback
#print axioms outer_integral_transport
#print axioms outer_integral_eq_flat_cone
end
end UnifiedTheory.Audit.KFCausalConformal4DConePushforward
