/- Full charged-frequency L2 domains of the actual neutral Fourier
fields, including charged polynomial weights and frequency multiplication. -/
import UnifiedTheory.Audit.KFCausalJointFourierSpatialMoments
import UnifiedTheory.Audit.KFCausalChargedProductFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalJointFourierFrequencyDomain
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalNeutralLinePackets (step)

local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

def spatial (j : ℕ) (q : Charged) : ℝ → ℂ :=
  fieldLine n β b (coefficients n w c (chart α r (q.1.1^2+q.1.2^2) q.2)) P j
    (fieldSlope r*q.1.2) (2*r.im*q.1.2)

def amplitude (j : ℕ) (q : Charged × ℝ) : ℂ := 𝓕 (spatial n α β w b c P r j q.1) q.2

theorem spatial_continuous (j : ℕ) :
    Continuous (fun q : Charged × ℝ => spatial n α β w b c P r j q.1 q.2) := by
  unfold spatial fieldLine KFCausalNeutralFourierShift.line KFCausalGaussianContourShift.horizontal
    KFCausalNeutralLineDomain.family KFCausalNeutralLinePackets.entire coefficients chart
  fun_prop

theorem amplitude_measurable (j : ℕ) : StronglyMeasurable (amplitude n α β w b c P r j) := by
  have hc : Continuous (fun q : (Charged × ℝ) × ℝ =>
      (Real.fourierChar (-inner ℝ q.2 q.1.2):ℂ)*spatial n α β w b c P r j q.1.1 q.2) := by
    have hs := (spatial_continuous n α β w b c P r j).comp
      (show Continuous (fun q : (Charged × ℝ) × ℝ => (q.1.1,q.2)) by fun_prop)
    fun_prop
  simpa only [amplitude,Real.fourier_eq,Circle.smul_def,smul_eq_mul] using
    hc.stronglyMeasurable.integral_prod_right'

variable (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
  (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2)
include hβ hA hC

theorem spatial_marginal_integrable (m j : ℕ) :
    Integrable (fun q : Charged => ∫ x : ℝ, q.1.2^(2*m)*‖spatial n α β w b c P r j q x‖^2)
      chargedMeasure := by
  have hm : StronglyMeasurable (fun q : Charged =>
      ∫ x : ℝ, q.1.2^(2*m)*‖spatial n α β w b c P r j q x‖^2) := by
    have hc : Continuous (fun q : Charged × ℝ => q.1.1.2^(2*m)*
        ‖spatial n α β w b c P r j q.1 q.2‖^2) := by
      have hs := spatial_continuous n α β w b c P r j
      fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  apply KFCausalChargedProductFubini.integrable_of_ordered _ hm
  · intro q
    apply integral_nonneg
    intro x
    exact mul_nonneg (by rw [pow_mul]; positivity) (sq_nonneg _)
  · have hi := KFCausalJointFourierSpatialMoments.field_moment_integrable
      n α β w b c P r hβ hA hC m j
    simp_rw [KFCausalJointFourierDilationRepresentation.density_zero] at hi
    exact KFCausalJointNeutralFourierOuterFubini.joint_marginals_integrable _ hi

theorem amplitude_moment_integrable (m j : ℕ) :
    Integrable (fun q : Charged × ℝ => q.1.1.2^(2*m)*‖amplitude n α β w b c P r j q‖^2)
      (chargedMeasure.prod volume) := by
  have hm : AEStronglyMeasurable (fun q : Charged × ℝ =>
      q.1.1.2^(2*m)*‖amplitude n α β w b c P r j q‖^2) (chargedMeasure.prod volume) :=
    ((by fun_prop : Continuous (fun q : Charged × ℝ => q.1.1.2^(2*m))).stronglyMeasurable.mul
      ((amplitude_measurable n α β w b c P r j).norm.pow 2)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [] with q
    have hf : MemLp (𝓕 (spatial n α β w b c P r j q)) 2 volume :=
      KFCausalL2FourierIntegral.integralFourier_memLp _
        (KFCausalNeutralFourierField.fieldLine_integrable n β hβ b _ P j _ _)
        (KFCausalNeutralFourierField.fieldLine_memLp n β hβ b _ P j _ _)
    exact ((memLp_two_iff_integrable_sq_norm hf.1).mp hf).const_mul _
  · have hi := spatial_marginal_integrable n α β w b c P r hβ hA hC m j
    apply hi.congr
    filter_upwards [] with q
    have he := KFCausalNeutralFourierEnergy.field_plancherel n β b
      (coefficients n w c (chart α r (q.1.1^2+q.1.2^2) q.2)) P hβ j
      (fieldSlope r*q.1.2) (2*r.im*q.1.2)
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_norm]
    rw [show |q.1.2|^(2*m) = q.1.2^(2*m) by rw [pow_mul,pow_mul,sq_abs]]
    rw [integral_const_mul,integral_const_mul]
    congr 1
    simpa only [amplitude,spatial,KFCausalNeutralFourierEnergy.frequencyMoment,
      KFCausalNeutralFourierField.fieldLine_fourier_square n β hβ] using he

theorem amplitude_weighted_memLp (m j : ℕ) :
    MemLp (fun q : Charged × ℝ => (q.1.1.2:ℂ)^m*amplitude n α β w b c P r j q)
      2 (chargedMeasure.prod volume) := by
  have hm : AEStronglyMeasurable (fun q : Charged × ℝ =>
      (q.1.1.2:ℂ)^m*amplitude n α β w b c P r j q) (chargedMeasure.prod volume) :=
    ((by fun_prop : Continuous (fun q : Charged × ℝ => (q.1.1.2:ℂ)^m)).stronglyMeasurable.mul
      (amplitude_measurable n α β w b c P r j)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (amplitude_moment_integrable n α β w b c P r hβ hA hC m j).congr
  filter_upwards [] with q
  have hv : ‖(q.1.1.2:ℂ)^m‖^2 = q.1.1.2^(2*m) := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,← pow_mul,Nat.mul_comm m 2]
    rw [pow_mul,pow_mul,sq_abs]
  rw [norm_mul,mul_pow,hv]

theorem amplitude_frequency_memLp (j : ℕ) :
    MemLp (fun q : Charged × ℝ => (q.2:ℂ)*amplitude n α β w b c P r j q)
      2 (chargedMeasure.prod volume) := by
  have hs := amplitude_weighted_memLp n α β w b c (fun i => step β (b i) (P i)) r hβ hA hC 0 j
  have hl := amplitude_weighted_memLp n α β w b c P r hβ hA hC 0 (j-1)
  simp only [pow_zero,one_mul] at hs hl
  have hi := (hs.add (hl.const_mul (j:ℂ))).const_mul (1/(2*(Real.pi:ℂ)*Complex.I))
  convert hi using 1
  funext q
  have he := KFCausalNeutralFourierMomentum.step_fourier n β b
    (coefficients n w c (chart α r (q.1.1.1^2+q.1.1.2^2) q.1.2)) P hβ j
    (fieldSlope r*q.1.1.2) (2*r.im*q.1.1.2) q.2
  change (q.2:ℂ)*amplitude n α β w b c P r j q = _
  change amplitude n α β w b c (fun i => step β (b i) (P i)) r j q =
    (2*(Real.pi:ℂ)*Complex.I*(q.2:ℂ))*amplitude n α β w b c P r j q-
      (j:ℂ)*amplitude n α β w b c P r (j-1) q at he
  simp only [Pi.add_apply]
  rw [he]
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

#print axioms spatial_continuous
#print axioms amplitude_measurable
#print axioms spatial_marginal_integrable
#print axioms amplitude_moment_integrable
#print axioms amplitude_weighted_memLp
#print axioms amplitude_frequency_memLp
end
end UnifiedTheory.Audit.KFCausalJointFourierFrequencyDomain
