/- Whole-configuration integrability of the actual weak and reduced
Gaussian cross responses. Field weights of degrees zero, two and four
are included; all L2 inputs and bounded clock multipliers are derived. -/
import UnifiedTheory.Audit.KFCausalGaussianResponseDensities
import UnifiedTheory.Audit.KFCausalIntegratedGaussianBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient weakPair reduced)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_continuous inverseClock_bound)
open UnifiedTheory.Audit.KFCausalGaussianKernelResponse
  (kernel kernelDerivative transverse transverseSlope)
open UnifiedTheory.Audit.KFCausalGaussianResponseDensities
  (amplitude momentum slopeDensity amplitude_memLp momentum_memLp slopeDensity_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

def relativeInverse (ε y s : ℝ) : ℂ := inverseClock ε y s-(clock ε s:ℂ)⁻¹

private theorem clock_positive (ε s : ℝ) (hε : 0 < ε) : 0 < clock ε s := by
  unfold clock
  positivity

private theorem clock_continuous (ε : ℝ) : Continuous (clock ε) :=
  Real.continuous_exp.add continuous_const

private theorem real_inverse_bound (ε s : ℝ) (hε : 0 < ε) : ‖(clock ε s:ℂ)⁻¹‖ ≤ 1/ε := by
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (clock_positive ε s hε),← one_div]
  exact one_div_le_one_div_of_le hε (le_add_of_nonneg_left (Real.exp_nonneg s))

theorem relativeInverse_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖relativeInverse ε y s‖ ≤ 2/ε := by
  calc
    _ ≤ ‖inverseClock ε y s‖+‖(clock ε s:ℂ)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1/ε+1/ε := add_le_add (inverseClock_bound ε y s hε hy) (real_inverse_bound ε s hε)
    _ = _ := by ring

theorem relativeInverse_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (relativeInverse ε y) :=
  (inverseClock_continuous ε y hε hy).sub
    ((Complex.continuous_ofReal.comp (clock_continuous ε)).inv₀
      (fun s => Complex.ofReal_ne_zero.mpr (clock_positive ε s hε).ne'))

theorem coefficient_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖(coefficient ε y s:ℂ)‖ ≤ 4/ε := by
  have hi := inverseClock_bound ε y s hε hy
  have hu : ‖inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2‖ ≤ 2/ε := by
    calc
      _ ≤ ‖inverseClock ε y s‖+‖(ε:ℂ)*(inverseClock ε y s)^2‖ := norm_add_le _ _
      _ = ‖inverseClock ε y s‖+ε*‖inverseClock ε y s‖^2 := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
      _ ≤ 1/ε+ε*(1/ε)^2 := add_le_add hi
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi 2) hε.le)
      _ = _ := by field_simp; ring
  have hr : ‖(inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2).re‖ ≤ 2/ε := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hu
  have hc : ‖(2:ℝ)/clock ε s‖ ≤ 2/ε := by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by norm_num) (clock_positive ε s hε).le)]
    exact div_le_div_of_nonneg_left (by norm_num) hε (le_add_of_nonneg_left (Real.exp_nonneg s))
  rw [Complex.norm_real]
  exact (norm_sub_le _ _).trans ((add_le_add hc hr).trans_eq (by ring))

theorem coefficient_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (coefficient ε y) := by
  have hi := inverseClock_continuous ε y hε hy
  exact (continuous_const.div (clock_continuous ε) (fun s => (clock_positive ε s hε).ne')).sub
    (Complex.continuous_re.comp (hi.add (continuous_const.mul (hi.pow 2))))

private theorem bounded_mul_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (g : ℝ → ℂ) (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) :
    MemLp (fun x : Configuration => g x.1*f x) 2 volume :=
  hf.mul' (memLp_top_of_bound (hg.comp continuous_fst).aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun x => hM x.1)))

variable (ε y a a' p p' α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "Ai" => amplitude ε a α β p y b C l n
local notation "Aj" => amplitude ε a' α' β' p' y c D l n
local notation "Si" => slopeDensity ε a α β p y b C l n
local notation "Sj" => slopeDensity ε a' α' β' p' y c D l n

def weakDensity (x : Configuration) : ℂ :=
  (l x.2:ℂ)^(2*n.val)*kernel ε y α β α' β' b c C D x.2 x.1*weakPair ε a a' p p' y x.1

def reducedDensity (x : Configuration) : ℂ :=
  (l x.2:ℂ)^(2*n.val)*reduced ε a a' p p' y
    (kernel ε y α β α' β' b c C D x.2) (kernelDerivative ε y α β α' β' b c C D x.2) x.1

theorem weak_factorization (h : ℝ) (hh : h ≠ 0) (x : Configuration) :
    weakDensity ε y a a' p p' α β α' β' b c C D l n x =
      (Complex.I/(h:ℂ))*(star (Ai x)*momentum ε a' α' β' p' y h c D l n x-
        star (momentum ε a α β p y h b C l n x)*Aj x) := by
  have he := KFCausalGaussianKernelResponse.gaussian_response_factorization
    ε y h a a' p p' α β α' β' hh b c C D x.2 x.1
  dsimp only at he
  symm
  calc
    _ = (l x.2:ℂ)^(2*n.val)*((Complex.I/(h:ℂ))*
      (star (C*KFCausalRelativeGaussianDifferential.profile
        (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p y)
        (KFCausalClockFloorRelativeShift.scale ε y) α β b x)*
          ((-Complex.I*(h:ℂ))*KFCausalClockResponseTransport.weakSlope ε a' p' y x.1*
            (D*KFCausalRelativeGaussianDifferential.profile
              (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a' p' y)
              (KFCausalClockFloorRelativeShift.scale ε y) α' β' c x))-
       star ((-Complex.I*(h:ℂ))*KFCausalClockResponseTransport.weakSlope ε a p y x.1*
         (C*KFCausalRelativeGaussianDifferential.profile
           (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p y)
           (KFCausalClockFloorRelativeShift.scale ε y) α β b x))*
         (D*KFCausalRelativeGaussianDifferential.profile
           (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a' p' y)
           (KFCausalClockFloorRelativeShift.scale ε y) α' β' c x))) := by
      rw [show 2*n.val=n.val+n.val by omega,pow_add]
      simp only [momentum,amplitude,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
      ring
    _ = _ := by rw [he]; unfold weakDensity; ring

theorem reduced_factorization (hε : 0 < ε) (x : Configuration) :
    reducedDensity ε y a a' p p' α β α' β' b c C D l n x =
      star (Ai x)*((coefficient ε y x.1:ℂ)*Aj x-relativeInverse ε y x.1*Sj x)-
        star (relativeInverse ε y x.1*Si x)*Aj x := by
  have hc : (clock ε x.1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε).ne'
  unfold reducedDensity reduced kernelDerivative kernel transverseSlope transverse
    KFCausalClockResponseTransport.pair slopeDensity amplitude relativeInverse
    KFCausalRelativeGaussianDifferential.profile
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  simp only [one_mul,star_mul,star_sub,star_pow,star_inv₀,star_one,Complex.star_def,Complex.conj_ofReal]
  field_simp
  ring

variable (h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (ha : 0 < a) (ha' : 0 < a') (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hα' : 0 < α') (hβ' : 0 < β') (hw' : 32*β' ≤ α')

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem weakDensity_integrable :
    Integrable (weakDensity ε (-h/2) a a' p p' α β α' β' b c C D l n) volume := by
  have hi := amplitude_memLp ε a α β hε ha hα hβ hw C p b h hb l n
  have hj := amplitude_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n
  have hmi := momentum_memLp ε a α β hε ha hα hβ hw C p b h hb l n
  have hmj := momentum_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n
  apply (((hi.star.integrable_mul hmj).sub (hmi.star.integrable_mul hj)).const_mul
    (Complex.I/(h:ℂ))).congr
  filter_upwards [] with x
  exact (weak_factorization ε (-h/2) a a' p p' α β α' β' b c C D l n h hh x).symm

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem reducedDensity_integrable :
    Integrable (reducedDensity ε (-h/2) a a' p p' α β α' β' b c C D l n) volume := by
  have hy := shift_bound ε h hb
  have hi := amplitude_memLp ε a α β hε ha hα hβ hw C p b h hb l n
  have hj := amplitude_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n
  have hsi := slopeDensity_memLp ε a α β hε ha hα hβ hw C p b h hb l n hh
  have hsj := slopeDensity_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n hh
  have hri := bounded_mul_memLp _ hsi (relativeInverse ε (-h/2))
    (relativeInverse_continuous ε (-h/2) hε hy) (2/ε) (fun s => relativeInverse_bound ε (-h/2) s hε hy)
  have hrj := bounded_mul_memLp _ hsj (relativeInverse ε (-h/2))
    (relativeInverse_continuous ε (-h/2) hε hy) (2/ε) (fun s => relativeInverse_bound ε (-h/2) s hε hy)
  have hcj := bounded_mul_memLp _ hj (fun s => (coefficient ε (-h/2) s:ℂ))
    (Complex.continuous_ofReal.comp (coefficient_continuous ε (-h/2) hε hy)) (4/ε)
      (fun s => coefficient_bound ε (-h/2) s hε hy)
  apply ((hi.star.integrable_mul (hcj.sub hrj)).sub (hri.star.integrable_mul hj)).congr
  filter_upwards [] with x
  exact (reduced_factorization ε (-h/2) a a' p p' α β α' β' b c C D l n hε x).symm

#print axioms relativeInverse_bound
#print axioms relativeInverse_continuous
#print axioms coefficient_bound
#print axioms coefficient_continuous
#print axioms weak_factorization
#print axioms reduced_factorization
#print axioms weakDensity_integrable
#print axioms reducedDensity_integrable
end
end UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
