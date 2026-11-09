/- Imaginary-geometry differentiation of the original common-real-source
joint energy. Local strict margins and the derivative are derived from
the finite sourced kernel. The lower bound uses proved finite increments,
not differentiation of an infinite series. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedKernel
import UnifiedTheory.Audit.KFCausalCommonRealGaussianImaginaryDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedImaginaryDerivative
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedEvenMomentFamily (packet)

open KFCausalCommonRealGaussianImaginaryDerivative (line)
variable (mass2 quartic vacuum : ℝ)
def value (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ) : ℝ :=
  ∫ z, KFCausalCommonRealGaussianWeightedJointEnergy.density mass2 quartic vacuum
    n α β B w (line a b) c z ∂jointMeasure
def slope (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ) : ℝ :=
  (KFCausalGaussianWeightedSourceKernelDerivative.familySlope mass2 quartic vacuum n α β w (line a b) Complex.I
    (fun _ => (B:ℂ)) c).re

private theorem line_re (a b : ℝ) : (line a b).re=a := by simp [line]
private theorem line_im (a b : ℝ) : (line a b).im=b := by simp [line]
private theorem line_area (a b : ℝ) : KFCausalReciprocalGaussianCoordinates.area (line a b)=a^2-b^2 := by
  simp [KFCausalReciprocalGaussianCoordinates.area,line_re,line_im]
private theorem gamma_re (α a b : ℝ) : 2*(gamma α (line a b)).re=α*(a^2-b^2) := by
  simp [gamma,line,pow_two,Complex.mul_re,Complex.mul_im]
  ring

private theorem margins_eventually (n : ℕ) (α β a b : ℝ) (w : Fin n → ℝ)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i) :
    ∀ᶠ t : ℝ in 𝓝 b, ∀ i, 8*β*t^2 < α*(a^2-t^2)*w i := by
  apply eventually_all.mpr
  intro i
  have hc : ContinuousAt (fun t : ℝ => α*(a^2-t^2)*w i-8*β*t^2) b := by fun_prop
  have he := hc.eventually (lt_mem_nhds (show 0 < α*(a^2-b^2)*w i-8*β*b^2 by linarith [hd i]))
  filter_upwards [he] with t ht
  linarith

private theorem original_floors (n : ℕ) (α β a b : ℝ) (w : Fin n → ℝ)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i) :
    ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area (line a b)-8*β*(line a b).im^2 := by
  intro i
  rw [line_area,line_im]
  nlinarith [hd i]

theorem value_nonnegative (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ value mass2 quartic vacuum n α β a B w c b :=
  integral_nonneg (fun z => KFCausalCommonRealGaussianWeightedJointEnergy.density_nonnegative
    mass2 quartic vacuum n α β B w (line a b) c z hm hq hv)

theorem value_eq_energy (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i, 0 < w i) (hb : |b| < a)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    value mass2 quartic vacuum n α β a B w c b =
      KFCausalCommonRealGaussianWeightedEnergy.energy mass2 quartic vacuum β B (3-2*a)
        (gamma α (line a b)) (8*β*b^2) w (fun i => c i*(w i:ℂ)) := by
  have hp : 0 < (gamma α (line a b)).re :=
    KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα (by simpa [line_re,line_im] using hb)
  have hi := KFCausalCommonRealGaussianWeightedJointEnergy.joint_integral_eq_energy
    mass2 quartic vacuum n α β B w (line a b) c hβ hp hw
    (fun i => by rw [line_im,gamma_re]; exact hd i) hm hq hv
  simpa only [value,KFCausalChargedPairCoordinates.fieldSlope,line_re,line_im] using hi

theorem value_eq_kernel (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i, 0 < w i) (hb : |b| < a)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    value mass2 quartic vacuum n α β a B w c b =
      (KFCausalGaussianWeightedSourceKernelDerivative.familyForm mass2 quartic vacuum
        n α β w (line a b) (fun _ => (B:ℂ)) c).re := by
  have hp : 0 < (gamma α (line a b)).re :=
    KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα (by simpa [line_re,line_im] using hb)
  have hi := KFCausalCommonRealGaussianWeightedKernel.joint_integral_eq_family
    mass2 quartic vacuum n α β B w (line a b) c hβ hp hw
    (fun i => by rw [line_im,gamma_re]; exact hd i) hm hq hv
  exact congrArg Complex.re hi

theorem value_hasDerivAt (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i, 0 < w i) (hb : |b| < a)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    HasDerivAt (value mass2 quartic vacuum n α β a B w c)
      (slope mass2 quartic vacuum n α β a B w c b) b := by
  have hr : HasDerivAt (line a) Complex.I b := by
    change HasDerivAt (fun t : ℝ => (a:ℂ)+Complex.I*(t:ℂ)) Complex.I b
    convert (((hasDerivAt_id b).ofReal_comp).const_mul Complex.I).const_add (a:ℂ) using 1
    norm_num
  have hf := original_floors n α β a b w hd
  have hh := KFCausalGaussianWeightedSourceKernelDerivative.familyForm_derivative mass2 quartic vacuum
    hr n α β w (fun _ => (B:ℂ)) c
    (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) (line a b) hβ (hf i) (hf j)).1)
    (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) (line a b) hβ (hf i) (hf j)).2)
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt b hh
  change HasDerivAt (fun t => (KFCausalGaussianWeightedSourceKernelDerivative.familyForm
    mass2 quartic vacuum n α β w (line a t) (fun _ => (B:ℂ)) c).re)
    (slope mass2 quartic vacuum n α β a B w c b) b at hreal
  apply hreal.congr_of_eventuallyEq
  have he : ∀ᶠ t : ℝ in 𝓝 b, |t| < a := continuous_abs.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [margins_eventually n α β a b w hd,he] with t ht htabs
  exact value_eq_kernel mass2 quartic vacuum n α β a B w c t hα hβ hw htabs ht hm hq hv

theorem positive_lower (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i, 0 < w i) (hb : 0 < b) (hba : b < a)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    -2*value mass2 quartic vacuum n α β a B w c b ≤ b*deriv (value mass2 quartic vacuum n α β a B w c) b := by
  let S : Set ℝ := {t | 0 < t ∧ t < a ∧ ∀ i, 8*β*t^2 < α*(a^2-t^2)*w i}
  have hS : S ∈ 𝓝 b := by
    filter_upwards [eventually_gt_nhds hb,eventually_lt_nhds hba,margins_eventually n α β a b w hd] with t ht0 hta ht
    exact ⟨ht0,hta,ht⟩
  have hm : MonotoneOn (fun t => t^2*value mass2 quartic vacuum n α β a B w c t) S := by
    intro b₁ hb₁ b₂ hb₂ hle
    dsimp only
    rw [value_eq_energy mass2 quartic vacuum n α β a B w c b₁ hα hβ hw (by simpa [abs_of_pos hb₁.1] using hb₁.2.1) hb₁.2.2 hmass hquartic hvacuum,
      value_eq_energy mass2 quartic vacuum n α β a B w c b₂ hα hβ hw (by simpa [abs_of_pos hb₂.1] using hb₂.2.1) hb₂.2.2 hmass hquartic hvacuum]
    exact KFCausalCommonRealGaussianWeightedEnergy.actual_scaled_le mass2 quartic vacuum α a β B (3-2*a) b₁ b₂ hα hβ
      hb₁.1 hle hb₂.2.1 w hw (fun i => c i*(w i:ℂ)) hb₂.2.2 hmass hquartic hvacuum
  have hn : 0 ≤ derivWithin (fun t => t^2*value mass2 quartic vacuum n α β a B w c t) S b := hm.derivWithin_nonneg
  rw [derivWithin_of_mem_nhds hS] at hn
  have hh := value_hasDerivAt mass2 quartic vacuum n α β a B w c b hα hβ hw (by simpa [abs_of_pos hb] using hba) hd hmass hquartic hvacuum
  have hprod := ((hasDerivAt_id b).pow 2).mul hh
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] at hprod
  change HasDerivAt (fun t => t^2*value mass2 quartic vacuum n α β a B w c t)
    (2*b*value mass2 quartic vacuum n α β a B w c b+b^2*slope mass2 quartic vacuum n α β a B w c b) b at hprod
  rw [hprod.deriv] at hn
  rw [hh.deriv]
  have hz : 0 ≤ b*(2*value mass2 quartic vacuum n α β a B w c b+b*slope mass2 quartic vacuum n α β a B w c b) := by nlinarith [hn]
  have hz' := (mul_nonneg_iff_of_pos_left hb).mp hz
  linarith

private theorem packet_conjugate (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (y : KFCausalChargedFourierGaussianMoments.Charged) :
    packet 0 (conj p) w c y = conj (packet 0 p w (fun i => conj (c i)) y) := by
  simp only [KFCausalChargedEvenMomentFamily.packet_expansion,pow_zero,one_mul,
    map_sum,map_mul,← Complex.exp_conj,map_neg,map_add,map_pow,Complex.conj_ofReal,
    Complex.conj_conj]

theorem conjugate_value (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ) :
    value mass2 quartic vacuum n α β a B w c (-b) = value mass2 quartic vacuum n α β a B w (fun i => conj (c i)) b := by
  have hg : gamma α (line a (-b))=conj (gamma α (line a b)) := by
    simp [gamma,line,map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I,Complex.conj_ofNat]
  unfold value
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  rcases z with ⟨⟨u,q⟩,Y⟩
  have hq : q = ![q 0,q 1] := by ext i; fin_cases i <;> rfl
  rw [hq,KFCausalCommonRealGaussianWeightedJointEnergy.density_factor,
    KFCausalCommonRealGaussianWeightedJointEnergy.density_factor,hg,packet_conjugate,Complex.norm_conj]
  simp only [KFCausalChargedPairCoordinates.fieldSlope,line_re,line_im,neg_sq,
    map_mul,Complex.conj_ofReal]

theorem imaginary_lower (n : ℕ) (α β a B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i, 0 < w i) (hb : |b| < a)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    -2*value mass2 quartic vacuum n α β a B w c b ≤ b*deriv (value mass2 quartic vacuum n α β a B w c) b := by
  rcases lt_trichotomy b 0 with hneg|hzero|hpos
  · have hmargin : ∀ i, 8*β*(-b)^2 < α*(a^2-(-b)^2)*w i := by simpa only [neg_sq] using hd
    have hh := value_hasDerivAt mass2 quartic vacuum n α β a B w (fun i => conj (c i)) (-b) hα hβ hw (by simpa only [abs_neg] using hb) hmargin hmass hquartic hvacuum
    have hc := hh.comp b (hasDerivAt_neg b)
    have he : (fun t => value mass2 quartic vacuum n α β a B w (fun i => conj (c i)) (-t)) = value mass2 quartic vacuum n α β a B w c := by
      funext t
      rw [conjugate_value]
      simp only [Complex.conj_conj]
    change HasDerivAt (fun t => value mass2 quartic vacuum n α β a B w (fun i => conj (c i)) (-t)) _ b at hc
    rw [he] at hc
    have hlo := positive_lower mass2 quartic vacuum n α β a B w (fun i => conj (c i)) (-b) hα hβ hw
      (by linarith) (by simpa only [abs_of_neg hneg] using hb) hmargin hmass hquartic hvacuum
    have hv := conjugate_value mass2 quartic vacuum n α β a B w (fun i => conj (c i)) b
    simp only [Complex.conj_conj] at hv
    rw [hv,hh.deriv] at hlo
    rw [hc.deriv]
    nlinarith
  · subst b
    simp only [zero_mul]
    linarith [value_nonnegative mass2 quartic vacuum n α β a B w c 0 hmass hquartic hvacuum]
  · exact positive_lower mass2 quartic vacuum n α β a B w c b hα hβ hw hpos
      (by simpa only [abs_of_pos hpos] using hb) hd hmass hquartic hvacuum

#print axioms value_nonnegative
#print axioms value_eq_energy
#print axioms value_eq_kernel
#print axioms value_hasDerivAt
#print axioms positive_lower
#print axioms conjugate_value
#print axioms imaginary_lower
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedImaginaryDerivative
