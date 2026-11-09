/- Actual finite charged packets, with all coherent width cross terms,
have an all-order even-moment imaginary-variation lower bound. -/
import UnifiedTheory.Audit.KFCausalChargedEvenMomentImaginaryBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedEvenMomentFamily
noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology BigOperators ComplexConjugate
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re actual_gamma_re_positive)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure density)
open KFCausalChargedFourierPolynomialGram (atom)
open KFCausalChargedEvenMomentImaginaryBound (kernel slope gamma gammaSlope momentConstant form)

variable {ι : Type*} [Fintype ι]

def packet (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℂ :=
  ∑ i, c i*atom p (w i) 0 l x.1.1 x.1.2 x.2

def energy (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, ‖packet l p w c x‖^2 ∂chargedMeasure

theorem packet_expansion (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    packet l p w c x = (x.1.2:ℂ)^l*
      ∑ i, c i*Complex.exp (-(w i:ℂ)*(p*((x.1.1:ℂ)^2+(x.1.2:ℂ)^2)+conj p*(x.2:ℂ))) := by
  unfold packet atom
  simp only [Complex.ofReal_zero,zero_div,zero_mul,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show -(w i:ℂ)*p*((x.1.1:ℂ)^2+(x.1.2:ℂ)^2)-(w i:ℂ)*conj p*(x.2:ℂ) =
    -(w i:ℂ)*(p*((x.1.1:ℂ)^2+(x.1.2:ℂ)^2)+conj p*(x.2:ℂ)) by ring]
  ring

private theorem cross (l : ℕ) (p : ℂ) (w z : ℝ) (x : Charged) :
    conj (atom p z 0 l x.1.1 x.1.2 x.2)*atom p w 0 l x.1.1 x.1.2 x.2 =
      density (widthSum p w z) (widthSum (conj p) w z) 0 (2*l) x.1.1 x.1.2 x.2 := by
  rw [KFCausalChargedFourierPolynomialGram.atom_cross]
  have hS : KFCausalChargedFourierPolynomialGram.width p z w = widthSum p w z := by
    unfold KFCausalChargedFourierPolynomialGram.width widthSum
    ring
  have hT : conj (widthSum p w z)=widthSum (conj p) w z := by simp [widthSum]
  rw [hS,hT,show l+l=2*l by omega]
  rfl

theorem packet_square (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    ((‖packet l p w c x‖^2:ℝ):ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*density (widthSum p (w i) (w j))
        (widthSum (conj p) (w i) (w j)) 0 (2*l) x.1.1 x.1.2 x.2 := by
  rw [Complex.ofReal_pow,← Complex.conj_mul']
  unfold packet
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← cross]
  ring

omit [Fintype ι] in
private theorem cross_integrable (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (i j : ι) :
    Integrable (fun x : Charged => (c i*conj (c j))*
      density (widthSum p (w i) (w j)) (widthSum (conj p) (w i) (w j))
        0 (2*l) x.1.1 x.1.2 x.2) chargedMeasure := by
  have hS : 0 < (widthSum p (w i) (w j)).re := by
    rw [widthSum_re]; exact mul_pos hp (add_pos (hw i) (hw j))
  have hT : 0 < (widthSum (conj p) (w i) (w j)).re := by
    rw [widthSum_re,Complex.conj_re]; exact mul_pos hp (add_pos (hw i) (hw j))
  exact (KFCausalChargedFourierGaussianMoments.density_integrable _ _ _ hS hT _).const_mul _

theorem packet_square_integrable (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    Integrable (fun x : Charged => ((‖packet l p w c x‖^2:ℝ):ℂ)) chargedMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable l p w c hp hw i j))
  exact hi.congr (Eventually.of_forall (fun x => (packet_square l p w c x).symm))

theorem packet_moment_integral (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    (∫ x : Charged, ((‖packet l p w c x‖^2:ℝ):ℂ) ∂chargedMeasure) =
      (momentConstant l:ℂ)*form l p w (star c) := by
  simp_rw [packet_square]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => cross_integrable l p w c hp hw i j))]
  simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,Complex.star_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => cross_integrable l p w c hp hw i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  have hS : 0 < (widthSum p (w i) (w j)).re := by
    rw [widthSum_re]; exact mul_pos hp (add_pos (hw i) (hw j))
  have hT : 0 < (widthSum (conj p) (w i) (w j)).re := by
    rw [widthSum_re,Complex.conj_re]; exact mul_pos hp (add_pos (hw i) (hw j))
  rw [KFCausalChargedFourierPolynomialGram.product_integral_order _
    (KFCausalChargedFourierGaussianMoments.density_integrable _ _ _ hS hT _)]
  change _*KFCausalChargedFourierGaussianMoments.integral _ _ _ _ = _
  rw [KFCausalChargedEvenMomentImaginaryBound.even_integral _ _ hS hT]
  unfold kernel
  simp only [Complex.conj_conj]
  ring

theorem energy_eq_form (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    energy l p w c = momentConstant l*(form l p w (star c)).re := by
  have h := congrArg Complex.re (packet_moment_integral l p w c hp hw)
  change RCLike.re (∫ x : Charged, ((‖packet l p w c x‖^2:ℝ):ℂ) ∂chargedMeasure) = _ at h
  rw [← integral_re (packet_square_integrable l p w c hp hw)] at h
  simpa only [energy,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] using h

theorem energy_nonnegative (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) :
    0 ≤ energy l p w c := integral_nonneg (fun _ => sq_nonneg _)

theorem actual_energy_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) :
    HasDerivAt (fun t : ℝ => energy l (gamma α (r+Complex.I*(t:ℂ))) w c)
      (momentConstant l*(star (star c) ⬝ᵥ
        ((fun i j => slope l (gamma α r) (gammaSlope α r) (w i) (w j)) *ᵥ star c)).re) 0 := by
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (KFCausalChargedEvenMomentImaginaryBound.actual_form_derivative α r hα hr l w hw (star c))).const_mul (momentConstant l)
  apply hd.congr_of_eventuallyEq
  have hp : 0 < (gamma α r).re := actual_gamma_re_positive α r hα hr
  have hc : ContinuousAt (fun t : ℝ => (gamma α (r+Complex.I*(t:ℂ))).re) 0 := by
    exact Complex.continuous_re.continuousAt.comp
      (KFCausalChargedEvenMomentImaginaryBound.imaginary_gamma_derivative α r).continuousAt
  have he : ∀ᶠ t : ℝ in 𝓝 0, 0 < (gamma α (r+Complex.I*(t:ℂ))).re :=
    hc.eventually (lt_mem_nhds (by simpa using hp))
  filter_upwards [he] with t ht
  exact energy_eq_form l _ w c ht hw

theorem actual_energy_derivative_lower (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) :
    -((l+2:ℝ)/2)*energy l (gamma α r) w c ≤
      r.im*deriv (fun t : ℝ => energy l (gamma α (r+Complex.I*(t:ℂ))) w c) 0 := by
  rw [(actual_energy_derivative α r hα hr l w hw c).deriv,
    energy_eq_form l (gamma α r) w c (actual_gamma_re_positive α r hα hr) hw]
  have h := KFCausalChargedEvenMomentImaginaryBound.actual_form_derivative_lower α r hα hr l w hw (star c)
  rw [(KFCausalChargedEvenMomentImaginaryBound.actual_form_derivative α r hα hr l w hw (star c)).deriv] at h
  have hc := KFCausalChargedEvenMomentImaginaryBound.momentConstant_positive l
  nlinarith

#print axioms packet_expansion
#print axioms packet_square
#print axioms packet_square_integrable
#print axioms packet_moment_integral
#print axioms energy_eq_form
#print axioms energy_nonnegative
#print axioms actual_energy_derivative
#print axioms actual_energy_derivative_lower
end
end UnifiedTheory.Audit.KFCausalChargedEvenMomentFamily
