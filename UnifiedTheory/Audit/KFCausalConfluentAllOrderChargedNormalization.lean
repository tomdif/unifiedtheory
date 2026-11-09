/- Actual zero-phase charged-plane moments at every polynomial order. The
Gamma normalization is derived from Gaussian/Laplace moments and a finite
binomial identity. The resulting obstruction concerns a marginal coercivity
constant, not the full physical response. -/
import UnifiedTheory.Audit.KFCausalConfluentAllOrderCoercivityObstruction
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalConfluentAllOrderChargedNormalization
noncomputable section
open MeasureTheory Set
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingConfluentMoments (monomial monomial_integrable monomial_integral)
open KFCausalShiftedComplexGaussianMoments (normalized)
open KFCausalJointFourierBoundaryGammaForm (weight moment)
open KFCausalConfluentAllOrderCoercivityObstruction (scaledMoment)

private def halfMoment (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, ((k:ℝ)+1/2)

private theorem halfMoment_succ (n : ℕ) :
    halfMoment (n+1)=halfMoment n*((n:ℝ)+1/2) := by
  simp [halfMoment,Finset.prod_range_succ]

private theorem normalized_halfMoment (n : ℕ) :
    normalized 1 0 (2*n)=(halfMoment n:ℂ) := by
  induction n with
  | zero => norm_num [normalized,halfMoment]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,normalized,ih,halfMoment_succ]
    push_cast
    ring

private theorem moment_halfMoment (n : ℕ) :
    moment n=(2*(n:ℝ)+1)*halfMoment n := by
  induction n with
  | zero => norm_num [moment,halfMoment]
  | succ n ih =>
    rw [show moment (n+1)=moment n*((n:ℝ)+3/2) by
      simp [moment,Finset.prod_range_succ],ih,halfMoment_succ]
    push_cast
    ring

private theorem sum_halfMoment (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), halfMoment i/(i.factorial:ℝ))=
      (2*(n:ℝ)+1)*halfMoment n/(n.factorial:ℝ) := by
  induction n with
  | zero => norm_num [halfMoment]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,halfMoment_succ,Nat.factorial_succ]
    push_cast
    have hn : (n.factorial:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp

private theorem choose_halfMoment (n i : ℕ) (hi : i ≤ n) :
    (n.choose i:ℝ)*halfMoment i*((n-i).factorial:ℝ)=
      (n.factorial:ℝ)*(halfMoment i/(i.factorial:ℝ)) := by
  have he : (n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ)=(n.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i.factorial:ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination halfMoment i*he

private theorem convolution (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*halfMoment i*((n-i).factorial:ℝ))=moment n := by
  calc
    _ = (n.factorial:ℝ)*∑ i ∈ Finset.range (n+1),halfMoment i/(i.factorial:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact choose_halfMoment n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = _ := by
      rw [sum_halfMoment,moment_halfMoment]
      have hn : (n.factorial:ℝ) ≠ 0 := by positivity
      field_simp

def radial (n : ℕ) (q : ℝ × ℝ) : ℂ :=
  (((q.1:ℂ)^2+(q.2:ℂ))/2)^n*Complex.exp (-((q.1:ℂ)^2+(q.2:ℂ)))
def radialDensity (n : ℕ) (q : ℝ × ℝ) : ℝ :=
  Real.exp (-(q.1^2+q.2))*((q.1^2+q.2)/2)^n

def chargedEnergy (n : ℕ) : ℝ := ∫ q, radialDensity (2*n) q ∂planeMeasure
def chargedCooling (n : ℕ) : ℝ :=
  ∫ q, 2*radialDensity (2*n) q-2*(n:ℝ)*radialDensity (2*n-1) q ∂planeMeasure

theorem radial_expansion (n : ℕ) (q : ℝ × ℝ) :
    radial n q=∑ i ∈ Finset.range (n+1), ((n.choose i:ℂ)/(2:ℂ)^n)*monomial 1 i (n-i) q := by
  unfold radial
  rw [div_pow,add_pow,Finset.sum_div,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [monomial,Complex.ofReal_one,neg_mul,one_mul,← pow_mul]
  ring

theorem radial_integrable (n : ℕ) : Integrable (radial n) planeMeasure := by
  change Integrable (fun q => radial n q) planeMeasure
  simp_rw [radial_expansion]
  exact integrable_finset_sum _ (fun i _ =>
    (monomial_integrable 1 (by norm_num) i (n-i)).const_mul _)

theorem radial_integral_complex (n : ℕ) :
    (∫ q, radial n q ∂planeMeasure)=
      KFCausalComplexGaussianMoments.gaussianValue 1*(scaledMoment n:ℂ) := by
  simp_rw [radial_expansion]
  rw [integral_finset_sum _ (fun i _ =>
    (monomial_integrable 1 (by norm_num) i (n-i)).const_mul _)]
  simp_rw [integral_const_mul,monomial_integral 1 (by norm_num)]
  norm_num only [Complex.ofReal_one,one_pow,div_one]
  simp_rw [normalized_halfMoment]
  have hc := congrArg (fun x : ℝ => (x:ℂ)) (convolution n)
  push_cast at hc
  calc
    _ = (KFCausalComplexGaussianMoments.gaussianValue 1/(2:ℂ)^n)*
        ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*(halfMoment i:ℂ)*((n-i).factorial:ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hc]; unfold scaledMoment; push_cast; ring

theorem radial_density_complex (n : ℕ) (q : ℝ × ℝ) :
    radial n q=(radialDensity n q:ℂ) := by
  unfold radial radialDensity
  push_cast
  ring

theorem radial_density_integrable (n : ℕ) : Integrable (radialDensity n) planeMeasure := by
  have hi := (radial_integrable n).re
  simpa only [radial_density_complex,Complex.ofReal_re] using hi

theorem radial_density_integral (n : ℕ) :
    (∫ q, radialDensity n q ∂planeMeasure)=
      2*(∫ t in Ioi (0:ℝ),weight t*(t/2)^n) := by
  have hr := integral_re (radial_integrable n)
  change (∫ q, (radial n q).re ∂planeMeasure)=(∫ q, radial n q ∂planeMeasure).re at hr
  have he : (fun q => (radial n q).re)=radialDensity n := by
    funext q
    rw [radial_density_complex,Complex.ofReal_re]
  rw [he] at hr
  rw [hr,radial_integral_complex]
  have hg := KFCausalChargedCoolingConfluentPolynomialDerivative.gaussian_mass_real
    1 (by norm_num)
  norm_num at hg
  rw [hg]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [KFCausalConfluentAllOrderCoercivityObstruction.scaled_moment_integral]
  have hG := Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0)
  norm_num only [show (1/2:ℝ)+1=3/2 by norm_num] at hG
  rw [Real.Gamma_one_half_eq] at hG
  rw [hG]
  ring

theorem charged_cooling_integrable (n : ℕ) :
    Integrable (fun q => 2*radialDensity (2*n) q-2*(n:ℝ)*radialDensity (2*n-1) q)
      planeMeasure :=
  ((radial_density_integrable (2*n)).const_mul 2).sub
    ((radial_density_integrable (2*n-1)).const_mul (2*(n:ℝ)))

theorem charged_energy_gamma (n : ℕ) :
    chargedEnergy n=2*KFCausalConfluentAllOrderCoercivityObstruction.energy n := by
  exact radial_density_integral (2*n)

theorem charged_cooling_gamma (n : ℕ) :
    chargedCooling n=2*KFCausalConfluentAllOrderCoercivityObstruction.cooling n := by
  rw [chargedCooling,integral_sub ((radial_density_integrable _).const_mul _)
    ((radial_density_integrable _).const_mul _)]
  simp only [integral_const_mul,radial_density_integral,
    KFCausalConfluentAllOrderCoercivityObstruction.scaled_moment_integral]
  rw [KFCausalConfluentAllOrderCoercivityObstruction.cooling_integral]
  ring

theorem charged_energy_positive (n : ℕ) : 0 < chargedEnergy n := by
  rw [charged_energy_gamma]
  exact mul_pos (by norm_num)
    (KFCausalConfluentAllOrderCoercivityObstruction.energy_positive n)

theorem charged_exact_quotient (n : ℕ) :
    chargedCooling n=(2/(4*(n:ℝ)+1))*chargedEnergy n := by
  rw [charged_cooling_gamma,charged_energy_gamma,
    KFCausalConfluentAllOrderCoercivityObstruction.exact_quotient]
  ring

theorem no_uniform_charged_coercivity :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*chargedEnergy n ≤ chargedCooling n := by
  rintro ⟨c,hc,h⟩
  obtain ⟨n,hn⟩ := KFCausalConfluentAllOrderCoercivityObstruction.exists_strict_loss c hc
  have h0 := h n
  rw [charged_energy_gamma,charged_cooling_gamma] at h0
  linarith

#print axioms radial_expansion
#print axioms radial_integrable
#print axioms radial_integral_complex
#print axioms radial_density_complex
#print axioms radial_density_integrable
#print axioms radial_density_integral
#print axioms charged_cooling_integrable
#print axioms charged_energy_gamma
#print axioms charged_cooling_gamma
#print axioms charged_energy_positive
#print axioms charged_exact_quotient
#print axioms no_uniform_charged_coercivity
end
end UnifiedTheory.Audit.KFCausalConfluentAllOrderChargedNormalization
