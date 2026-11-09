/- Exact positive shifted kernel for the four-term polynomial span.
Four explicit evaluations prove strict positivity for every nonzero
coefficient vector, including all destructive interference. -/
import UnifiedTheory.Audit.KFCausalQuarticSpanMoments
import UnifiedTheory.Audit.KFCausalQuarticChargeProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalQuarticSpanKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairCoordinates
open KFCausalQuarticSpanMoments
open KFCausalPairedSpanMoments (pairedCoordinate)
open KFCausalQuarticChargeProfiles (chargedRadius)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalRelativeGaussianDifferential (exponent)
open KFCausalMatterOrderedDomain (pointField)

def physicalBasis (i : Fin 4) (q : Transverse) : ℝ :=
  ![1,pairPolynomial q,(pairPolynomial q)^2,chargedRadius q] i
def physicalProfile (r : ℂ) (c : Coefficients) (q : Transverse) : ℂ :=
  ∑ i, coefficient c r i*(physicalBasis i q:ℂ)
def physicalDensity (α β : ℝ) (r : ℂ) (c : Coefficients) (q : Transverse) : ℝ :=
  potential (pointField q)*‖physicalProfile r c q*Complex.exp (exponent α β 0 r q)‖^2
def kernel (α β : ℝ) (r : ℂ) (c : Coefficients) : ℝ :=
  ∫ q, physicalDensity α β r c q

theorem basis_reconstruct (i : Fin 4) (r : ℂ) (u : Transverse) :
    physicalBasis i (reconstruct r u) = basis i u := by
  fin_cases i
  · rfl
  · exact pair_reconstruct r u
  · exact congrArg (fun x : ℝ => x^2) (pair_reconstruct r u)
  · change (u 0)^2+(u 1)^2+((u 2+u 3)/2)^2+((u 2-u 3)/2)^2 =
      (u 0)^2+(u 1)^2+((u 2)^2+(u 3)^2)/2
    ring

theorem profile_expansion (r : ℂ) (c : Coefficients) (u : Transverse) :
    profile r c u = c 0+c 1*r^2*(pairedCoordinate u:ℂ)+
      c 2*r^4*(pairedCoordinate u:ℂ)^2+c 3*r^2*(radialCoordinate u:ℂ) := by
  simp [profile,coefficient,degrees,basis,Fin.sum_univ_succ,add_assoc]

theorem density_reconstruct (α β : ℝ) (r : ℂ) (c : Coefficients) (u : Transverse) :
    physicalDensity α β r c (reconstruct r u) = density α β c r u := by
  simp only [physicalDensity,physicalProfile,basis_reconstruct,field_reconstruct,
    norm_mul,mul_pow,gaussian_norm_reconstruct,
    KFCausalChargedPairTransverseCoupling.gaussian_weight]
  unfold density profile KFCausalChargedPairPotentialKernel.widths
  ring

theorem kernel_formula (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    kernel α β r c = value α β r c := by
  rw [kernel,integral_coordinates r]
  simp_rw [density_reconstruct]
  rw [value_integral α β c r hA hB hβ]
  ring

theorem exists_nonzero_profile (r : ℂ) (c : Coefficients) (hr : r ≠ 0) (hc : c ≠ 0) :
    ∃ u : Transverse, profile r c u ≠ 0 := by
  by_contra! hz
  have h0 : c 0 = 0 := by
    simpa [profile_expansion,pairedCoordinate,radialCoordinate] using hz 0
  have h3 : c 3=0 := by
    have he := hz ![1,0,0,0,0]
    norm_num [profile_expansion,pairedCoordinate,radialCoordinate,h0,
      Matrix.cons_val_two,Matrix.cons_val_three] at he
    exact he.resolve_right hr
  have hp : c 1*r^2+c 2*r^4 = 0 := by
    have he := hz ![1,1,0,0,0]
    norm_num [profile_expansion,pairedCoordinate,radialCoordinate,h0,h3,
      Matrix.cons_val_two,Matrix.cons_val_three] at he
    exact he
  have hm : -(c 1*r^2)+c 2*r^4 = 0 := by
    have he := hz ![1,-1,0,0,0]
    norm_num [profile_expansion,pairedCoordinate,radialCoordinate,h0,h3,
      Matrix.cons_val_two,Matrix.cons_val_three] at he
    exact he
  have h1r : c 1*r^2=0 := by linear_combination (hp-hm)/2
  have h2r : c 2*r^4=0 := by linear_combination (hp+hm)/2
  have h1 : c 1=0 := (mul_eq_zero.mp h1r).resolve_right (pow_ne_zero 2 hr)
  have h2 : c 2=0 := (mul_eq_zero.mp h2r).resolve_right (pow_ne_zero 4 hr)
  apply hc
  funext i
  fin_cases i <;> assumption

theorem density_continuous (α β : ℝ) (r : ℂ) (c : Coefficients) :
    Continuous (density α β c r) := by
  have hp : Continuous (fun u : Transverse =>
      ‖profile r c u‖^2*potential (u 4+fieldSlope r*u 2)) := by
    simp only [profile_expansion]
    unfold pairedCoordinate radialCoordinate potential
    fun_prop
  exact hp.mul (KFCausalPolynomialGaussianIntegrals.weight_continuous 5 _)

theorem density_nonnegative (α β : ℝ) (r : ℂ) (c : Coefficients) (u : Transverse) :
    0 ≤ density α β c r u := by
  unfold density potential
  exact mul_nonneg (by positivity)
    (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u).le

theorem value_positive (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β)
    (hr : r ≠ 0) (hc : c ≠ 0) : 0 < value α β r c := by
  obtain ⟨u,hu⟩ := exists_nonzero_profile r c hr hc
  have hp : 0 < density α β c r u := by
    unfold density
    exact mul_pos (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hu))
      (show 0 < potential (u 4+fieldSlope r*u 2) by unfold potential; positivity))
      (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u)
  have hi : 0 < ∫ v, density α β c r v := integral_pos_of_integrable_nonneg_nonzero
    (f := density α β c r) (x := u)
    (density_continuous α β r c) (density_integrable α β c r hA hB hβ)
    (density_nonnegative α β r c) hp.ne'
  rw [value_integral α β c r hA hB hβ]
  exact div_pos hi (by norm_num)

theorem physicalProfile_smul (r : ℂ) (c : Coefficients) (z : ℂ) (q : Transverse) :
    physicalProfile r (z • c) q = z*physicalProfile r c q := by
  simp only [physicalProfile,coefficient,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem physicalDensity_smul (α β : ℝ) (r : ℂ) (c : Coefficients) (z : ℂ) (q : Transverse) :
    physicalDensity α β r (z • c) q = ‖z‖^2*physicalDensity α β r c q := by
  simp only [physicalDensity,physicalProfile_smul,mul_assoc,norm_mul,mul_pow]
  ring

theorem kernel_smul (α β : ℝ) (r : ℂ) (c : Coefficients) (z : ℂ) :
    kernel α β r (z • c) = ‖z‖^2*kernel α β r c := by
  simp_rw [kernel,physicalDensity_smul,integral_const_mul]

theorem kernel_zero (α β : ℝ) (r : ℂ) : kernel α β r 0 = 0 := by
  simp [kernel,physicalDensity,physicalProfile,coefficient]

theorem kernel_nonnegative (α β : ℝ) (r : ℂ) (c : Coefficients) :
    0 ≤ kernel α β r c := by
  apply integral_nonneg
  intro q
  unfold physicalDensity potential
  positivity

#print axioms basis_reconstruct
#print axioms profile_expansion
#print axioms density_reconstruct
#print axioms kernel_formula
#print axioms exists_nonzero_profile
#print axioms density_continuous
#print axioms density_nonnegative
#print axioms value_positive
#print axioms physicalProfile_smul
#print axioms physicalDensity_smul
#print axioms kernel_smul
#print axioms kernel_zero
#print axioms kernel_nonnegative
end
end UnifiedTheory.Audit.KFCausalQuarticSpanKernel
