/- Exact integration of the narrow charged plane after the neutral
coordinate has been integrated. The coefficients retain the quartic
potential, and the broad factor is the actual Laplace transform. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeLaplace
import UnifiedTheory.Audit.KFCausalReciprocalCrossKernel
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgePlane
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalComplexGaussianMoments (moment value gaussianValue)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalChargedPairCoordinates (fieldSlope)

def c0 (β : ℝ) : ℝ := 1+1/(8*β)+3/(64*β^2)
def c1 (β : ℝ) : ℝ := 1/2+3/(8*β)
def polynomial (β d u : ℝ) : ℝ := c0 β+c1 β*d^2*u^2+(1/4)*d^4*u^4
def monomial (b c : ℂ) (n : ℕ) (u : ℝ × ℝ) : ℂ :=
  moment b 0 u.1*moment c n u.2
def density (b c : ℂ) (β d : ℝ) (u : ℝ × ℝ) : ℂ :=
  (polynomial β d u.2:ℂ)*Complex.exp (-b*(u.1:ℂ)^2-c*(u.2:ℂ)^2)

theorem coefficients_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ c0 β ∧ 0 ≤ c1 β := by
  constructor <;> dsimp [c0,c1] <;> positivity

theorem polynomial_nonneg (β d u : ℝ) (hβ : 0 < β) : 0 ≤ polynomial β d u := by
  obtain ⟨h0,h1⟩ := coefficients_nonneg β hβ
  unfold polynomial
  positivity

theorem monomial_integrable (b c : ℂ) (hb : 0 < b.re) (hc : 0 < c.re) (n : ℕ) :
    Integrable (monomial b c n) := by
  exact (KFCausalComplexGaussianMoments.moment_integrable b hb 0).mul_prod
    (KFCausalComplexGaussianMoments.moment_integrable c hc n)

theorem monomial_integral (b c : ℂ) (n : ℕ) :
    (∫ u, monomial b c n u) = value b 0*value c n :=
  integral_prod_mul (moment b 0) (moment c n)

theorem density_decomposition (b c : ℂ) (β d : ℝ) (u : ℝ × ℝ) :
    density b c β d u = (c0 β:ℂ)*monomial b c 0 u+
      (c1 β:ℂ)*(d:ℂ)^2*monomial b c 2 u+(1/4:ℂ)*(d:ℂ)^4*monomial b c 4 u := by
  simp only [density,polynomial,monomial,moment,pow_zero,one_mul,sub_eq_add_neg,
    neg_mul,Complex.exp_add]
  push_cast
  ring

theorem density_integrable (b c : ℂ) (hb : 0 < b.re) (hc : 0 < c.re) (β d : ℝ) :
    Integrable (density b c β d) := by
  have hi := (((monomial_integrable b c hb hc 0).const_mul (c0 β:ℂ)).add
    ((monomial_integrable b c hb hc 2).const_mul ((c1 β:ℂ)*(d:ℂ)^2))).add
    ((monomial_integrable b c hb hc 4).const_mul ((1/4:ℂ)*(d:ℂ)^4))
  exact hi.congr (Filter.Eventually.of_forall (fun u => (density_decomposition b c β d u).symm))

theorem density_integral (b c : ℂ) (hb : 0 < b.re) (hc : 0 < c.re) (β d : ℝ) :
    (∫ u, density b c β d u) = gaussianValue b*gaussianValue c*
      ((c0 β:ℂ)+(c1 β:ℂ)*(d:ℂ)^2/(2*c)+3*(d:ℂ)^4/(16*c^2)) := by
  simp_rw [density_decomposition]
  have h0 := (monomial_integrable b c hb hc 0).const_mul (c0 β:ℂ)
  have h2 := (monomial_integrable b c hb hc 2).const_mul ((c1 β:ℂ)*(d:ℂ)^2)
  have h4 := (monomial_integrable b c hb hc 4).const_mul ((1/4:ℂ)*(d:ℂ)^4)
  have h02 : Integrable (fun u => (c0 β:ℂ)*monomial b c 0 u+
      (c1 β:ℂ)*(d:ℂ)^2*monomial b c 2 u) := h0.add h2
  rw [integral_add h02 h4,integral_add h0 h2]
  simp_rw [integral_const_mul,monomial_integral]
  rw [KFCausalComplexGaussianMoments.value_zero b hb,
    KFCausalComplexGaussianMoments.value_zero c hc,
    KFCausalComplexGaussianMoments.value_two c hc,
    KFCausalComplexGaussianMoments.value_four c hc]
  ring

theorem kernel_plane (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    KFCausalReciprocalCrossKernel.kernel α β w v r =
      ((Real.pi:ℂ)/4)*(w:ℂ)*(v:ℂ)*gaussianValue (2*(β:ℂ))*
        (∫ u, density (B α w v r) (C α β w v r) β (fieldSlope r) u)/conj (B α w v r) := by
  obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v r hw hv hA hC hβ
  rw [KFCausalReciprocalCrossKernel.kernel_formula α β w v r hw hv hA hC hβ,
    density_integral _ _ hb hc]
  unfold KFCausalReciprocalCrossKernel.formula KFCausalComplexPotentialGaussian.formula
    KFCausalComplexPotentialGaussian.variance
  rw [KFCausalReciprocalWedgeGeometry.broad_factor α w v (by linarith) (by linarith)]
  unfold c0 c1
  push_cast
  ring

def jointMeasure : Measure ((ℝ × ℝ) × ℝ) := volume.prod (volume.restrict (Set.Ioi 0))
def jointDensity (b c : ℂ) (β d : ℝ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  density b c β d p.1*Complex.exp (-conj b*(p.2:ℂ))

theorem joint_integrable (b c : ℂ) (hb : 0 < b.re) (hc : 0 < c.re) (β d : ℝ) :
    Integrable (jointDensity b c β d) jointMeasure :=
  (density_integrable b c hb hc β d).mul_prod
    (KFCausalReciprocalWedgeLaplace.laplace_integrable (conj b) (by simpa using hb))

theorem joint_integral (b c : ℂ) (hb : 0 < b.re) (β d : ℝ) :
    (∫ p, jointDensity b c β d p ∂jointMeasure) = (∫ u, density b c β d u)/conj b := by
  unfold jointDensity jointMeasure
  rw [integral_prod_mul (density b c β d) (fun y : ℝ => Complex.exp (-conj b*(y:ℂ))),
    KFCausalReciprocalWedgeLaplace.laplace_integral (conj b) (by simpa using hb)]
  ring

theorem kernel_joint (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    KFCausalReciprocalCrossKernel.kernel α β w v r =
      ((Real.pi:ℂ)/4)*gaussianValue (2*(β:ℂ))*(w:ℂ)*(v:ℂ)*
        ∫ p, jointDensity (B α w v r) (C α β w v r) β (fieldSlope r) p ∂jointMeasure := by
  obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v r hw hv hA hC hβ
  rw [joint_integral _ _ hb,kernel_plane α β w v r hw hv hA hC hβ]
  ring

#print axioms coefficients_nonneg
#print axioms polynomial_nonneg
#print axioms monomial_integrable
#print axioms monomial_integral
#print axioms density_decomposition
#print axioms density_integrable
#print axioms density_integral
#print axioms kernel_plane
#print axioms joint_integrable
#print axioms joint_integral
#print axioms kernel_joint
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgePlane
