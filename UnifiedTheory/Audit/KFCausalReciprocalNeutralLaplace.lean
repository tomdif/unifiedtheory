/- A common Laplace lift of the joint neutral cross kernel. The neutral
coordinate is retained, and the broad charged factor is represented by
an absolutely integrable half-line exponential. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPlaneIntegrability
import UnifiedTheory.Audit.KFCausalReciprocalWedgeLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralLaplace
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralKernel (neutral planeDensity kernel)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalComplexGaussianMoments (moment value gaussianValue)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalChargedPairCoordinates (fieldSlope)

abbrev Joint := (ℝ × (Fin 2 → ℝ)) × ℝ
def jointMeasure : Measure Joint := volume.prod (volume.restrict (Set.Ioi 0))

def jointDensity (β : ℝ) (b c r : ℂ) (F G : ℂ → ℂ) (p : Joint) : ℂ :=
  (Complex.exp (-b*(p.1.1:ℂ)^2)*planeDensity β c r F G p.1.2)*Complex.exp (-conj b*(p.2:ℂ))

theorem joint_integrable (β : ℝ) (b c r : ℂ) (F G : ℂ → ℂ) (hb : 0 < b.re)
    (hi : Integrable (planeDensity β c r F G)) :
    Integrable (jointDensity β b c r F G) jointMeasure := by
  have hg : Integrable (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2)) := by
    have he : (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2)) = moment b 0 := by
      funext u
      simp [moment]
    rw [he]
    exact KFCausalComplexGaussianMoments.moment_integrable b hb 0
  exact (hg.mul_prod hi).mul_prod
    (KFCausalReciprocalWedgeLaplace.laplace_integrable (conj b) (by simpa using hb))

theorem joint_integral (β : ℝ) (b c r : ℂ) (F G : ℂ → ℂ) (hb : 0 < b.re) :
    (∫ p, jointDensity β b c r F G p ∂jointMeasure) =
      gaussianValue b*(∫ u, planeDensity β c r F G u)/conj b := by
  unfold jointDensity jointMeasure
  rw [integral_prod_mul (fun p : ℝ × (Fin 2 → ℝ) =>
      Complex.exp (-b*(p.1:ℂ)^2)*planeDensity β c r F G p.2)
    (fun y : ℝ => Complex.exp (-conj b*(y:ℂ))),
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ),
    integral_prod_mul (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2)) (planeDensity β c r F G),
    KFCausalReciprocalWedgeLaplace.laplace_integral (conj b) (by simpa using hb)]
  have he := KFCausalComplexGaussianMoments.value_zero b hb
  simp only [value,moment,pow_zero,one_mul] at he
  rw [he]
  ring

theorem kernel_joint (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (hA : 0 < (A α w v r).re) (hB : 0 < (B α w v r).re) :
    kernel α β w v r F G = ((Real.pi:ℂ)/4)*(w:ℂ)*(v:ℂ)*
      ∫ p, jointDensity β (B α w v r) (C α β w v r) r F G p ∂jointMeasure := by
  rw [KFCausalReciprocalNeutralKernel.kernel_gaussian_marginal α β w v hw hv r F G hA hB,
    KFCausalReciprocalWedgeGeometry.broad_factor α w v hw hv,joint_integral _ _ _ _ _ _ hB]
  ring

def weight (β : ℝ) (r : ℂ) (p : Joint) : ℝ :=
  potential (p.1.2 1+fieldSlope r*p.1.2 0)*
    Real.exp (-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2)

theorem weight_positive (β : ℝ) (r : ℂ) (p : Joint) : 0 < weight β r p :=
  mul_pos (KFCausalQuarticPlaneDomination.potential_positive _) (Real.exp_pos _)

theorem joint_factor (α β w v : ℝ) (r : ℂ) (F G : ℂ → ℂ) (p : Joint) :
    jointDensity β (B α w v r) (C α β w v r) r F G p =
      (weight β r p:ℂ)*
        Complex.exp (-B α w v r*((p.1.1^2+(p.1.2 0)^2:ℝ):ℂ)-conj (B α w v r)*(p.2:ℂ))*
        (conj (F (neutral r (p.1.2 0) (p.1.2 1)))*G (neutral r (p.1.2 0) (p.1.2 1))) := by
  simp only [jointDensity,planeDensity,weight,Complex.ofReal_mul,Complex.ofReal_exp]
  have he : -B α w v r*(p.1.1:ℂ)^2+
      (-C α β w v r*(p.1.2 0:ℂ)^2-2*(β:ℂ)*(p.1.2 1:ℂ)^2)+
      (-conj (B α w v r)*(p.2:ℂ)) =
      ((-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2:ℝ):ℂ)+
        (-B α w v r*((p.1.1^2+(p.1.2 0)^2:ℝ):ℂ)-conj (B α w v r)*(p.2:ℂ)) := by
    unfold C
    push_cast
    ring
  have hh := congrArg Complex.exp he
  simp only [Complex.exp_add] at hh
  linear_combination (potential (p.1.2 1+fieldSlope r*p.1.2 0):ℂ)*
    (conj (F (neutral r (p.1.2 0) (p.1.2 1)))*G (neutral r (p.1.2 0) (p.1.2 1)))*hh

#print axioms joint_integrable
#print axioms joint_integral
#print axioms kernel_joint
#print axioms weight_positive
#print axioms joint_factor
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralLaplace
