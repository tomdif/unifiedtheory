/- Exact finite-box Euler integration by parts for the actual BDG kernel.
The curvature kernel xi*f'(xi) is replaced by the original kernel acting
on an Euler derivative of the test profile. This is a finite-parameter
identity, not a differentiated continuum limit or a curved limit theorem. -/
import UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalMinkowski4DEulerIBP
noncomputable section
open MeasureTheory Set
open KFCausalMinkowski4DMoments (f4D)
open KFCausalMinkowski4DSecondOrder (f4D_hasDerivAt)

def fd (x : ℝ) : ℝ := Real.exp (-x)*(-10+25*x-12*x^2+(4/3)*x^3)
def kernel (a u v : ℝ) : ℝ := a*(v-u)^2*f4D (a*u^2*v^2)
def variation (a u v : ℝ) : ℝ := a*(v-u)^2*(a*u^2*v^2)*fd (a*u^2*v^2)
def fluxU (a u v : ℝ) : ℝ :=
  (a*(v-u)^2-2*a*u*(v-u))*f4D (a*u^2*v^2)+2*variation a u v
def fluxV (a u v : ℝ) : ℝ :=
  (a*(v-u)^2+2*a*v*(v-u))*f4D (a*u^2*v^2)+2*variation a u v
def boxIntegral (A B : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B, F p

theorem variation_eq_deriv (a u v : ℝ) :
    variation a u v = a*(v-u)^2*(a*u^2*v^2)*deriv f4D (a*u^2*v^2) := by
  rw [(f4D_hasDerivAt _).deriv]
  rfl

theorem flux_u_derivative (a u v : ℝ) :
    HasDerivAt (fun x => x*kernel a x v) (fluxU a u v) u := by
  have hz : HasDerivAt (fun x : ℝ => a*x^2*v^2) (2*a*u*v^2) u := by
    convert ((hasDerivAt_pow 2 u).const_mul a).mul_const (v^2) using 1; ring
  have hp : HasDerivAt (fun x : ℝ => a*(v-x)^2) (-2*a*(v-u)) u := by
    convert (((hasDerivAt_id u).const_sub v).pow 2).const_mul a using 1; simp only [id_eq]; ring
  have hh := (hasDerivAt_id u).mul (hp.mul ((f4D_hasDerivAt _).comp u hz))
  convert hh using 1
  dsimp [fluxU,variation,fd]
  ring

theorem flux_v_derivative (a u v : ℝ) :
    HasDerivAt (fun x => x*kernel a u x) (fluxV a u v) v := by
  have hz : HasDerivAt (fun x : ℝ => a*u^2*x^2) (2*a*u^2*v) v := by
    convert (hasDerivAt_pow 2 v).const_mul (a*u^2) using 1; ring
  have hp : HasDerivAt (fun x : ℝ => a*(x-u)^2) (2*a*(v-u)) v := by
    convert (((hasDerivAt_id v).sub_const u).pow 2).const_mul a using 1; simp only [id_eq]; ring
  have hh := (hasDerivAt_id v).mul (hp.mul ((f4D_hasDerivAt _).comp v hz))
  convert hh using 1
  dsimp [fluxV,variation,fd]
  ring

private theorem box_integrable (A B : ℝ) (F : ℝ × ℝ → ℝ) (hc : Continuous F) :
    IntegrableOn F (Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B) :=
  (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private theorem integral_u_zero (A B : ℝ) (hA : 0 ≤ A)
    (F D : ℝ × ℝ → ℝ) (hD : Continuous D)
    (hd : ∀ v u, HasDerivAt (fun x => F (x,v)) (D (u,v)) u)
    (h0 : ∀ v, F (0,v)=0) (h1 : ∀ v, F (A,v)=0) :
    boxIntegral A B D=0 := by
  have hi := box_integrable A B D hD
  change Integrable D ((volume.prod volume).restrict (Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B)) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ p, D p ∂(volume.prod volume).restrict (Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B))=0
  rw [← Measure.prod_restrict]
  rw [integral_prod_symm D hi]
  have he (v : ℝ) : (∫ u in Ioc (0:ℝ) A, D (u,v))=0 := by
    rw [← intervalIntegral.integral_of_le hA,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd v u)
        ((hD.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 A),h1,h0]
    ring
  simp only [he,integral_zero]

private theorem integral_v_zero (A B : ℝ) (hB : 0 ≤ B)
    (F D : ℝ × ℝ → ℝ) (hD : Continuous D)
    (hd : ∀ u v, HasDerivAt (fun x => F (u,x)) (D (u,v)) v)
    (h0 : ∀ u, F (u,0)=0) (h1 : ∀ u, F (u,B)=0) :
    boxIntegral A B D=0 := by
  have hi := box_integrable A B D hD
  change Integrable D ((volume.prod volume).restrict (Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B)) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ p, D p ∂(volume.prod volume).restrict (Ioc (0:ℝ) A ×ˢ Ioc (0:ℝ) B))=0
  rw [← Measure.prod_restrict]
  rw [integral_prod D hi]
  have he (u : ℝ) : (∫ v in Ioc (0:ℝ) B, D (u,v))=0 := by
    rw [← intervalIntegral.integral_of_le hB,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd u v)
        ((hD.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 B),h1,h0]
    ring
  simp only [he,integral_zero]

theorem compact_euler_identity (a A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (F Fu Fv : ℝ × ℝ → ℝ) (hF : Continuous F)
    (hFu : Continuous Fu) (hFv : Continuous Fv)
    (hdu : ∀ v u, HasDerivAt (fun x => F (x,v)) (Fu (u,v)) u)
    (hdv : ∀ u v, HasDerivAt (fun x => F (u,x)) (Fv (u,v)) v)
    (hFA : ∀ v, F (A,v)=0) (hFB : ∀ u, F (u,B)=0) :
    boxIntegral A B (fun p => variation a p.1 p.2*F p) =
      -(1/4)*boxIntegral A B (fun p => kernel a p.1 p.2*
        (4*F p+p.1*Fu p+p.2*Fv p)) := by
  let U : ℝ × ℝ → ℝ := fun p => fluxU a p.1 p.2*F p+p.1*kernel a p.1 p.2*Fu p
  let V : ℝ × ℝ → ℝ := fun p => fluxV a p.1 p.2*F p+p.2*kernel a p.1 p.2*Fv p
  have hUc : Continuous U := by dsimp [U,fluxU,variation,kernel,fd,f4D]; fun_prop
  have hVc : Continuous V := by dsimp [V,fluxV,variation,kernel,fd,f4D]; fun_prop
  have hu : boxIntegral A B U=0 := by
    apply integral_u_zero A B hA (fun p => p.1*kernel a p.1 p.2*F p) U hUc
    · intro v u; exact (flux_u_derivative a u v).mul (hdu v u)
    · intro v; simp only [zero_mul]
    · intro v; rw [hFA,mul_zero]
  have hv : boxIntegral A B V=0 := by
    apply integral_v_zero A B hB (fun p => p.2*kernel a p.1 p.2*F p) V hVc
    · intro u v; exact (flux_v_derivative a u v).mul (hdv u v)
    · intro u; simp only [zero_mul]
    · intro u; rw [hFB,mul_zero]
  have he : (fun p => U p+V p) = (fun p =>
      4*(variation a p.1 p.2*F p)+kernel a p.1 p.2*(4*F p+p.1*Fu p+p.2*Fv p)) := by
    funext p
    dsimp [U,V,fluxU,fluxV,kernel]
    ring
  have hc1 : Continuous (fun p : ℝ × ℝ => variation a p.1 p.2*F p) := by
    dsimp [variation,fd]; fun_prop
  have hc2 : Continuous (fun p : ℝ × ℝ => kernel a p.1 p.2*(4*F p+p.1*Fu p+p.2*Fv p)) := by
    dsimp [kernel,f4D]; fun_prop
  have hz : boxIntegral A B (fun p => U p+V p)=0 := by
    rw [boxIntegral,integral_add (box_integrable A B U hUc) (box_integrable A B V hVc)]
    change boxIntegral A B U+boxIntegral A B V=0
    rw [hu,hv]; ring
  rw [he,boxIntegral,integral_add ((box_integrable A B _ hc1).const_mul 4)
    (box_integrable A B _ hc2),integral_const_mul] at hz
  change 4*boxIntegral A B (fun p => variation a p.1 p.2*F p)+
    boxIntegral A B (fun p => kernel a p.1 p.2*(4*F p+p.1*Fu p+p.2*Fv p))=0 at hz
  linarith

#print axioms variation_eq_deriv
#print axioms flux_u_derivative
#print axioms flux_v_derivative
#print axioms compact_euler_identity
end
end UnifiedTheory.Audit.KFCausalMinkowski4DEulerIBP
