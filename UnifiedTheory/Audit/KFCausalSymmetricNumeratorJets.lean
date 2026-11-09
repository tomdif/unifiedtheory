/- First and second derivatives of the full sourced Gaussian numerator
along affine transverse lines. Both polynomial factors and the Gaussian
are differentiated; there is no division by a polynomial or its value. -/
import UnifiedTheory.Audit.KFCausalNeutralLinePackets
import UnifiedTheory.Audit.KFCausalComplexQuadraticPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricNumeratorJets
noncomputable section
open KFCausalComplexQuadraticPerturbation (quadratic bilinear)
variable {ι : Type*} [Fintype ι]

def slope (b d : ℂ) (Z U : ι → ℂ) : ℂ := b*d-2*bilinear Z U
def curvature (U : ι → ℂ) : ℂ := -2*quadratic U

def value (Γ b : ℂ) (Q P : Polynomial ℂ) (A z : ℂ) (Z : ι → ℂ) : ℂ :=
  Γ*Complex.exp (b*z-quadratic Z)*(Q.eval A*P.eval z)

def first (Γ b : ℂ) (Q P : Polynomial ℂ) (A z a d : ℂ) (Z U : ι → ℂ) : ℂ :=
  Γ*Complex.exp (b*z-quadratic Z)*
    (a*Q.derivative.eval A*P.eval z+d*Q.eval A*P.derivative.eval z+
      slope b d Z U*Q.eval A*P.eval z)

def second (Γ b : ℂ) (Q P : Polynomial ℂ) (A z a d : ℂ) (Z U : ι → ℂ) : ℂ :=
  Γ*Complex.exp (b*z-quadratic Z)*
    (a^2*Q.derivative.derivative.eval A*P.eval z+
      2*a*d*Q.derivative.eval A*P.derivative.eval z+
      d^2*Q.eval A*P.derivative.derivative.eval z+
      2*slope b d Z U*(a*Q.derivative.eval A*P.eval z+d*Q.eval A*P.derivative.eval z)+
      ((slope b d Z U)^2+curvature U)*Q.eval A*P.eval z)

theorem quadratic_affine_derivative (Z U : ι → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => quadratic (fun i => Z i+s*U i))
      (2*bilinear (fun i => Z i+t*U i) U) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (((hasDerivAt_id t).mul_const (U i)).const_add (Z i)).pow 2)
  convert hd using 1
  simp only [bilinear,Finset.mul_sum,id_eq]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem slope_affine_derivative (b d : ℂ) (Z U : ι → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => slope b d (fun i => Z i+s*U i) U) (curvature U) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (((hasDerivAt_id t).mul_const (U i)).const_add (Z i)).mul_const (U i))
  convert (hd.const_mul 2).const_sub (b*d) using 1
  simp only [curvature,quadratic,Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem value_affine_derivative (Γ b : ℂ) (Q P : Polynomial ℂ)
    (A z a d : ℂ) (Z U : ι → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => value Γ b Q P (A+s*a) (z+s*d) (fun i => Z i+s*U i))
      (first Γ b Q P (A+t*a) (z+t*d) a d (fun i => Z i+t*U i) U) t := by
  have hA := ((hasDerivAt_id t).mul_const a).const_add A
  have hz := ((hasDerivAt_id t).mul_const d).const_add z
  have hQ := (Q.hasDerivAt _).comp t hA
  have hP := (P.hasDerivAt _).comp t hz
  have he := ((hz.const_mul b).sub (quadratic_affine_derivative Z U t)).cexp
  convert (he.const_mul Γ).mul (hQ.mul hP) using 1
  simp only [first,slope,Function.comp_apply,Pi.mul_apply,Pi.sub_apply,id_eq]
  ring

theorem first_affine_derivative (Γ b : ℂ) (Q P : Polynomial ℂ)
    (A z a d : ℂ) (Z U : ι → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => first Γ b Q P (A+s*a) (z+s*d) a d (fun i => Z i+s*U i) U)
      (second Γ b Q P (A+t*a) (z+t*d) a d (fun i => Z i+t*U i) U) t := by
  have hA := ((hasDerivAt_id t).mul_const a).const_add A
  have hz := ((hasDerivAt_id t).mul_const d).const_add z
  have hQ := (Q.hasDerivAt _).comp t hA
  have hQ' := (Q.derivative.hasDerivAt _).comp t hA
  have hP := (P.hasDerivAt _).comp t hz
  have hP' := (P.derivative.hasDerivAt _).comp t hz
  have he := ((hz.const_mul b).sub (quadratic_affine_derivative Z U t)).cexp
  have hg := slope_affine_derivative b d Z U t
  have hp := (((hQ'.const_mul a).mul hP).add ((hQ.const_mul d).mul hP')).add
    ((hg.mul hQ).mul hP)
  convert (he.const_mul Γ).mul hp using 1
  simp only [second,slope,Function.comp_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,id_eq]
  ring

theorem value_real_derivative (Γ b : ℂ) (Q P : Polynomial ℂ)
    (A z a d : ℂ) (Z U : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => value Γ b Q P (A+(s:ℂ)*a) (z+(s:ℂ)*d)
      (fun i => Z i+(s:ℂ)*U i))
      (first Γ b Q P (A+(t:ℂ)*a) (z+(t:ℂ)*d) a d (fun i => Z i+(t:ℂ)*U i) U) t :=
  (value_affine_derivative Γ b Q P A z a d Z U (t:ℂ)).comp_ofReal

theorem first_real_derivative (Γ b : ℂ) (Q P : Polynomial ℂ)
    (A z a d : ℂ) (Z U : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => first Γ b Q P (A+(s:ℂ)*a) (z+(s:ℂ)*d) a d
      (fun i => Z i+(s:ℂ)*U i) U)
      (second Γ b Q P (A+(t:ℂ)*a) (z+(t:ℂ)*d) a d (fun i => Z i+(t:ℂ)*U i) U) t :=
  (first_affine_derivative Γ b Q P A z a d Z U (t:ℂ)).comp_ofReal

#print axioms quadratic_affine_derivative
#print axioms slope_affine_derivative
#print axioms value_affine_derivative
#print axioms first_affine_derivative
#print axioms value_real_derivative
#print axioms first_real_derivative
end
end UnifiedTheory.Audit.KFCausalSymmetricNumeratorJets
