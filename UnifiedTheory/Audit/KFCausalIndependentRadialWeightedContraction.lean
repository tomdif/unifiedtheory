/- The physical coherent packet IBP contracted with an arbitrary constant
complex bilinear metric. Actual derivative products are L1 in five dimensions;
the contraction contains every mixed derivative and interference term. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseIBP

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialWeightedContraction
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalIndependentRadialPhysicalPolynomial (Poly)
open KFCausalIndependentRadialTransverseRegularity (RealSpace)
open KFCausalIndependentRadialTransverseIBP (direction family familyStep)

abbrev Metric := Fin 5→Fin 5→ℂ
def basis (i : Fin 5) : RealSpace := Pi.single i 1

def firstPolynomial (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b : Fin n→ℂ)
    (P : Fin n→Poly) (i : Fin 5) : Fin n→Poly := familyStep n α wL wR δ b (basis i) P

def secondPolynomial (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b : Fin n→ℂ)
    (P : Fin n→Poly) (i j : Fin 5) : Fin n→Poly :=
  firstPolynomial n α wL wR δ b (firstPolynomial n α wL wR δ b P j) i

def laplacian (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (B : Metric) (x : RealSpace) : ℂ :=
  ∑ij : Fin 5×Fin 5,B ij.1 ij.2*family n α wL wR δ b C
    (secondPolynomial n α wL wR δ b P ij.1 ij.2) x

def gradientForm (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (B : Metric) (W : Poly) (x : RealSpace) : ℂ :=
  ∑ij : Fin 5×Fin 5,B ij.1 ij.2*(MvPolynomial.eval (fun i=>(x i:ℂ)) W*
    (conj (family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.1) x)*
      family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.2) x))

def weightForm (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (B : Metric) (W : Poly) (x : RealSpace) : ℂ :=
  ∑ij : Fin 5×Fin 5,B ij.1 ij.2*(MvPolynomial.eval (fun i=>(x i:ℂ))
    (direction (fun k=>(basis ij.1 k:ℂ)) W)*
      (conj (family n α wL wR δ b C P x)*
        family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.2) x))

variable (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j) (hR : ∀j,1≤wR j)
    (hδ : ‖δ‖≤1/5) (B : Metric) (W : Poly)
include hα hL hR hδ

theorem forms_integrable :
    Integrable (gradientForm n α wL wR δ b C P B W) ∧
      Integrable (weightForm n α wL wR δ b C P B W) := by
  constructor
  · exact integrable_finset_sum Finset.univ (fun ij _=>
      (KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C
        (firstPolynomial n α wL wR δ b P ij.1) (firstPolynomial n α wL wR δ b P ij.2)
        hα hL hR hδ W).const_mul (B ij.1 ij.2))
  · exact integrable_finset_sum Finset.univ (fun ij _=>
      (KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C P
        (firstPolynomial n α wL wR δ b P ij.2) hα hL hR hδ
        (direction (fun k=>(basis ij.1 k:ℂ)) W)).const_mul (B ij.1 ij.2))

theorem laplacian_form_integrable :
    Integrable (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*laplacian n α wL wR δ b C P B x)) := by
  have hi := integrable_finset_sum Finset.univ (fun ij (_:ij∈(Finset.univ:Finset (Fin 5×Fin 5)))=>
    (KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C P
      (secondPolynomial n α wL wR δ b P ij.1 ij.2) hα hL hR hδ W).const_mul (B ij.1 ij.2))
  simpa only [laplacian,Finset.mul_sum,mul_left_comm] using hi

theorem weighted_laplacian_ibp :
    (∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*(-laplacian n α wL wR δ b C P B x)))=
      ∫x:RealSpace,gradientForm n α wL wR δ b C P B W x+
        weightForm n α wL wR δ b C P B W x := by
  let t := fun ij : Fin 5×Fin 5 => fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
    (conj (family n α wL wR δ b C P x)*
      family n α wL wR δ b C (secondPolynomial n α wL wR δ b P ij.1 ij.2) x)
  let u := fun ij : Fin 5×Fin 5 => fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
    (conj (family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.1) x)*
      family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.2) x)
  let v := fun ij : Fin 5×Fin 5 => fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ))
    (direction (fun k=>(basis ij.1 k:ℂ)) W)*
      (conj (family n α wL wR δ b C P x)*
        family n α wL wR δ b C (firstPolynomial n α wL wR δ b P ij.2) x)
  have ht ij : Integrable (t ij) :=
    KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C P
      (secondPolynomial n α wL wR δ b P ij.1 ij.2) hα hL hR hδ W
  have hu ij : Integrable (u ij) :=
    KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C
      (firstPolynomial n α wL wR δ b P ij.1) (firstPolynomial n α wL wR δ b P ij.2)
      hα hL hR hδ W
  have hv ij : Integrable (v ij) :=
    KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C P
      (firstPolynomial n α wL wR δ b P ij.2) hα hL hR hδ
      (direction (fun k=>(basis ij.1 k:ℂ)) W)
  have he ij : (∫x,t ij x)=-(∫x,v ij x)-(∫x,u ij x) :=
    KFCausalIndependentRadialTransverseIBP.weighted_second_ibp n α wL wR δ b C P
      hα hL hR hδ (basis ij.1) (basis ij.2) W
  have hleft (x:RealSpace) : MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*(-laplacian n α wL wR δ b C P B x))=
        ∑ij : Fin 5×Fin 5,-B ij.1 ij.2*t ij x := by
    simp only [laplacian,t,Finset.mul_sum,mul_neg]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ij _
    ring
  simp_rw [hleft]
  rw [integral_finset_sum _ (fun ij _=>(ht ij).const_mul (-B ij.1 ij.2))]
  have hi := forms_integrable n α wL wR δ b C P hα hL hR hδ B W
  rw [integral_add hi.1 hi.2]
  change _=(∫x:RealSpace,∑ij : Fin 5×Fin 5,B ij.1 ij.2*u ij x)+
    (∫x:RealSpace,∑ij : Fin 5×Fin 5,B ij.1 ij.2*v ij x)
  rw [integral_finset_sum _ (fun ij _=>(hu ij).const_mul (B ij.1 ij.2)),
    integral_finset_sum _ (fun ij _=>(hv ij).const_mul (B ij.1 ij.2)),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [integral_const_mul,he]
  ring

#print axioms forms_integrable
#print axioms laplacian_form_integrable
#print axioms weighted_laplacian_ibp
end
end UnifiedTheory.Audit.KFCausalIndependentRadialWeightedContraction
