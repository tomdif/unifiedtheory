/- Full five-dimensional weighted integration by parts for the actual
complex-sheared physical Gaussian family. All polynomial derivatives and
cross-width L1 premises are constructed, so the Haar-space Fubini theorem
introduces no boundary or assumed derivative-domain premise. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialTransverseIBP
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalIndependentRadialPhysicalPolynomial (Poly physicalPoint packet)
open KFCausalIndependentRadialTransverseRegularity (RealSpace realPoint rates)
open KFCausalIndependentRadialTransverseLines (totalQuadratic)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalPairedModeCoordinates (scale)

def direction (v : Fin 5→ℂ) (Q : Poly) : Poly :=
  ∑i,MvPolynomial.C (v i)*MvPolynomial.pderiv i Q

def exponent (α wL wR : ℝ) (b : ℂ) : Poly :=
  -(∑i,MvPolynomial.C (rates α wL wR i:ℂ)*MvPolynomial.X i^2)+
    MvPolynomial.C b*MvPolynomial.X 4

def step (α wL wR : ℝ) (δ b : ℂ) (v : RealSpace) (Q : Poly) : Poly :=
  direction (fun i=>physicalPoint δ v i) Q+
    Q*direction (fun i=>physicalPoint δ v i) (exponent α wL wR b)

private theorem direction_add (v : Fin 5→ℂ) (P Q : Poly) :
    direction v (P+Q)=direction v P+direction v Q := by
  simp [direction,mul_add,Finset.sum_add_distrib]

private theorem direction_mul (v : Fin 5→ℂ) (P Q : Poly) :
    direction v (P*Q)=direction v P*Q+P*direction v Q := by
  simp only [direction,MvPolynomial.pderiv_mul,mul_add,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem direction_X (v : Fin 5→ℂ) (j : Fin 5) :
    direction v (MvPolynomial.X j)=MvPolynomial.C (v j) := by
  unfold direction
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hi),mul_zero]
  · simp

theorem direction_derivative (Q : Poly) (x v : Fin 5→ℂ) :
    HasDerivAt (fun t:ℂ=>MvPolynomial.eval (fun i=>x i+t*v i) Q)
      (MvPolynomial.eval x (direction v Q)) 0 := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa [direction,MvPolynomial.pderiv_C] using hasDerivAt_const (0:ℂ) a
  | add P Q hP hQ => simpa [direction_add] using hP.add hQ
  | mul_X P j hP =>
    have hj := ((hasDerivAt_id (0:ℂ)).mul_const (v j)).const_add (x j)
    simpa only [direction_mul,direction_X,map_add,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,
      id_eq,zero_mul,add_zero,one_mul,Pi.mul_apply] using hP.mul hj

theorem exponent_eval (α wL wR : ℝ) (b : ℂ) (x : Space) :
    MvPolynomial.eval (fun i=>x i) (exponent α wL wR b)=
      -totalQuadratic α wL wR x+b*x 4 := by
  simp only [exponent,map_add,map_neg,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,
    rates,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    totalQuadratic,KFCausalIndependentRadialEntireLaplacian.quadratic,
    KFCausalIndependentRadialEntireLaplacian.radiusLeft,
    KFCausalIndependentRadialEntireLaplacian.radiusRight]
  change -((α/wL:ℝ)*x 0^2+((α*wR:ℝ)*x 1^2+((α/wL:ℝ)*x 2^2+
    ((α*wR:ℝ)*x 3^2+(α/32:ℝ)*x 4^2))))+b*x 4=_
  ring

private theorem physical_affine (δ : ℂ) (x v : RealSpace) (t : ℝ) :
    physicalPoint δ (x+t • v)=physicalPoint δ x+(t:ℂ) • physicalPoint δ v := by
  ext i
  fin_cases i <;> simp [physicalPoint,realPoint,flow] <;> ring

theorem packet_line_derivative (α wL wR : ℝ) (δ b : ℂ) (Q : Poly)
    (v x : RealSpace) : HasLineDerivAt ℝ (packet α wL wR δ b Q)
      (packet α wL wR δ b (step α wL wR δ b v Q) x) x v := by
  let y : Fin 5→ℂ := fun i=>physicalPoint δ x i
  let u : Fin 5→ℂ := fun i=>physicalPoint δ v i
  have hp := (direction_derivative Q y u).comp_ofReal
  have he := ((direction_derivative (exponent α wL wR b) y u).comp_ofReal).cexp
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at he
  unfold HasLineDerivAt
  convert hp.mul he using 1
  · funext t
    rw [packet,←exponent_eval]
    simp only [physical_affine,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,y,u,Pi.mul_apply]
  · simp only [packet,step,map_add,map_mul,Complex.ofReal_zero,zero_mul,add_zero,y,u]
    rw [exponent_eval]
    ring

def family (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (Q : Fin n→Poly) (x : RealSpace) : ℂ :=
  ∑j,C j*packet α (wL j) (wR j) δ (b j) (Q j) x

def familyStep (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b : Fin n→ℂ)
    (v : RealSpace) (Q : Fin n→Poly) : Fin n→Poly :=
  fun j=>step α (wL j) (wR j) δ (b j) v (Q j)

theorem family_weighted_memLp (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C : Fin n→ℂ) (Q : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j)
    (hR : ∀j,1≤wR j) (hδ : ‖δ‖≤1/5) (W : Poly) :
    MemLp (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      family n α wL wR δ b C Q x) 2 volume := by
  have hh := memLp_finset_sum Finset.univ (fun j (_:j∈(Finset.univ:Finset (Fin n)))=>
    (KFCausalIndependentRadialPhysicalPolynomial.weighted_packet_memLp α (wL j) (wR j)
      hα (hL j) (hR j) δ hδ (b j) W (Q j)).const_mul (C j))
  simpa only [family,Finset.mul_sum,mul_left_comm] using hh

theorem family_cross_integrable (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C D : Fin n→ℂ) (P Q : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j)
    (hR : ∀j,1≤wR j) (hδ : ‖δ‖≤1/5) (W : Poly) :
    Integrable (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*family n α wL wR δ b D Q x)) := by
  have h0 : MemLp (family n α wL wR δ b C P) 2 volume := by
    simpa using family_weighted_memLp n α wL wR δ b C P hα hL hR hδ 1
  have hi := h0.star.integrable_mul
    (family_weighted_memLp n α wL wR δ b D Q hα hL hR hδ W)
  change Integrable (fun x=>star (family n α wL wR δ b C P x)*
    (MvPolynomial.eval (fun i=>(x i:ℂ)) W*family n α wL wR δ b D Q x)) at hi
  simpa only [Complex.star_def,mul_left_comm] using hi

theorem family_line_derivative (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C : Fin n→ℂ) (Q : Fin n→Poly) (v x : RealSpace) :
    HasLineDerivAt ℝ (family n α wL wR δ b C Q)
      (family n α wL wR δ b C (familyStep n α wL wR δ b v Q) x) x v := by
  exact HasDerivAt.fun_sum (fun j _=>
    (packet_line_derivative α (wL j) (wR j) δ (b j) (Q j) v x).const_mul (C j))

theorem weighted_family_ibp (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C D : Fin n→ℂ) (P Q : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j)
    (hR : ∀j,1≤wR j) (hδ : ‖δ‖≤1/5) (v : RealSpace) (W : Poly) :
    (∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*
        family n α wL wR δ b D (familyStep n α wL wR δ b v Q) x))=
    -(∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) (direction (fun i=>(v i:ℂ)) W)*
      (conj (family n α wL wR δ b C P x)*family n α wL wR δ b D Q x))-
     (∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C (familyStep n α wL wR δ b v P) x)*
        family n α wL wR δ b D Q x)) := by
  let f := family n α wL wR δ b C P
  let g := family n α wL wR δ b D Q
  let df := family n α wL wR δ b C (familyStep n α wL wR δ b v P)
  let dg := family n α wL wR δ b D (familyStep n α wL wR δ b v Q)
  let w := fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W
  let dw := fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) (direction (fun i=>(v i:ℂ)) W)
  have hw (x:RealSpace) : HasLineDerivAt ℝ w (dw x) x v := by
    convert (direction_derivative W (fun i=>(x i:ℂ)) (fun i=>(v i:ℂ))).comp_ofReal using 1
    simp [HasLineDerivAt,w,dw,Complex.ofReal_add,Complex.ofReal_mul]
  have hf (x:RealSpace) := family_line_derivative n α wL wR δ b C P v x
  have hg (x:RealSpace) := family_line_derivative n α wL wR δ b D Q v x
  have hu (x:RealSpace) : HasLineDerivAt ℝ (fun y=>w y*conj (f y))
      (dw x*conj (f x)+w x*conj (df x)) x v := by
    simpa only [HasLineDerivAt,zero_smul,add_zero,Pi.mul_apply,Complex.star_def] using
      (hw x).mul (hf x).star
  have h1 := family_cross_integrable n α wL wR δ b C D P
    (familyStep n α wL wR δ b v Q) hα hL hR hδ W
  have h2 := family_cross_integrable n α wL wR δ b C D P Q hα hL hR hδ
    (direction (fun i=>(v i:ℂ)) W)
  have h3 := family_cross_integrable n α wL wR δ b C D
    (familyStep n α wL wR δ b v P) Q hα hL hR hδ W
  have h0 := family_cross_integrable n α wL wR δ b C D P Q hα hL hR hδ W
  have hi2 : Integrable (fun x=>(dw x*conj (f x)+w x*conj (df x))*g x) := by
    simpa only [add_mul,mul_assoc] using h2.add h3
  have hh := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B:=ContinuousLinearMap.mul ℝ ℂ) hi2
    (show Integrable (fun x=>(w x*conj (f x))*dg x) by simpa only [mul_assoc] using h1)
    (show Integrable (fun x=>(w x*conj (f x))*g x) by simpa only [mul_assoc] using h0) hu hg
  change (∫x:RealSpace,(w x*conj (f x))*dg x)=
    -(∫x:RealSpace,(dw x*conj (f x)+w x*conj (df x))*g x) at hh
  simp only [add_mul,mul_assoc] at hh
  rw [integral_add h2 h3] at hh
  exact hh.trans (neg_add _ _)

theorem family_neutral_profile (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C : Fin n→ℂ) (P : Fin n→Polynomial ℂ) (x : RealSpace) :
    family n α wL wR δ b C (fun j=>KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial (P j)) x=
      ∑j,C j*KFCausalIndependentRadialEntireLaplacian.profile (α/wL j:ℝ) (α*wR j:ℝ)
        (α/32) (b j) (P j) (physicalPoint δ x) := by
  simp only [family,KFCausalIndependentRadialPhysicalPolynomial.packet_profile]

theorem weighted_second_ibp (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ)
    (b C : Fin n→ℂ) (P : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j)
    (hR : ∀j,1≤wR j) (hδ : ‖δ‖≤1/5) (u v : RealSpace) (W : Poly) :
    (∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C P x)*family n α wL wR δ b C
        (familyStep n α wL wR δ b u (familyStep n α wL wR δ b v P)) x))=
    -(∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) (direction (fun i=>(u i:ℂ)) W)*
      (conj (family n α wL wR δ b C P x)*
        family n α wL wR δ b C (familyStep n α wL wR δ b v P) x))-
     (∫x:RealSpace,MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (family n α wL wR δ b C (familyStep n α wL wR δ b u P) x)*
        family n α wL wR δ b C (familyStep n α wL wR δ b v P) x)) :=
  weighted_family_ibp n α wL wR δ b C C P (familyStep n α wL wR δ b v P)
    hα hL hR hδ u W

#print axioms direction_derivative
#print axioms exponent_eval
#print axioms packet_line_derivative
#print axioms family_weighted_memLp
#print axioms family_cross_integrable
#print axioms family_line_derivative
#print axioms weighted_family_ibp
#print axioms family_neutral_profile
#print axioms weighted_second_ibp
end
end UnifiedTheory.Audit.KFCausalIndependentRadialTransverseIBP
