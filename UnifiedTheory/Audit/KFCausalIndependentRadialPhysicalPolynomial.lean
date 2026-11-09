/- Polynomial L2 control for the literal complex-sheared physical Gaussian.
The neutral source and polynomial are attached exactly; arbitrary physical
polynomial insertions and coherent cross-width products retain genuine L1. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalPolynomial
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalIndependentRadialTransverseRegularity (RealSpace realPoint rates target)
open KFCausalIndependentRadialPulledLaplacian (scaledPoint flow_scaled)
open KFCausalIndependentRadialTransverseLines (totalQuadratic)
open KFCausalIndependentRadialEntireLaplacian (profile)
open KFCausalPairedModeCoordinates (scale)

abbrev Poly := MvPolynomial (Fin 5) ℂ

def physicalPoint (δ : ℂ) (x : RealSpace) : Space := flow (2*scale) δ (realPoint x)
def packet (α wL wR : ℝ) (δ b : ℂ) (Q : Poly) (x : RealSpace) : ℂ :=
  MvPolynomial.eval (fun i=>physicalPoint δ x i) Q *
    Complex.exp (-totalQuadratic α wL wR (physicalPoint δ x)+b*physicalPoint δ x 4)
def rescalePolynomial (α wL wR : ℝ) (Q : Poly) : Poly :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i=>MvPolynomial.C ((Real.sqrt (rates α wL wR i):ℂ)⁻¹)*MvPolynomial.X i) Q

def neutralPolynomial (P : Polynomial ℂ) : Poly :=
  P.eval₂ MvPolynomial.C (MvPolynomial.X 4)

def flowPolynomial (δ : ℂ) : Fin 5→Poly :=
  ![MvPolynomial.C (Complex.exp (-δ/2))*MvPolynomial.X 0,
    MvPolynomial.C (Complex.exp (-δ/2))*MvPolynomial.X 1,
    MvPolynomial.C (Complex.exp (δ/2))*MvPolynomial.X 2,
    MvPolynomial.C (Complex.exp (δ/2))*MvPolynomial.X 3,
    MvPolynomial.X 4+MvPolynomial.C (2*(2*scale:ℝ)*(Complex.exp (δ/2)-1))*MvPolynomial.X 3]
def pullPolynomial (δ : ℂ) (Q : Poly) : Poly :=
  MvPolynomial.eval₂ MvPolynomial.C (flowPolynomial δ) Q

private theorem scaled_quadratic (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL)
    (hR : 0<wR) (x : Space) :
    KFCausalComplexQuadraticPerturbation.quadratic (fun i=>scaledPoint α wL wR x i)=
      totalQuadratic α wL wR x := by
  have hs : (Real.sqrt (α/wL):ℂ)^2=(α/wL:ℝ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht : (Real.sqrt (α*wR):ℂ)^2=(α*wR:ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hn : (Real.sqrt (α/32):ℂ)^2=(α/32:ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤α/32 by positivity)
  simp only [KFCausalComplexQuadraticPerturbation.quadratic,scaledPoint,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_pow,hs,ht,hn,add_zero,totalQuadratic,
    KFCausalIndependentRadialEntireLaplacian.quadratic,
    KFCausalIndependentRadialEntireLaplacian.radiusLeft,
    KFCausalIndependentRadialEntireLaplacian.radiusRight]
  ring

private theorem rescale_eval (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL)
    (hR : 0<wR) (Q : Poly) (x : Space) :
    MvPolynomial.eval (fun i=>scaledPoint α wL wR x i) (rescalePolynomial α wL wR Q)=
      MvPolynomial.eval (fun i=>x i) Q := by
  unfold rescalePolynomial
  rw [←MvPolynomial.eval_assoc]
  apply congrArg (fun y : Fin 5→ℂ => MvPolynomial.eval y Q)
  funext i
  have hpos : ∀j,0<rates α wL wR j := by
    intro j
    fin_cases j <;> dsimp [rates] <;> positivity
  have hz : (Real.sqrt (rates α wL wR i):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hpos i)).ne'
  have he : scaledPoint α wL wR x i=(Real.sqrt (rates α wL wR i):ℂ)*x i := by
    fin_cases i <;> rfl
  simp only [Function.comp_apply,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  change (Real.sqrt (rates α wL wR i):ℂ)⁻¹*scaledPoint α wL wR x i=x i
  rw [he,←mul_assoc,inv_mul_cancel₀ hz,one_mul]

theorem packet_eq_normalized (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL)
    (hR : 0<wR) (δ b : ℂ) (Q : Poly) (x : RealSpace) :
    packet α wL wR δ b Q x=
      KFCausalIndependentRadialTransverseRegularity.packet α wL wR δ
        (Pi.single 4 (b/(Real.sqrt (α/32):ℂ))) (rescalePolynomial α wL wR Q) x := by
  have hy : target α wL wR δ x=scaledPoint α wL wR (physicalPoint δ x) :=
    flow_scaled α wL wR hα hR δ (realPoint x)
  have hn : (Real.sqrt (α/32):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold packet KFCausalIndependentRadialTransverseRegularity.packet
  rw [hy,rescale_eval α wL wR hα hL hR,scaled_quadratic α wL wR hα hL hR]
  congr 2
  have hs : (∑ i : Fin 5, (Pi.single 4 (b/(Real.sqrt (α/32):ℂ)) : Fin 5→ℂ) i *
      scaledPoint α wL wR (physicalPoint δ x) i)=b*physicalPoint δ x 4 := by
    rw [Finset.sum_eq_single 4]
    · rw [Pi.single_eq_same]
      change (b/(Real.sqrt (α/32):ℂ))*((Real.sqrt (α/32):ℂ)*physicalPoint δ x 4)=_
      field_simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  rw [hs]
  ring

theorem neutralPolynomial_eval (P : Polynomial ℂ) (x : Fin 5→ℂ) :
    MvPolynomial.eval x (neutralPolynomial P)=P.eval (x 4) := by
  unfold neutralPolynomial
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.eval₂_monomial,Polynomial.eval_monomial]

theorem packet_profile (α wL wR : ℝ) (δ b : ℂ) (P : Polynomial ℂ) (x : RealSpace) :
    packet α wL wR δ b (neutralPolynomial P) x=
      profile (α/wL:ℝ) (α*wR:ℝ) (α/32) b P (physicalPoint δ x) := by
  unfold packet
  rw [neutralPolynomial_eval]
  simp only [profile,KFCausalNeutralLinePackets.entire,totalQuadratic,neg_add,
    Complex.exp_add]
  ring

theorem packet_memLp (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b : ℂ) (Q : Poly) :
    MemLp (packet α wL wR δ b Q) 2 volume := by
  have he : packet α wL wR δ b Q=
      KFCausalIndependentRadialTransverseRegularity.packet α wL wR δ
        (Pi.single 4 (b/(Real.sqrt (α/32):ℂ))) (rescalePolynomial α wL wR Q) := by
    funext x
    exact packet_eq_normalized α wL wR hα hL (zero_lt_one.trans_le hR) δ b Q x
  rw [he]
  exact KFCausalIndependentRadialTransverseRegularity.packet_memLp α wL wR hα hL hR δ hδ _ _

theorem flowPolynomial_eval (δ : ℂ) (x : Space) (i : Fin 5) :
    MvPolynomial.eval (fun j=>x j) (flowPolynomial δ i)=flow (2*scale) δ x i := by
  fin_cases i <;> simp [flowPolynomial,flow]

theorem pullPolynomial_eval (δ : ℂ) (Q : Poly) (x : Space) :
    MvPolynomial.eval (fun i=>x i) (pullPolynomial δ Q)=
      MvPolynomial.eval (fun i=>flow (2*scale) δ x i) Q := by
  unfold pullPolynomial
  rw [←MvPolynomial.eval_assoc]
  apply congrArg (fun y : Fin 5→ℂ => MvPolynomial.eval y Q)
  funext i
  exact flowPolynomial_eval δ x i

theorem weighted_packet (α wL wR : ℝ) (δ b : ℂ) (W Q : Poly) (x : RealSpace) :
    MvPolynomial.eval (fun i=>(x i:ℂ)) W*packet α wL wR δ b Q x=
      packet α wL wR δ b (pullPolynomial (-δ) W*Q) x := by
  unfold packet
  rw [map_mul,pullPolynomial_eval]
  have hf : flow (2*scale) (-δ) (physicalPoint δ x)=realPoint x := by
    unfold physicalPoint
    rw [KFCausalComplexShearGroup.flow_compose,neg_add_cancel,KFCausalComplexShearGroup.flow_zero]
  rw [hf]
  exact mul_assoc _ _ _ |>.symm

theorem weighted_packet_memLp (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b : ℂ) (W Q : Poly) :
    MemLp (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*packet α wL wR δ b Q x)
      2 volume := by
  simp_rw [weighted_packet]
  exact packet_memLp α wL wR hα hL hR δ hδ b _

theorem weighted_cross_integrable (α wL wR vL vR : ℝ) (hα : 0<α)
    (hL : 0<wL) (hR : 1≤wR) (hvL : 0<vL) (hvR : 1≤vR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b c : ℂ) (W P Q : Poly) :
    Integrable (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) W*
      (conj (packet α wL wR δ b P x)*packet α vL vR δ c Q x)) := by
  have hi := (packet_memLp α wL wR hα hL hR δ hδ b P).star.integrable_mul
    (weighted_packet_memLp α vL vR hα hvL hvR δ hδ c W Q)
  convert hi using 1
  funext x
  simp only [Pi.mul_apply,Pi.star_apply,Complex.star_def]
  ring

#print axioms packet_eq_normalized
#print axioms neutralPolynomial_eval
#print axioms packet_profile
#print axioms packet_memLp
#print axioms flowPolynomial_eval
#print axioms pullPolynomial_eval
#print axioms weighted_packet
#print axioms weighted_packet_memLp
#print axioms weighted_cross_integrable
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalPolynomial
