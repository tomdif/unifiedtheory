/- Actual five-dimensional completion for the coherent physical Gaussian
family. The differential expression uses the literal clock/shear metric;
all integral and derivative premises come from the constructed packet family. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialWeightedContraction
import UnifiedTheory.Audit.KFCausalPhysicalClockMetricCompletion
import UnifiedTheory.Audit.KFCausalPhysicalClockMetricCoefficients

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialIntegralCompletion
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalIndependentRadialPhysicalPolynomial (Poly)
open KFCausalIndependentRadialTransverseRegularity (RealSpace)
open KFCausalIndependentRadialTransverseIBP (family direction)
open KFCausalIndependentRadialWeightedContraction (basis firstPolynomial laplacian gradientForm weightForm)
open KFCausalComplexShearPerturbation (Space)
open KFCausalPhysicalClockMetric (metric shiftedClock)
open KFCausalPhysicalClockMetricCoefficients (coefficient inner_contraction)
open KFCausalPhysicalClockMetricCompletion (fieldVector second density)
open KFCausalCommonRealGaussianWeightedEnergy (potential)
open KFCausalPairedModeCoordinates (scale)

def field (x : RealSpace) : ℝ := 2*scale*x 3+x 4
def fieldPolynomial : Poly := MvPolynomial.C ((2*scale:ℝ):ℂ)*MvPolynomial.X 3+MvPolynomial.X 4
def weightPolynomial (m g k : ℝ) : Poly := MvPolynomial.C (k:ℂ)+
  MvPolynomial.C ((m/2:ℝ):ℂ)*fieldPolynomial^2+MvPolynomial.C ((g/4:ℝ):ℂ)*fieldPolynomial^4

theorem weight_eval (m g k : ℝ) (x : RealSpace) :
    MvPolynomial.eval (fun i=>(x i:ℂ)) (weightPolynomial m g k)=
      (potential m g k (field x):ℂ) := by
  simp only [weightPolynomial,fieldPolynomial,map_add,map_mul,map_pow,MvPolynomial.eval_C,
    MvPolynomial.eval_X,potential,field]
  push_cast
  ring

private theorem direction_basis (i : Fin 5) (Q : Poly) :
    direction (fun j=>(basis i j:ℂ)) Q=MvPolynomial.pderiv i Q := by
  unfold direction
  rw [Finset.sum_eq_single i]
  · simp [basis]
  · intro j _ hj
    simp [basis,hj]
  · simp

theorem weight_direction (m g k : ℝ) (x : RealSpace) (i : Fin 5) :
    MvPolynomial.eval (fun j=>(x j:ℂ))
      (direction (fun j=>(basis i j:ℂ)) (weightPolynomial m g k))=
        conj (fieldVector i)*(KFCausalPhysicalClockMetricCompletion.slope m g (field x):ℂ) := by
  rw [direction_basis]
  fin_cases i <;>
    simp [weightPolynomial,fieldPolynomial,
      MvPolynomial.pderiv_X,fieldVector,KFCausalPhysicalClockMetricCompletion.slope,field] <;>
      norm_num [map_ofNat,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
        Complex.ofReal_div] <;> ring

def gradient (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (x : RealSpace) : Space :=
  WithLp.toLp 2 (fun i=>family n α wL wR δ b C (firstPolynomial n α wL wR δ b P i) x)

theorem forms_eq (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (ε s m g k : ℝ) (x : RealSpace) :
    gradientForm n α wL wR δ b C P (coefficient ε s δ) (weightPolynomial m g k) x+
      weightForm n α wL wR δ b C P (coefficient ε s δ) (weightPolynomial m g k) x=
    (potential m g k (field x):ℂ)*inner ℂ (gradient n α wL wR δ b C P x)
      (metric ε s δ (gradient n α wL wR δ b C P x))+
      (KFCausalPhysicalClockMetricCompletion.slope m g (field x):ℂ)*conj (family n α wL wR δ b C P x)*
        inner ℂ fieldVector (metric ε s δ (gradient n α wL wR δ b C P x)) := by
  rw [←inner_contraction,←inner_contraction]
  simp only [gradientForm,weightForm,weight_eval,weight_direction,Finset.mul_sum,gradient]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

def energyDensity (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (m g k : ℝ) (x : RealSpace) : ℝ :=
  potential m g k (field x)*‖family n α wL wR δ b C P x‖^2

def pairedDensity (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (ε s h m g k : ℝ) (x : RealSpace) : ℂ :=
  (potential m g k (field x):ℂ)*conj (family n α wL wR δ b C P x)*
    ((shiftedClock ε s δ/2)*family n α wL wR δ b C P x-
      ((h:ℂ)^2/2)*laplacian n α wL wR δ b C P (coefficient ε s δ) x)

def completedDensity (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (ε s h m g k : ℝ) (x : RealSpace) : ℝ :=
  density ε s h m g k (field x) δ (family n α wL wR δ b C P x)
    (gradient n α wL wR δ b C P x)

private theorem norm_square (z : ℂ) : conj z*z=(‖z‖^2:ℝ) := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self]

variable (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Poly) (hα : 0<α) (hL : ∀j,0<wL j) (hR : ∀j,1≤wR j)
    (hδ : ‖δ‖≤1/20) (ε s h m g k : ℝ)
include hα hL hR hδ

theorem energy_integrable : Integrable (energyDensity n α wL wR δ b C P m g k) := by
  have hi := KFCausalIndependentRadialTransverseIBP.family_cross_integrable n α wL wR δ b C C P P
    hα hL hR (by linarith : ‖δ‖≤1/5) (weightPolynomial m g k)
  have he : (fun x:RealSpace=>MvPolynomial.eval (fun i=>(x i:ℂ)) (weightPolynomial m g k)*
      (conj (family n α wL wR δ b C P x)*family n α wL wR δ b C P x))=
        fun x=>(energyDensity n α wL wR δ b C P m g k x:ℂ) := by
    funext x
    rw [weight_eval,norm_square]
    simp only [energyDensity,Complex.ofReal_mul]
  rw [he] at hi
  simpa only [Complex.ofReal_re] using hi.re

theorem pairing_integrable : Integrable (pairedDensity n α wL wR δ b C P ε s h m g k) ∧
    Integrable (completedDensity n α wL wR δ b C P ε s h m g k) := by
  have he : Integrable (fun x:RealSpace=>(energyDensity n α wL wR δ b C P m g k x:ℂ)) :=
    (energy_integrable n α wL wR δ b C P hα hL hR hδ m g k).ofReal
  have hl := KFCausalIndependentRadialWeightedContraction.laplacian_form_integrable
    n α wL wR δ b C P hα hL hR (by linarith : ‖δ‖≤1/5)
    (coefficient ε s δ) (weightPolynomial m g k)
  have hf := KFCausalIndependentRadialWeightedContraction.forms_integrable
    n α wL wR δ b C P hα hL hR (by linarith : ‖δ‖≤1/5)
    (coefficient ε s δ) (weightPolynomial m g k)
  constructor
  · convert (he.const_mul (shiftedClock ε s δ/2)).sub (hl.const_mul ((h:ℂ)^2/2)) using 1
    funext x
    simp only [Pi.sub_apply,pairedDensity,energyDensity,Complex.ofReal_mul,weight_eval]
    rw [←norm_square]
    ring
  · have hi : Integrable (fun x:RealSpace=>
        ((shiftedClock ε s δ/2)*(energyDensity n α wL wR δ b C P m g k x:ℂ)+
          ((h:ℂ)^2/2)*(gradientForm n α wL wR δ b C P (coefficient ε s δ)
            (weightPolynomial m g k) x+weightForm n α wL wR δ b C P (coefficient ε s δ)
            (weightPolynomial m g k) x)).re) :=
      ((he.const_mul (shiftedClock ε s δ/2)).add
        ((hf.1.add hf.2).const_mul ((h:ℂ)^2/2))).re
    apply hi.congr
    filter_upwards with x
    simp only [completedDensity,density,energyDensity,Complex.ofReal_mul,forms_eq]
    congr 1
    ring

theorem integral_identity :
    (∫x:RealSpace,pairedDensity n α wL wR δ b C P ε s h m g k x).re=
      ∫x:RealSpace,completedDensity n α wL wR δ b C P ε s h m g k x := by
  let E : RealSpace→ℂ := fun x=>(energyDensity n α wL wR δ b C P m g k x:ℂ)
  let A : RealSpace→ℂ := fun x=>MvPolynomial.eval (fun i=>(x i:ℂ)) (weightPolynomial m g k)*
    (conj (family n α wL wR δ b C P x)*(-laplacian n α wL wR δ b C P (coefficient ε s δ) x))
  let B : RealSpace→ℂ := fun x=>gradientForm n α wL wR δ b C P (coefficient ε s δ)
      (weightPolynomial m g k) x+weightForm n α wL wR δ b C P (coefficient ε s δ)
      (weightPolynomial m g k) x
  have he : Integrable E := (energy_integrable n α wL wR δ b C P hα hL hR hδ m g k).ofReal
  have hla := KFCausalIndependentRadialWeightedContraction.laplacian_form_integrable
    n α wL wR δ b C P hα hL hR (by linarith : ‖δ‖≤1/5)
    (coefficient ε s δ) (weightPolynomial m g k)
  have ha : Integrable A := by simpa only [A,mul_neg] using hla.neg
  have hfb := KFCausalIndependentRadialWeightedContraction.forms_integrable
    n α wL wR δ b C P hα hL hR (by linarith : ‖δ‖≤1/5)
    (coefficient ε s δ) (weightPolynomial m g k)
  have hb : Integrable B := hfb.1.add hfb.2
  have hab : (∫x,A x)=∫x,B x := KFCausalIndependentRadialWeightedContraction.weighted_laplacian_ibp
    n α wL wR δ b C P hα hL hR (by linarith : ‖δ‖≤1/5)
    (coefficient ε s δ) (weightPolynomial m g k)
  have hp : pairedDensity n α wL wR δ b C P ε s h m g k=
      fun x=>(shiftedClock ε s δ/2)*E x+((h:ℂ)^2/2)*A x := by
    funext x
    simp only [pairedDensity,E,A,energyDensity,Complex.ofReal_mul,weight_eval]
    rw [←norm_square]
    ring
  have hc : completedDensity n α wL wR δ b C P ε s h m g k=
      fun x=>((shiftedClock ε s δ/2)*E x+((h:ℂ)^2/2)*B x).re := by
    funext x
    simp only [completedDensity,density,E,B,energyDensity,Complex.ofReal_mul,forms_eq]
    ring
  rw [hp,hc,integral_add (he.const_mul _) (ha.const_mul _),integral_const_mul,
    integral_const_mul,hab,←integral_const_mul,←integral_const_mul,
    ←integral_add (he.const_mul _) (hb.const_mul _)]
  exact (integral_re ((he.const_mul _).add (hb.const_mul _))).symm

theorem positive_vacuum_integral_lower (hε : 0<ε) (hm : 0≤m) (hg : 0≤g) (hk : 0<k) :
    -((2*h^2/ε)*(12+(m+3*g)/k))*(∫x:RealSpace,energyDensity n α wL wR δ b C P m g k x)≤
      (∫x:RealSpace,pairedDensity n α wL wR δ b C P ε s h m g k x).re := by
  rw [integral_identity n α wL wR δ b C P hα hL hR hδ ε s h m g k,←integral_const_mul]
  apply integral_mono ((energy_integrable n α wL wR δ b C P hα hL hR hδ m g k).const_mul _)
    (pairing_integrable n α wL wR δ b C P hα hL hR hδ ε s h m g k).2
  intro x
  simpa only [energyDensity,completedDensity,mul_assoc] using
    KFCausalPhysicalClockMetricCompletion.positive_vacuum_lower ε s h m g k (field x)
      hε δ hδ hm hg hk (family n α wL wR δ b C P x) (gradient n α wL wR δ b C P x)

#print axioms weight_eval
#print axioms weight_direction
#print axioms forms_eq
#print axioms energy_integrable
#print axioms pairing_integrable
#print axioms integral_identity
#print axioms positive_vacuum_integral_lower
end
end UnifiedTheory.Audit.KFCausalIndependentRadialIntegralCompletion
