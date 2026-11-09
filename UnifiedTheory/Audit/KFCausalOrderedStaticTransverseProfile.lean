/- The original shifted source and ordered-static representatives in
physical real transverse coordinates. The only coordinate premise is
the explicit real inverse shear, discharged by the physical chart. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMetricLaplacian
import UnifiedTheory.Audit.KFCausalOrderedStaticPotentialPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticTransverseProfile
noncomputable section
open scoped ComplexConjugate
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalIndependentRadialTransverseRegularity (RealSpace realPoint)
open KFCausalIndependentRadialPhysicalPolynomial (neutralPolynomial physicalPoint packet packet_profile)
open KFCausalIndependentRadialTransverseIBP (family)
open KFCausalIndependentRadialWeightedContraction (laplacian)
open KFCausalIndependentRadialPulledLaplacian (coordinate scalar entireOutput)
open KFCausalComplexShearPerturbation (flow)
open KFCausalComplexShearGroup (flow_compose)
open KFCausalPairedModeCoordinates (scale)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalPhysicalClockMetric (shiftedClock)
open KFCausalPhysicalClockMetricCoefficients (coefficient)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalOrderedStaticPotentialPairing (sourceProfile staticProfile)

def shifted (h : ℝ) (x : Product) : ℂ := shift (h/2) (x.2 0:ℂ)
def increment (ε h s : ℝ) (x : Product) : ℂ := complexInverse ε (shifted h x)-(s:ℂ)
def amplitude (n : ℕ) (ε h : ℝ) (a p : Fin n→ℝ) (C : Fin n→ℂ) (x : Product) : Fin n→ℂ :=
  fun j=>scalar ε (a j) (groundWidth h) (C j) (p j) (shifted h x)
def transverse (n : ℕ) (ε h s : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (x : Product) (y : RealSpace) : ℂ :=
  family n (groundWidth h) w w (increment ε h s x) b (amplitude n ε h a p C x)
    (fun j=>neutralPolynomial (P j)) y
def transverseLaplacian (n : ℕ) (ε h s : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (x : Product) (y : RealSpace) : ℂ :=
  laplacian n (groundWidth h) w w (increment ε h s x) b (amplitude n ε h a p C x)
    (fun j=>neutralPolynomial (P j)) (coefficient ε s (increment ε h s x)) y

theorem shifted_clock (ε h s : ℝ) (x : Product) :
    KFCausalClockFloorComplexDefect.complexClock ε (shifted h x)=
      shiftedClock ε s (increment ε h s x) := by
  unfold KFCausalClockFloorComplexDefect.complexClock shiftedClock increment
  rw [add_sub_cancel]

private theorem flow_reference (ε h s : ℝ) (x : Product) (y : RealSpace)
    (hc : coordinate (momentumScale h) ((split 2 4).symm x)=flow (2*scale) (-(s:ℂ)) (realPoint y)) :
    flow (2*scale) (complexInverse ε (shifted h x))
      (coordinate (momentumScale h) ((split 2 4).symm x))=
      physicalPoint (increment ε h s x) y := by
  rw [hc,flow_compose]
  congr 1

variable (n : ℕ) (ε h s : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hh : h≠0) (hw : ∀i,1≤w i)
    (x : Product) (y : RealSpace)
    (hc : coordinate (momentumScale h) ((split 2 4).symm x)=flow (2*scale) (-(s:ℂ)) (realPoint y))
include hh hw hc

theorem source_reference : sourceProfile n ε h a w p C b P x=transverse n ε h s a w p C b P x y := by
  unfold sourceProfile transverse family amplitude
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalIndependentRadialPulledLaplacian.numerator_formula ε (a j) (groundWidth h)
    (w j) (w j) (momentumScale h) (C j) (p j) (b j) (P j) 0 0
    (groundWidth_positive h hh) (zero_lt_one.trans_le (hw j)) (zero_lt_one.trans_le (hw j))]
  simp only [pow_zero,one_mul,entireOutput]
  change scalar ε (a j) (groundWidth h) (C j) (p j) (shifted h x)*
    KFCausalIndependentRadialEntireLaplacian.profile _ _ _ _ _
      (flow (2*scale) (complexInverse ε (shifted h x))
        (coordinate (momentumScale h) ((split 2 4).symm x)))=_
  rw [flow_reference ε h s x y hc,packet_profile]

theorem static_reference : staticProfile n ε h a w p C b P x=
    (shiftedClock ε s (increment ε h s x)/2)*transverse n ε h s a w p C b P x y-
      ((h:ℂ)^2/2)*transverseLaplacian n ε h s a w p C b P x y := by
  have hrep (j : Fin n) : KFCausalOrderedStaticOutputRepresentative.profile ε (a j) h (w j) (w j)
      (C j) (p j) (b j) (P j) (shifted h x) ((split 2 4).symm x)=
      (shiftedClock ε s (increment ε h s x)/2)*amplitude n ε h a p C x j*
        packet (groundWidth h) (w j) (w j) (increment ε h s x) (b j) (neutralPolynomial (P j)) y-
      ((h:ℂ)^2/2)*(shiftedClock ε s (increment ε h s x))⁻¹*amplitude n ε h a p C x j*
        ∑i:Fin 5,KFCausalIndependentRadialEntireLaplacian.second (groundWidth h/w j:ℝ)
          (groundWidth h*w j:ℝ) (groundWidth h/32) (b j) (P j) i
          (physicalPoint (increment ε h s x) y) := by
    rw [KFCausalIndependentRadialPulledLaplacian.ordered_profile_laplacian ε (a j) h (w j) (w j)
      (C j) (p j) (b j) (P j) (groundWidth_positive h hh)
      (zero_lt_one.trans_le (hw j)) (zero_lt_one.trans_le (hw j))]
    simp only [entireOutput,flow_reference ε h s x y hc,
      KFCausalGaussianHolomorphicClockWeight.clockPower,Bool.false_eq_true,if_false,if_true,
      amplitude,packet_profile]
    rw [shifted_clock ε h s x]
    ring
  change (∑j,KFCausalOrderedStaticOutputRepresentative.profile ε (a j) h (w j) (w j)
    (C j) (p j) (b j) (P j) (shifted h x) ((split 2 4).symm x))=_
  simp_rw [hrep]
  unfold transverseLaplacian
  rw [KFCausalIndependentRadialMetricLaplacian.family_neutral_laplacian]
  simp only [transverse,family,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem pairing_reference (m g k : ℝ) :
    (KFCausalCommonRealGaussianWeightedEnergy.potential m g k
      (KFCausalIndependentRadialIntegralCompletion.field y):ℂ)*
      conj (sourceProfile n ε h a w p C b P x)*staticProfile n ε h a w p C b P x=
    KFCausalIndependentRadialIntegralCompletion.pairedDensity n (groundWidth h) w w
      (increment ε h s x) b (amplitude n ε h a p C x) (fun j=>neutralPolynomial (P j))
      ε s h m g k y := by
  rw [source_reference n ε h s a w p C b P hh hw x y hc,
    static_reference n ε h s a w p C b P hh hw x y hc]
  rfl

#print axioms shifted_clock
#print axioms source_reference
#print axioms static_reference
#print axioms pairing_reference
end
end UnifiedTheory.Audit.KFCausalOrderedStaticTransverseProfile
