/- Exact whole-space attachment of the original finite-packet potential/static
pairing to its physical transverse differential density. Absolute integrability
comes from the actual original Hilbert outputs before changing coordinates. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalMeasure
import UnifiedTheory.Audit.KFCausalOrderedStaticTransverseProfile

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticTransverseIntegral
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalIndependentRadialTransverseRegularity (RealSpace)
open KFCausalIndependentRadialPhysicalPolynomial (neutralPolynomial)
open KFCausalOrderedStaticPotentialPairing (field sourceProfile staticProfile)
open KFCausalIndependentRadialPhysicalMeasure (inverse)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalCommonRealGaussianWeightedEnergy (potential)

def clockIncrement (ε : ℝ) (hε : 0<ε) (h q : ℝ) : ℂ :=
  KFCausalComplexClockInverse.complexInverse ε
    (KFCausalTwoShearClockQuotient.shift (h/2) (q:ℂ))-((chartIso ε hε).symm q:ℂ)

def clockAmplitude (n : ℕ) (ε h : ℝ) (a p : Fin n→ℝ) (C : Fin n→ℂ)
    (q : ℝ) : Fin n→ℂ := fun j=>
  KFCausalIndependentRadialPulledLaplacian.scalar ε (a j) (groundWidth h) (C j) (p j)
    (KFCausalTwoShearClockQuotient.shift (h/2) (q:ℂ))

def originalDensity (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hε : 0<ε) (m g k : ℝ) (x : Product) : ℂ :=
  (potential m g k (field ε hε x):ℂ)*conj (sourceProfile n ε h a w p C b P x)*
    staticProfile n ε h a w p C b P x

def transverseDensity (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hε : 0<ε) (m g k q : ℝ) (y : RealSpace) : ℂ :=
  KFCausalIndependentRadialIntegralCompletion.pairedDensity n (groundWidth h) w w
    (clockIncrement ε hε h q) b (clockAmplitude n ε h a p C q)
    (fun j=>neutralPolynomial (P j)) ε ((chartIso ε hε).symm q) h m g k y

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10) (m g k : ℝ)

include ha hh hw hb in
theorem original_integrable : Integrable (originalDensity n ε h a w p C b P hε m g k) := by
  have h0 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 0
  have h2 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 2
  have h4 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 4
  apply (((h0.const_mul (k:ℂ)).add (h2.const_mul ((m/2:ℝ):ℂ))).add
    (h4.const_mul ((g/4:ℝ):ℂ))).congr
  filter_upwards with x
  simp only [Pi.add_apply,originalDensity,potential,map_mul,map_pow,Complex.conj_ofReal,
    pow_zero,one_mul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

include hh hw in
theorem inverse_density (q : ℝ) (y : RealSpace) :
    originalDensity n ε h a w p C b P hε m g k
      (inverse ε hε (momentumScale h) q y)=
    transverseDensity n ε h a w p C b P hε m g k q y := by
  unfold originalDensity
  rw [KFCausalIndependentRadialPhysicalMeasure.inverse_field]
  exact KFCausalOrderedStaticTransverseProfile.pairing_reference n ε h
    ((chartIso ε hε).symm q) a w p C b P hh hw
    (inverse ε hε (momentumScale h) q y) y
    (by simpa only [Complex.ofReal_neg] using
          (KFCausalIndependentRadialPhysicalMeasure.inverse_coordinate ε hε
            (momentumScale h) q (momentumScale_ne_zero h hh) y)) m g k

include ha hh hw hb in
theorem transverse_integrable : Integrable (fun z:ℝ×RealSpace=>
    transverseDensity n ε h a w p C b P hε m g k z.1 z.2) := by
  have hi := (KFCausalIndependentRadialPhysicalMeasure.integrable_inverse_iff ε hε
    (momentumScale h) (momentumScale_ne_zero h hh)
    (originalDensity n ε h a w p C b P hε m g k)).mpr
      (original_integrable n ε h a w p C b P hε ha hh hw hb m g k)
  exact hi.congr (Filter.Eventually.of_forall (fun z=>
    inverse_density n ε h a w p C b P hε hh hw m g k z.1 z.2))

include ha hh hw hb in
theorem integral_eq_transverse :
    (∫x:Product,originalDensity n ε h a w p C b P hε m g k x)=
    (|momentumScale h|^2)⁻¹ • ∫q:ℝ,∫y:RealSpace,
      transverseDensity n ε h a w p C b P hε m g k q y := by
  rw [KFCausalIndependentRadialPhysicalMeasure.integral_inverse ε hε (momentumScale h)
    (momentumScale_ne_zero h hh) _
    (original_integrable n ε h a w p C b P hε ha hh hw hb m g k)]
  congr 1
  apply integral_congr_ae
  filter_upwards with q
  apply integral_congr_ae
  filter_upwards with y
  exact inverse_density n ε h a w p C b P hε hh hw m g k q y

#print axioms original_integrable
#print axioms inverse_density
#print axioms transverse_integrable
#print axioms integral_eq_transverse
end
end UnifiedTheory.Audit.KFCausalOrderedStaticTransverseIntegral
