/- Whole-clock lower bound for the actual original finite-packet pairing.
Both whole-space integrability statements are derived from actual L2 outputs.
This is a finite-family estimate, not an assertion of an operator core. -/
import UnifiedTheory.Audit.KFCausalOrderedStaticTransverseIntegral

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticIntegratedLower
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalIndependentRadialTransverseRegularity (RealSpace)
open KFCausalIndependentRadialPhysicalPolynomial (neutralPolynomial)
open KFCausalOrderedStaticPotentialPairing (field sourceProfile halfOutput)
open KFCausalIndependentRadialPhysicalMeasure (inverse)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalCommonRealGaussianWeightedEnergy (potential)
open KFCausalOrderedStaticTransverseIntegral

def originalEnergy (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hε : 0<ε) (m g k : ℝ) (x : Product) : ℝ :=
  potential m g k (field ε hε x)*‖sourceProfile n ε h a w p C b P x‖^2

def transverseEnergy (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hε : 0<ε) (m g k q : ℝ) (y : RealSpace) : ℝ :=
  KFCausalIndependentRadialIntegralCompletion.energyDensity n (groundWidth h) w w
    (clockIncrement ε hε h q) b (clockAmplitude n ε h a p C q)
    (fun j=>neutralPolynomial (P j)) m g k y

private theorem real_power_norm (t : ℝ) (z : ℂ) (j : ℕ) :
    ‖(t:ℂ)^j*z‖^2=t^(2*j)*‖z‖^2 := by
  rw [norm_mul,mul_pow,norm_pow,←pow_mul,mul_comm j 2,pow_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [←pow_mul]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10) (m g k : ℝ)

include ha hh hw hb in
private theorem channel_integrable (j : ℕ) : Integrable (fun x:Product=>
    (field ε hε x)^(2*j)*‖sourceProfile n ε h a w p C b P x‖^2) := by
  have hm := (Lp.memLp (KFCausalClockFloorMixedRadial.clockMixed ε hε
    (halfOutput n ε h a w p C b P hε ha hh hw hb j))).ae_eq
      (KFCausalOrderedStaticPotentialPairing.halfOutput_coe n ε h a w p C b P
        hε ha hh hw hb j)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [real_power_norm] using hi

include ha hh hw hb in
theorem energy_integrable : Integrable (originalEnergy n ε h a w p C b P hε m g k) := by
  have h0 := channel_integrable n ε h a w p C b P hε ha hh hw hb 0
  have h1 := channel_integrable n ε h a w p C b P hε ha hh hw hb 1
  have h2 := channel_integrable n ε h a w p C b P hε ha hh hw hb 2
  apply (((h0.const_mul k).add (h1.const_mul (m/2))).add (h2.const_mul (g/4))).congr
  filter_upwards with x
  simp only [Pi.add_apply,originalEnergy,potential]
  ring

include hh hw in
theorem inverse_energy (q : ℝ) (y : RealSpace) :
    originalEnergy n ε h a w p C b P hε m g k
      (inverse ε hε (momentumScale h) q y)=
    transverseEnergy n ε h a w p C b P hε m g k q y := by
  unfold originalEnergy
  rw [KFCausalIndependentRadialPhysicalMeasure.inverse_field,
    KFCausalOrderedStaticTransverseProfile.source_reference n ε h
      ((chartIso ε hε).symm q) a w p C b P hh hw
      (inverse ε hε (momentumScale h) q y) y
      (by simpa only [Complex.ofReal_neg] using
            (KFCausalIndependentRadialPhysicalMeasure.inverse_coordinate ε hε
              (momentumScale h) q (momentumScale_ne_zero h hh) y))]
  rfl

include ha hh hw hb in
theorem transverse_energy_integrable : Integrable (fun z:ℝ×RealSpace=>
    transverseEnergy n ε h a w p C b P hε m g k z.1 z.2) := by
  have hi := (KFCausalIndependentRadialPhysicalMeasure.integrable_inverse_iff ε hε
    (momentumScale h) (momentumScale_ne_zero h hh)
    (originalEnergy n ε h a w p C b P hε m g k)).mpr
      (energy_integrable n ε h a w p C b P hε ha hh hw hb m g k)
  exact hi.congr (Filter.Eventually.of_forall (fun z=>
    inverse_energy n ε h a w p C b P hε hh hw m g k z.1 z.2))

include ha hh hw hb in
theorem energy_integral_eq :
    (∫x:Product,originalEnergy n ε h a w p C b P hε m g k x)=
    (|momentumScale h|^2)⁻¹*(∫q:ℝ,∫y:RealSpace,
      transverseEnergy n ε h a w p C b P hε m g k q y) := by
  rw [KFCausalIndependentRadialPhysicalMeasure.integral_inverse ε hε (momentumScale h)
    (momentumScale_ne_zero h hh) _
    (energy_integrable n ε h a w p C b P hε ha hh hw hb m g k),smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with q
  apply integral_congr_ae
  filter_upwards with y
  exact inverse_energy n ε h a w p C b P hε hh hw m g k q y

theorem increment_bound (ε h q : ℝ) (hε : 0<ε) (hb : |h|≤ε/10) :
    ‖clockIncrement ε hε h q‖≤1/20 := by
  have hi := KFCausalIndependentRadialTransverseLines.actual_half_increment ε h q hε hb
  simpa only [KFCausalComplexClockInverse.complexInverse_real ε hε q] using hi

include ha hh hw hb in
theorem integrated_lower (hm : 0≤m) (hg : 0≤g) (hk : 0<k) :
    -((2*h^2/ε)*(12+(m+3*g)/k))*(∫x:Product,
      originalEnergy n ε h a w p C b P hε m g k x)≤
    (∫x:Product,originalDensity n ε h a w p C b P hε m g k x).re := by
  have hE := transverse_energy_integrable n ε h a w p C b P hε ha hh hw hb m g k
  have hD := transverse_integrable n ε h a w p C b P hε ha hh hw hb m g k
  have hDi : Integrable (fun q:ℝ=>∫y:RealSpace,
      transverseDensity n ε h a w p C b P hε m g k q y) := hD.integral_prod_left
  have hr : (∫q:ℝ,(∫y:RealSpace,transverseDensity n ε h a w p C b P hε m g k q y).re)=
      (∫q:ℝ,∫y:RealSpace,transverseDensity n ε h a w p C b P hε m g k q y).re :=
    integral_re hDi
  have hp (q:ℝ) := KFCausalIndependentRadialIntegralCompletion.positive_vacuum_integral_lower
    n (groundWidth h) w w (clockIncrement ε hε h q) b (clockAmplitude n ε h a p C q)
    (fun j=>neutralPolynomial (P j)) (groundWidth_positive h hh)
    (fun j=>zero_lt_one.trans_le (hw j)) hw (increment_bound ε h q hε hb)
    ε ((chartIso ε hε).symm q) h m g k hε hm hg hk
  have hi : -((2*h^2/ε)*(12+(m+3*g)/k))*(∫q:ℝ,∫y:RealSpace,
      transverseEnergy n ε h a w p C b P hε m g k q y)≤
      (∫q:ℝ,∫y:RealSpace,transverseDensity n ε h a w p C b P hε m g k q y).re := by
    rw [←integral_const_mul,←hr]
    exact integral_mono (hE.integral_prod_left.const_mul _) hDi.re hp
  rw [energy_integral_eq n ε h a w p C b P hε ha hh hw hb m g k,
    integral_eq_transverse n ε h a w p C b P hε ha hh hw hb m g k,Complex.smul_re,
    smul_eq_mul]
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (sq_nonneg |momentumScale h|))

#print axioms energy_integrable
#print axioms inverse_energy
#print axioms transverse_energy_integrable
#print axioms energy_integral_eq
#print axioms increment_bound
#print axioms integrated_lower
end
end UnifiedTheory.Audit.KFCausalOrderedStaticIntegratedLower
