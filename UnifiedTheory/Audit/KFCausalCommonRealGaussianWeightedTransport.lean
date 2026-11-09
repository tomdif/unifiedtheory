/- Exact weighted original physical transport bound. The clock amplitudes
are frozen only for the geometric derivative; the full clock integration
by parts separately retains their motion. The source is common real, P=1. -/
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralKernel
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralWholeClock
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedTransport
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalReciprocalNeutralPositiveEnergy (coefficients)
open KFCausalWeightedReciprocalNeutralWholeClock (kernels clockPairing positiveSlice transportResponse)
open KFCausalCommonRealGaussianWeightedResponse (jointEnergy)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
variable (mass2 quartic vacuum : ℝ)

private theorem actual_geometry (n : ℕ) (α β ε y s : ℝ) (w : Fin n → ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    0 < (gamma α (scale ε y s)).re ∧
      (∀ i, 8*β*(scale ε y s).im^2 < 2*(gamma α (scale ε y s)).re*w i) ∧
      (∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area (scale ε y s)-8*β*(scale ε y s).im^2) := by
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hr : |(scale ε y s).im| < (scale ε y s).re := by
    nlinarith [sq_abs (scale ε y s).im,abs_nonneg (scale ε y s).im]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα hr
  have hf (i : Fin n) : 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area (scale ε y s)-8*β*(scale ε y s).im^2 := by
    have hreg := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
    obtain ⟨hc,ha'⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hreg
    exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha' hc).2
  refine ⟨hp,?_,hf⟩
  intro i
  have he : 2*(gamma α (scale ε y s)).re=α*KFCausalReciprocalGaussianCoordinates.area (scale ε y s) := by
    simp [gamma,KFCausalReciprocalGaussianCoordinates.area,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  nlinarith [hf i]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "y" => -h/2
local notation "fam" => KFCausalGaussianWeightedSourceKernelDerivative.familyForm mass2 quartic vacuum
local notation "fslope" => KFCausalGaussianWeightedSourceKernelDerivative.familySlope mass2 quartic vacuum

include hε hh hw hb in
theorem clockPairing_family (s : ℝ) :
    clockPairing mass2 quartic vacuum n ε h a w p C b (fun _ => 1) s=
      ((Real.pi:ℂ)/4)*fam n α β w (scale ε y s) b (coefficients n ε h a p C s) := by
  have hy : |y| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  unfold clockPairing KFCausalFiniteMatrixClockTransport.value
    KFCausalGaussianWeightedSourceKernelDerivative.familyForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [kernels,KFCausalWeightedReciprocalNeutralKernel.actual_pairKernel mass2 quartic vacuum
    ε y α β (w i) (w j) (b i) (b j) hε hy (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (hw i) (hw j)]
  simp only [coefficients,KFCausalClockResponseTransport.pair,map_mul,Complex.star_def]
  ring

include hε hh hw hb in
theorem kernels_derivative (i j : Fin n) (s : ℝ) :
    deriv (kernels mass2 quartic vacuum n ε h w b (fun _ => 1) i j) s=
      ((Real.pi:ℂ)/4)*(w i:ℂ)*(w j:ℂ)*
        KFCausalGaussianWeightedSourceKernelDerivative.pairSlope mass2 quartic vacuum
          α β (w i) (w j) (scale ε y s) (deriv (scale ε y) s) (b i) (b j) := by
  have hy : |y| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have he : kernels mass2 quartic vacuum n ε h w b (fun _ => 1) i j=
      fun t => ((Real.pi:ℂ)/4)*(w i:ℂ)*(w j:ℂ)*
        KFCausalGaussianWeightedSourceKernelDerivative.pairKernel mass2 quartic vacuum
          α β (w i) (w j) (scale ε y t) (b i) (b j) :=
    funext (KFCausalWeightedReciprocalNeutralKernel.actual_pairKernel mass2 quartic vacuum
      ε y α β (w i) (w j) (b i) (b j) hε hy (groundWidth_positive h hh)
      (neutralWidth_positive h hh) (neutralWidth_bound h) (hw i) (hw j))
  rw [he]
  obtain ⟨_,_,hf⟩ := actual_geometry n α β ε y s w (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw
  obtain ⟨hB,hC⟩ := KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) (scale ε y s)
    (neutralWidth_positive h hh) (hf i) (hf j)
  have hd := KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy
  rw [hd.deriv]
  exact ((KFCausalGaussianWeightedSourceKernelDerivative.pairKernel_derivative mass2 quartic vacuum
    hd α β (w i) (w j) (b i) (b j) hB hC).const_mul _).deriv

include hε hh hw hb in
theorem transport_family (s : ℝ) :
    transportResponse mass2 quartic vacuum n ε h a w p C b (fun _ => 1) s=
      Real.pi/4*(fslope n α β w (scale ε y s) (deriv (scale ε y) s) b
        (coefficients n ε h a p C s)).re := by
  have he : KFCausalFiniteMatrixClockTransport.transport n ε y a p C
      (kernels mass2 quartic vacuum n ε h w b (fun _ => 1)) s=
      ((Real.pi:ℂ)/4)*fslope n α β w (scale ε y s) (deriv (scale ε y) s) b
        (coefficients n ε h a p C s) := by
    unfold KFCausalFiniteMatrixClockTransport.transport KFCausalGaussianWeightedSourceKernelDerivative.familySlope
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [kernels_derivative mass2 quartic vacuum n ε h w b hε hh hw hb]
    simp only [coefficients,KFCausalClockResponseTransport.pair,map_mul,Complex.star_def]
    ring
  unfold transportResponse
  rw [he]
  simp

variable (B : ℝ) (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum)
include hε hh hw hb hmass hquartic hvacuum in
theorem positiveSlice_joint (s : ℝ) :
    positiveSlice mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s=
      Real.pi/4*jointEnergy mass2 quartic vacuum n α β w (scale ε y s) B
        (coefficients n ε h a p C s) := by
  have hy : |y| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  obtain ⟨hp,hd,_⟩ := actual_geometry n α β ε y s w (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw
  have he := KFCausalCommonRealGaussianWeightedKernel.joint_integral_eq_family mass2 quartic vacuum
    n α β B w (scale ε y s) (coefficients n ε h a p C s) (neutralWidth_positive h hh)
    hp (fun i => lt_of_lt_of_le (by norm_num) (hw i)) hd hmass hquartic hvacuum
  change (clockPairing mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s).re = _
  rw [clockPairing_family mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) hε hh hw hb,← he]
  simp only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rfl

include hε hh hw hb hmass hquartic hvacuum in
theorem positiveSlice_nonnegative (s : ℝ) :
    0 ≤ positiveSlice mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s := by
  rw [positiveSlice_joint mass2 quartic vacuum n ε h a w p C hε hh hw hb B hmass hquartic hvacuum]
  exact mul_nonneg (by positivity) (integral_nonneg (fun z =>
    KFCausalCommonRealGaussianWeightedJointEnergy.density_nonnegative mass2 quartic vacuum
      n α β B w (scale ε y s) (coefficients n ε h a p C s) z hmass hquartic hvacuum))

include hε hh hw hb hmass hquartic hvacuum in
theorem transport_bound (s : ℝ) :
    transportResponse mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s ≤
      536*fraction ε s*positiveSlice mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s := by
  have hy : |y| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  rw [transport_family mass2 quartic vacuum n ε h a w p C (fun _ => (B:ℂ)) hε hh hw hb,
    positiveSlice_joint mass2 quartic vacuum n ε h a w p C hε hh hw hb B hmass hquartic hvacuum]
  have he := KFCausalCommonRealGaussianWeightedResponse.actual_kernel_bound mass2 quartic vacuum
    n α β ε y s B w (coefficients n ε h a p C s) (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw hmass hquartic hvacuum
  convert mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ Real.pi/4) using 1
  ring

#print axioms clockPairing_family
#print axioms kernels_derivative
#print axioms transport_family
#print axioms positiveSlice_joint
#print axioms positiveSlice_nonnegative
#print axioms transport_bound
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedTransport
