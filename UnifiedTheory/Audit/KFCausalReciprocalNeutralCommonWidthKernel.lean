/- Exact reduction of every common reciprocal-width kernel to the
existing neutral kernel with charged parameter alpha*w. The factor w^2
is independent of clock position and preserves all neutral interference. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative
import UnifiedTheory.Audit.KFCausalNeutralFiniteResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralCommonWidthKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalNeutralKernel (kernel)
open KFCausalReciprocalNeutralPositiveForm (pairing)
open KFCausalNeutralExponentialProfiles
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralClockDerivative (finiteCurve totalEnergy)
open KFCausalNeutralFiniteResponse (realKernel)

theorem B_common (α w : ℝ) (r : ℂ) : B α w w r = B (α*w) 1 1 r := by
  unfold B
  push_cast
  ring

theorem C_common (α β w : ℝ) (r : ℂ) : C α β w w r = C (α*w) β 1 1 r := by
  unfold C
  rw [B_common α w r]

theorem kernel_common (α β w : ℝ) (r : ℂ) (hα : 0 < α) (hw : 0 < w)
    (hA : 0 < area r) (F G : ℂ → ℂ) :
    kernel α β w w r F G = (w:ℂ)^2*kernel (α*w) β 1 1 r F G := by
  have ha : 0 < (A α w w r).re := by rw [KFCausalReciprocalCrossGeometry.A_re]; positivity
  have hb : 0 < (B α w w r).re := by rw [KFCausalReciprocalCrossGeometry.B_re]; positivity
  have ha' : 0 < (A (α*w) 1 1 r).re := by rw [KFCausalReciprocalCrossGeometry.A_re]; positivity
  have hb' : 0 < (B (α*w) 1 1 r).re := by rw [KFCausalReciprocalCrossGeometry.B_re]; positivity
  rw [KFCausalReciprocalNeutralLaplace.kernel_joint α β w w hw.ne' hw.ne' r F G ha hb,
    KFCausalReciprocalNeutralLaplace.kernel_joint (α*w) β 1 1 (by norm_num) (by norm_num) r F G ha' hb',
    B_common,C_common]
  push_cast
  ring

theorem pairing_common (N : ℕ) (α β w : ℝ) (r : ℂ) (hα : 0 < α)
    (hw : 0 < w) (hA : 0 < area r) (c d : Fin N → ℂ) (F : Fin N → ℂ → ℂ) :
    pairing N α β (fun _ => w) r c d F =
      (w:ℂ)^2*pairing N (α*w) β (fun _ => 1) r c d F := by
  unfold pairing
  simp only [kernel_common α β w r hα hw hA,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exponent_unit (α β : ℝ) (r : ℂ) (q : Transverse) :
    KFCausalReciprocalGaussianCoordinates.exponent α β 1 r q =
      KFCausalRelativeGaussianDifferential.exponent α β 0 r q := by
  have hs : KFCausalReciprocalSqueezeFlow.squeeze 0 q = q := by
    ext i
    fin_cases i <;> simp [KFCausalReciprocalSqueezeFlow.squeeze,
      KFCausalReciprocalSqueezeFlow.diagonal,KFCausalReciprocalSqueezeFlow.offDiagonal]
  simpa only [mul_zero,neg_zero,Real.exp_zero,mul_one,hs] using
    (KFCausalReciprocalGaussianOutputs.exponent_squeeze α β 0 r q).symm

theorem factor_unit (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (k : ℕ) (q : Transverse) :
    KFCausalReciprocalNeutralSliceIntegrability.factor α β 1 r b P k q =
      profileFactor α β r (exponentialProfile b 1 P) k q := by
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,profileFactor,exponent_unit]

theorem finiteCurve_unit (N : ℕ) (ε y α β : ℝ) (b c : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (k : ℕ) (s : ℝ) (q : Transverse) :
    finiteCurve N ε y α β (fun _ => 1) b P (fun _ => c) k s q =
      profileFactor α β (scale ε y s) (finiteProfile Finset.univ b c P) k q := by
  simp only [finiteCurve,KFCausalReciprocalNeutralClockEnvelope.curve,factor_unit,
    finiteProfile_factor]
  apply Finset.sum_congr rfl
  intro i _
  unfold profileFactor exponentialProfile
  ring

theorem pairing_unit_real (N : ℕ) (ε y α β : ℝ) (b c : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (s : ℝ) :
    (pairing N α β (fun _ => 1) (scale ε y s) c c
      (fun i => exponentialProfile (b i) 1 (P i))).re = realKernel ε y α β N b c P s := by
  rw [KFCausalReciprocalNeutralKernelDerivative.pairing_totalEnergy N ε y α β
    (fun _ => 1) b P (fun _ => c) hε hy hα hβ hwidth (fun _ => le_rfl),Complex.ofReal_re]
  have he (k : ℕ) : KFCausalTransverseClockDifferentiation.energy
      (finiteCurve N ε y α β (fun _ => 1) b P (fun _ => c) k) s =
      (KFCausalNeutralFiniteGram.finiteKernel ε y α β N b c P k s).re := by
    rw [KFCausalNeutralFiniteGram.finiteKernel_re α β ε y s hα hβ hwidth hε hy]
    unfold KFCausalTransverseClockDifferentiation.energy
    simp only [finiteCurve_unit]
  simp only [totalEnergy,he,realKernel,KFCausalNeutralFiniteGram.energyKernel,Complex.add_re,
    Complex.mul_re,Complex.div_re,Complex.one_re,Complex.one_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.normSq_ofNat]
  norm_num
  ring

theorem pairing_common_real (N : ℕ) (ε y α β w : ℝ) (b c : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hw : 1 ≤ w) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (s : ℝ) :
    (pairing N α β (fun _ => w) (scale ε y s) c c
      (fun i => exponentialProfile (b i) 1 (P i))).re = w^2*realKernel ε y (α*w) β N b c P s := by
  have hw₀ : 0 < w := by linarith
  have hαw : α ≤ α*w := by nlinarith
  rw [pairing_common N α β w _ hα hw₀
    (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy),
    ← Complex.ofReal_pow,Complex.re_ofReal_mul,
    pairing_unit_real N ε y (α*w) β b c P (by positivity) hβ (hwidth.trans hαw) hε hy]

#print axioms B_common
#print axioms C_common
#print axioms kernel_common
#print axioms pairing_common
#print axioms exponent_unit
#print axioms factor_unit
#print axioms finiteCurve_unit
#print axioms pairing_unit_real
#print axioms pairing_common_real
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralCommonWidthKernel
