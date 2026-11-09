/- Joint continuity of actual polynomial transverse factors and their
clock derivatives under continuous clock, source and position parameters. -/
import UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialKernelJointContinuity
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential (inverseClock inverseClock_continuous)
open UnifiedTheory.Audit.KFCausalPolynomialKernelResponse (weight weightDerivative transverse transverseDerivative)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor factorDerivative)

variable {X : Type*} [TopologicalSpace X] (ε y α β : ℝ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (s : X → ℝ) (q : X → Transverse) (b : X → Fin 5 → ℂ) (C : X → ℂ)
  (hs : Continuous s) (hq : Continuous q) (hb : Continuous b) (hC : Continuous C)
  (P : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : ℕ)

include hε hy hs hq hb hC in
theorem factor_continuous :
    Continuous (fun t => factor ε y α β (b t) (C t) P l n (q t) (s t)) := by
  have hr := (scale_smooth ε y hε hy).continuous.comp hs
  have hp (i : Fin 5) : Continuous (fun t => position (scale ε y (s t)) (q t) i) := by
    unfold position
    split_ifs <;> fun_prop
  have he : Continuous (fun t => KFCausalRelativeGaussianDifferential.exponent α β (b t)
      (scale ε y (s t)) (q t)) := by
    unfold KFCausalRelativeGaussianDifferential.exponent
    fun_prop
  exact ((Complex.continuous_ofReal.comp (l.continuous.comp hq)).pow n).mul
    ((P.continuous.comp (hp 4)).mul (hC.mul (by simpa only
      [KFCausalRelativeGaussianDifferential.profile,one_mul] using he.cexp)))

include hε hy hs hq hb hC in
theorem factorDerivative_continuous :
    Continuous (fun t => factorDerivative ε y α β (b t) (C t) P l n (q t) (s t)) := by
  have hr := (scale_smooth ε y hε hy).continuous.comp hs
  have hi := (inverseClock_continuous ε y hε hy).comp hs
  have hp (i : Fin 5) : Continuous (fun t => position (scale ε y (s t)) (q t) i) := by
    unfold position
    split_ifs <;> fun_prop
  have hd (i : Fin 5) : Continuous (fun t => direction (scale ε y (s t)) (q t) i) := by
    unfold direction
    split_ifs <;> fun_prop
  have he : Continuous (fun t => KFCausalRelativeGaussianDifferential.exponent α β (b t)
      (scale ε y (s t)) (q t)) := by
    unfold KFCausalRelativeGaussianDifferential.exponent
    fun_prop
  have hg : Continuous (fun t => KFCausalGaussianKernelResponse.transverse ε y α β (b t) (C t) (q t) (s t)) := by
    simpa only [KFCausalGaussianKernelResponse.transverse,
      KFCausalRelativeGaussianDifferential.profile,one_mul] using hC.mul he.cexp
  have hsl : Continuous (fun t => KFCausalRelativeGaussianDifferential.slope
      (scale ε y) α β (b t) (s t,q t)) := by
    unfold KFCausalRelativeGaussianDifferential.slope
    fun_prop
  have hc : Continuous (fun t => ((KFCausalClockResponseTransport.clock ε (s t):ℂ)*
      inverseClock ε y (s t)-1)) := by
    unfold KFCausalClockResponseTransport.clock
    fun_prop
  have hw : Continuous (fun t => weight ε y P (q t) (s t)) := P.continuous.comp (hp 4)
  have hwd : Continuous (fun t => weightDerivative ε y P (q t) (s t)) :=
    (P.derivative.continuous.comp (hp 4)).mul (hc.mul (hd 4))
  exact ((Complex.continuous_ofReal.comp (l.continuous.comp hq)).pow n).mul
    ((hwd.mul hg).add (hw.mul ((hc.mul hsl).mul hg)))

#print axioms factor_continuous
#print axioms factorDerivative_continuous
end
end UnifiedTheory.Audit.KFCausalPolynomialKernelJointContinuity
