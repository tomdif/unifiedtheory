/- Clock derivatives and finite-interval response transport for actual
polynomial Gaussian cross kernels. The differentiated polynomial retains
the complex neutral shear. No derivative or boundary premise is supplied. -/
import UnifiedTheory.Audit.KFCausalGaussianKernelResponse
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_continuous scale_derivative)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
  (position direction profile slope)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalClockResponseTransport
  (clock pair weakPair reduced interval_response)

def weight (ε y : ℝ) (P : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  P.eval (position (scale ε y s) q 4)

def weightDerivative (ε y : ℝ) (P : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  P.derivative.eval (position (scale ε y s) q 4)*
    (((clock ε s:ℂ)*inverseClock ε y s-1)*direction (scale ε y s) q 4)

theorem weight_derivative (ε y : ℝ) (P : Polynomial ℂ) (q : Transverse)
    (s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (weight ε y P q) (weightDerivative ε y P q s) s := by
  have hp := KFCausalRelativeGaussianClockDerivative.position_clock_derivative
    (scale ε y) s ((clock ε s:ℂ)*inverseClock ε y s-1)
    (scale_derivative ε y s hε hy) q 4
  simpa only [weight,weightDerivative,Function.comp_def,smul_eq_mul,mul_comm] using
    (P.hasDerivAt (position (scale ε y s) q 4)).scomp s hp

theorem weightDerivative_continuous (ε y : ℝ) (P : Polynomial ℂ)
    (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (weightDerivative ε y P q) := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hi := inverseClock_continuous ε y hε hy
  have hp : Continuous (fun s => position (scale ε y s) q 4) := by
    unfold position
    simp only [ite_true]
    fun_prop
  have hd : Continuous (fun s => direction (scale ε y s) q 4) := by
    unfold direction
    simp only [ite_true]
    fun_prop
  exact (P.derivative.continuous.comp hp).mul
    ((((Complex.continuous_ofReal.comp (Real.continuous_exp.add continuous_const)).mul hi).sub
      continuous_const).mul hd)

def transverse (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  weight ε y P q s*KFCausalGaussianKernelResponse.transverse ε y α β b C q s

def transverseDerivative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  weightDerivative ε y P q s*KFCausalGaussianKernelResponse.transverse ε y α β b C q s+
    weight ε y P q s*(KFCausalGaussianKernelResponse.transverseSlope ε y α β b q s*
      KFCausalGaussianKernelResponse.transverse ε y α β b C q s)

theorem transverse_derivative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (transverse ε y α β b C P q)
      (transverseDerivative ε y α β b C P q s) s :=
  (weight_derivative ε y P q s hε hy).mul
    (KFCausalGaussianKernelResponse.transverse_derivative ε y α β b C q s hε hy)

theorem transverse_continuous (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (transverse ε y α β b C P q) :=
  continuous_iff_continuousAt.mpr
    (fun s => (transverse_derivative ε y α β b C P q s hε hy).continuousAt)

theorem transverseDerivative_continuous (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (transverseDerivative ε y α β b C P q) := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hi := inverseClock_continuous ε y hε hy
  have hp (i : Fin 5) : Continuous (fun s => position (scale ε y s) q i) := by
    unfold position
    split_ifs <;> fun_prop
  have hd (i : Fin 5) : Continuous (fun s => direction (scale ε y s) q i) := by
    unfold direction
    split_ifs <;> fun_prop
  have hs : Continuous (fun s => slope (scale ε y) α β b (s,q)) := by
    unfold KFCausalRelativeGaussianDifferential.slope
    exact continuous_finset_sum _ (fun i _ =>
      (continuous_const.sub (continuous_const.mul (hp i))).mul (hd i))
  have ht : Continuous (KFCausalGaussianKernelResponse.transverse ε y α β b C q) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (KFCausalGaussianKernelResponse.transverse_derivative ε y α β b C q s hε hy).continuousAt)
  have hts : Continuous (KFCausalGaussianKernelResponse.transverseSlope ε y α β b q) :=
    (((Complex.continuous_ofReal.comp (Real.continuous_exp.add continuous_const)).mul hi).sub
      continuous_const).mul hs
  exact ((weightDerivative_continuous ε y P q hε hy).mul ht).add
    ((P.continuous.comp (hp 4)).mul (hts.mul ht))

def kernel (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (P Q : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  star (transverse ε y α β b C P q s)*transverse ε y α' β' c D Q q s

def kernelDerivative (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (P Q : Polynomial ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  star (transverseDerivative ε y α β b C P q s)*transverse ε y α' β' c D Q q s+
    star (transverse ε y α β b C P q s)*transverseDerivative ε y α' β' c D Q q s

theorem kernel_derivative (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (P Q : Polynomial ℂ) (q : Transverse) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (kernel ε y α β α' β' b c C D P Q q)
      (kernelDerivative ε y α β α' β' b c C D P Q q s) s :=
  (transverse_derivative ε y α β b C P q s hε hy).star.mul
    (transverse_derivative ε y α' β' c D Q q s hε hy)

theorem kernel_factorization (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (P Q : Polynomial ℂ) (q : Transverse) (s : ℝ) :
    kernel ε y α β α' β' b c C D P Q q s =
      star (weight ε y P q s)*weight ε y Q q s*
        KFCausalGaussianKernelResponse.kernel ε y α β α' β' b c C D q s := by
  simp only [kernel,transverse,KFCausalGaussianKernelResponse.kernel,star_mul]
  ring

theorem profile_factorization (ε y a p α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (P : Polynomial ℂ) (q : Transverse) (s : ℝ) :
    clockAmplitude ε a p y s*transverse ε y α β b C P q s =
      weight ε y P q s*(C*profile (clockAmplitude ε a p y) (scale ε y) α β b (s,q)) := by
  simp only [transverse,KFCausalGaussianKernelResponse.transverse,profile,one_mul]
  ring

theorem actual_kernel_interval (ε y a a' p p' α β α' β' : ℝ)
    (b c : Fin 5 → ℂ) (C D : ℂ) (P Q : Polynomial ℂ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (l r : ℝ) :
    (∫ s in l..r, kernel ε y α β α' β' b c C D P Q q s*weakPair ε a a' p p' y s) =
      kernel ε y α β α' β' b c C D P Q q r*pair ε a a' p p' y r/(clock ε r:ℂ)-
      kernel ε y α β α' β' b c C D P Q q l*pair ε a a' p p' y l/(clock ε l:ℂ)+
      ∫ s in l..r, reduced ε a a' p p' y
        (kernel ε y α β α' β' b c C D P Q q)
        (kernelDerivative ε y α β α' β' b c C D P Q q) s := by
  have hT := transverse_continuous ε y α β b C P q hε hy
  have hU := transverse_continuous ε y α' β' c D Q q hε hy
  have hTd := transverseDerivative_continuous ε y α β b C P q hε hy
  have hUd := transverseDerivative_continuous ε y α' β' c D Q q hε hy
  exact interval_response ε a a' p p' y hε hy _ _ (hT.star.mul hU)
    ((hTd.star.mul hU).add (hT.star.mul hUd))
    (fun s => kernel_derivative ε y α β α' β' b c C D P Q q s hε hy) l r

#print axioms weight_derivative
#print axioms weightDerivative_continuous
#print axioms transverse_derivative
#print axioms transverse_continuous
#print axioms transverseDerivative_continuous
#print axioms kernel_derivative
#print axioms kernel_factorization
#print axioms profile_factorization
#print axioms actual_kernel_interval
end
end UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
