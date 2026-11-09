/- Instantiate clock transport with the actual shifted transverse
Gaussian cross kernels. All derivatives and continuity are derived.
Widths, sources and complex coefficients can differ across the pair.
The identity is on a finite clock interval at a fixed transverse point;
it supplies neither a transverse lower bound nor an infinite-tail limit. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumDensity
import UnifiedTheory.Audit.KFCausalRelativeGaussianClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianKernelResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_continuous scale_derivative)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
  (profile profile_smooth slope position direction)
open UnifiedTheory.Audit.KFCausalClockResponseTransport
  (clock pair weakPair weakSlope reduced coefficient interval_response)

def transverse (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  C*profile (fun _ => 1) (scale ε y) α β b (s,q)

def transverseSlope (ε y α β : ℝ) (b : Fin 5 → ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  ((clock ε s:ℂ)*inverseClock ε y s-1)*slope (scale ε y) α β b (s,q)

def kernel (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ) (q : Transverse) (s : ℝ) : ℂ :=
  star (transverse ε y α β b C q s)*transverse ε y α' β' c D q s

def kernelDerivative (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (q : Transverse) (s : ℝ) : ℂ :=
  kernel ε y α β α' β' b c C D q s*
    (star (transverseSlope ε y α β b q s)+transverseSlope ε y α' β' c q s)

theorem transverse_derivative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (q : Transverse) (s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (transverse ε y α β b C q)
      (transverseSlope ε y α β b q s*transverse ε y α β b C q s) s := by
  have hd := (KFCausalRelativeGaussianClockDerivative.profile_clock_derivative
    (fun _ => 1) (scale ε y) α β b s q 0
    ((clock ε s:ℂ)*inverseClock ε y s-1)
    (by simpa using hasDerivAt_const s (1:ℂ)) (scale_derivative ε y s hε hy)).const_mul C
  convert hd using 1
  simp only [transverse,transverseSlope,zero_add]
  ring

theorem kernel_derivative (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
    (q : Transverse) (s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (kernel ε y α β α' β' b c C D q)
      (kernelDerivative ε y α β α' β' b c C D q s) s := by
  convert (transverse_derivative ε y α β b C q s hε hy).star.mul
    (transverse_derivative ε y α' β' c D q s hε hy) using 1
  simp only [kernelDerivative,kernel,star_mul]
  ring

private theorem transverse_continuous (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (transverse ε y α β b C q) := by
  exact continuous_const.mul ((profile_smooth (fun _ => 1) (scale ε y)
    contDiff_const (scale_smooth ε y hε hy) α β b).continuous.comp
      (continuous_id.prodMk continuous_const))

private theorem transverseSlope_continuous (ε y α β : ℝ) (b : Fin 5 → ℂ)
    (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (transverseSlope ε y α β b q) := by
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
  exact (((Complex.continuous_ofReal.comp (Real.continuous_exp.add continuous_const)).mul hi).sub
    continuous_const).mul hs

theorem gaussian_pair_factorization (ε y a a' p p' α β α' β' : ℝ)
    (b c : Fin 5 → ℂ) (C D : ℂ) (q : Transverse) (s : ℝ) :
    star (C*profile (clockAmplitude ε a p y) (scale ε y) α β b (s,q))*
      (D*profile (clockAmplitude ε a' p' y) (scale ε y) α' β' c (s,q)) =
      pair ε a a' p p' y s*kernel ε y α β α' β' b c C D q s := by
  simp only [pair,kernel,transverse,profile,one_mul,star_mul]
  ring

private theorem signed_pair_algebra (h : ℝ) (hh : h ≠ 0) (u v w z : ℂ) :
    (Complex.I/(h:ℂ))*(star u*((-Complex.I*(h:ℂ))*z*v)-
      star ((-Complex.I*(h:ℂ))*w*u)*v) = star u*v*(star w+z) := by
  simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  field_simp [Complex.ofReal_ne_zero.mpr hh]
  ring_nf
  simp [Complex.I_sq]

theorem gaussian_response_factorization (ε y h a a' p p' α β α' β' : ℝ)
    (hh : h ≠ 0) (b c : Fin 5 → ℂ) (C D : ℂ) (q : Transverse) (s : ℝ) :
    let u := C*profile (clockAmplitude ε a p y) (scale ε y) α β b (s,q)
    let v := D*profile (clockAmplitude ε a' p' y) (scale ε y) α' β' c (s,q)
    (Complex.I/(h:ℂ))*(star u*((-Complex.I*(h:ℂ))*weakSlope ε a' p' y s*v)-
      star ((-Complex.I*(h:ℂ))*weakSlope ε a p y s*u)*v) =
      kernel ε y α β α' β' b c C D q s*weakPair ε a a' p p' y s := by
  dsimp only
  rw [signed_pair_algebra h hh,gaussian_pair_factorization]
  unfold weakPair
  ring

theorem actual_kernel_interval (ε y a a' p p' α β α' β' : ℝ)
    (b c : Fin 5 → ℂ) (C D : ℂ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (l r : ℝ) :
    (∫ s in l..r, kernel ε y α β α' β' b c C D q s*weakPair ε a a' p p' y s) =
      kernel ε y α β α' β' b c C D q r*pair ε a a' p p' y r/(clock ε r:ℂ)-
      kernel ε y α β α' β' b c C D q l*pair ε a a' p p' y l/(clock ε l:ℂ)+
      ∫ s in l..r, reduced ε a a' p p' y
        (kernel ε y α β α' β' b c C D q) (kernelDerivative ε y α β α' β' b c C D q) s := by
  have hK : Continuous (kernel ε y α β α' β' b c C D q) :=
    (transverse_continuous ε y α β b C q hε hy).star.mul
      (transverse_continuous ε y α' β' c D q hε hy)
  have hK' : Continuous (kernelDerivative ε y α β α' β' b c C D q) :=
    hK.mul ((transverseSlope_continuous ε y α β b q hε hy).star.add
      (transverseSlope_continuous ε y α' β' c q hε hy))
  exact interval_response ε a a' p p' y hε hy _ _ hK hK'
    (fun s => kernel_derivative ε y α β α' β' b c C D q s hε hy) l r

#print axioms transverse_derivative
#print axioms kernel_derivative
#print axioms gaussian_pair_factorization
#print axioms gaussian_response_factorization
#print axioms actual_kernel_interval
end
end UnifiedTheory.Audit.KFCausalGaussianKernelResponse
