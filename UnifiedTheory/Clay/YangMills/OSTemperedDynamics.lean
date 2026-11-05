/- Time evolution for a continuous Schwartz hierarchy: reflection positivity
and stationarity suffice. Exponential damping of actual Schwartz translations
proves contraction and null-space descent; no uniform bare L1 bound is used. -/
import UnifiedTheory.Clay.YangMills.OSDampedKernelShift
import UnifiedTheory.Clay.YangMills.OSScalarDynamics
import UnifiedTheory.Clay.YangMills.SchwartzTranslationGrowth
import UnifiedTheory.Clay.YangMills.SchwartzTensorContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSTemperedDynamics
noncomputable section
open Filter ContinuumControl PeriodicLattice4 CellTranslationCovariance
open OSPositiveTimeKernel PositiveKernelForm KernelHilbertCompletion
open SchwartzTranslations WilsonReflectedTensor
open scoped Topology NNReal

theorem timeVector_ray (m : ℕ) (t : ℝ) :
    timeVector m (t+t) = t • timeVector m 2 := by
  ext j
  change (if j.2 = 0 then t+t else 0) = t * (if j.2 = 0 then 2 else 0)
  split_ifs <;> ring

theorem reflectedTensor_smul_right (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) (c : ℂ) :
    reflectedTensor m n 0 plane f (c • g) = c • reflectedTensor m n 0 plane f g := by
  ext x
  simp only [reflectedTensor, SchwartzConfigurationTensor.tensor_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem reflectedTensor_zero_right (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) : reflectedTensor m n 0 plane f 0 = 0 := by
  ext x
  simp only [reflectedTensor, SchwartzConfigurationTensor.tensor_apply,
    SchwartzMap.zero_apply, mul_zero]

/-- Only one test is translated after stationarity moves the reflected shift
to the right. Its exponentially damped Schwartz limit is zero. -/
theorem kernel_damped_decay (W : Hierarchy) (plane : Plane) (ht : Stationary W)
    (eps : ℝ) (heps : 0 < eps) (i j : Label) :
    Tendsto (fun t : ℝ≥0 => (Real.exp (-eps*(t:ℝ)) : ℂ) *
      kernel W plane (shift t i,shift t j)) atTop (𝓝 0) := by
  have hg := SchwartzTranslationGrowth.damped_nnreal_translation_tendsto_zero
    j.2.1 (timeVector j.1 2) eps heps
  have hten := SchwartzTensorContinuity.reflected_tensor_tendsto i.1 j.1 0 plane
    (fun _ : ℝ≥0 => i.2.1)
    (fun t : ℝ≥0 => (Real.exp (-eps*(t:ℝ)) : ℂ) •
      translationCLM ((t:ℝ) • timeVector j.1 2) j.2.1)
    i.2.1 0 tendsto_const_nhds hg
  have hlim := (W.correlation (i.1+j.1)).continuous.continuousAt.tendsto.comp hten
  simp only [reflectedTensor_zero_right, map_zero] at hlim
  convert hlim using 1
  funext t
  rw [kernel_shift W plane ht t t i j]
  change _ = W.correlation (i.1+j.1)
    (reflectedTensor i.1 j.1 0 plane i.2.1
      ((Real.exp (-eps*(t:ℝ)) : ℂ) •
        translationCLM ((t:ℝ) • timeVector j.1 2) j.2.1))
  rw [reflectedTensor_smul_right, map_smul, smul_eq_mul]
  change _ * W.correlation (i.1+j.1)
    (reflectedTensor i.1 j.1 0 plane i.2.1
      (translationCLM (timeVector j.1 ((t+t:ℝ≥0):ℝ)) j.2.1)) = _
  rw [NNReal.coe_add, timeVector_ray]

def shiftAlgebra (W : Hierarchy) (plane : Plane) (hp : Positive W plane)
    (ht : Stationary W) : OSDampedKernelShift.ShiftAlgebra (positiveKernel W plane hp) where
  shift := shift
  zero := shift_zero
  add := shift_add
  symmetric := kernel_symmetric W plane ht

theorem dampedDecay (W : Hierarchy) (plane : Plane) (hp : Positive W plane)
    (ht : Stationary W) :
    OSDampedKernelShift.DampedDecay (positiveKernel W plane hp) (shiftAlgebra W plane hp ht) :=
  kernel_damped_decay W plane ht

/-- This bounded shift data is derived from the actual tempered kernel;
the bound is its original canonical-state norm. -/
def shiftData (W : Hierarchy) (plane : Plane) (hp : Positive W plane)
    (ht : Stationary W) : OSKernelShift.ShiftData (positiveKernel W plane hp) :=
  OSDampedKernelShift.boundedData _ (shiftAlgebra W plane hp ht) (dampedDecay W plane hp ht)

/-- A strongly continuous positive symmetric contraction semigroup on the
actual OS Hilbert completion, without a bare-observable bound. -/
def evolution (W : Hierarchy) (plane : Plane) (hp : Positive W plane)
    (ht : Stationary W) : OSScalarDynamics.Evolution W plane hp where
  operator := OSKernelShift.operator _ (shiftData W plane hp ht)
  canonical_action := OSKernelShift.operator_canonical _ _
  zero := OSKernelShift.operator_zero _ _
  add := OSKernelShift.operator_add _ _
  contraction := OSKernelShift.operator_contraction _ _
  symmetric := OSStrongContinuity.operator_symmetric _ _
  positive := OSStrongContinuity.operator_positive _ _
  strongly_continuous := OSStrongContinuity.operator_continuous _ _
    (kernel_shift_continuous W plane)

theorem null_descent (W : Hierarchy) (plane : Plane) (hp : Positive W plane)
    (ht : Stationary W) (t : ℝ≥0) (x : Formal (positiveKernel W plane hp))
    (hx : embed (positiveKernel W plane hp) x = 0) :
    embed (positiveKernel W plane hp)
      (OSKernelShift.formal _ (shiftData W plane hp ht) t x) = 0 :=
  OSKernelShift.formal_null _ _ t x hx

end
end UnifiedTheory.Clay.YangMills.OSTemperedDynamics
