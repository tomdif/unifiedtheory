/- The normalized vacuum and its invariant orthogonal sector for the actual
OS evolution. No factorization or uniqueness of the vacuum is assumed. -/
import UnifiedTheory.Clay.YangMills.OSFactorizedCollapse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSVacuumSector
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSFactorizedCollapse
open WilsonReflectedTensor
open scoped NNReal

theorem shift_vacuum (t : ℝ≥0) : shift t vacuumLabel = vacuumLabel := by
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  ext x
  simp only [shift, vacuumLabel, SchwartzTranslations.translationCLM_apply, vacuumTest_apply]

variable (W : Hierarchy) (plane : Plane) (hp : Positive W plane)

def vacuum : Hilbert (positiveKernel W plane hp) :=
  canonical (positiveKernel W plane hp) vacuumLabel

theorem kernel_vacuum
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    (positiveKernel W plane hp).value (vacuumLabel,vacuumLabel) = 1 := by
  change W.correlation 0 (reflectedTensor 0 0 0 plane vacuumTest vacuumTest) = 1
  rw [hn, integral_reflectedTensor 0 0 plane vacuumTest vacuumTest]
  have hi : (∫ x, vacuumTest x) = (1 : ℂ) := by
    simpa only [amplitude, vacuumLabel, pow_zero, one_mul] using amplitude_vacuum 0
  rw [hi]
  simp

theorem vacuum_norm
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    ‖vacuum W plane hp‖ = 1 :=
  KernelHilbertCompletion.vacuum_norm _ vacuumLabel (kernel_vacuum W plane hp hn)

theorem vacuum_inner
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    inner ℂ (vacuum W plane hp) (vacuum W plane hp) = 1 := by
  change inner ℂ (canonical _ vacuumLabel) (canonical _ vacuumLabel) = 1
  rw [canonical_inner, kernel_vacuum W plane hp hn]

theorem evolution_vacuum (D : Evolution W plane hp) (t : ℝ≥0) :
    D.operator t (vacuum W plane hp) = vacuum W plane hp := by
  unfold vacuum
  rw [D.canonical_action, shift_vacuum]

theorem inner_vacuum_evolution (D : Evolution W plane hp) (t : ℝ≥0)
    (v : Hilbert (positiveKernel W plane hp)) :
    inner ℂ (vacuum W plane hp) (D.operator t v) = inner ℂ (vacuum W plane hp) v := by
  rw [← D.symmetric, evolution_vacuum]

def centered (v : Hilbert (positiveKernel W plane hp)) : Hilbert (positiveKernel W plane hp) :=
  v - (inner ℂ (vacuum W plane hp) v) • vacuum W plane hp

theorem centered_orthogonal
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (v : Hilbert (positiveKernel W plane hp)) :
    inner ℂ (vacuum W plane hp) (centered W plane hp v) = 0 := by
  rw [centered, inner_sub_right, inner_smul_right, vacuum_inner W plane hp hn,
    mul_one, sub_self]

theorem centered_vacuum
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    centered W plane hp (vacuum W plane hp) = 0 := by
  rw [centered, vacuum_inner W plane hp hn, one_smul, sub_self]

theorem centered_idempotent
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (v : Hilbert (positiveKernel W plane hp)) :
    centered W plane hp (centered W plane hp v) = centered W plane hp v := by
  conv_lhs => rw [centered]
  rw [centered_orthogonal W plane hp hn, zero_smul, sub_zero]

theorem evolution_centered (D : Evolution W plane hp) (t : ℝ≥0)
    (v : Hilbert (positiveKernel W plane hp)) :
    D.operator t (centered W plane hp v) = centered W plane hp (D.operator t v) := by
  simp only [centered, map_sub, map_smul, evolution_vacuum,
    inner_vacuum_evolution]

theorem preserves_vacuum_orthogonal (D : Evolution W plane hp) (t : ℝ≥0)
    (v : Hilbert (positiveKernel W plane hp))
    (hv : inner ℂ (vacuum W plane hp) v = 0) :
    inner ℂ (vacuum W plane hp) (D.operator t v) = 0 := by
  rw [inner_vacuum_evolution, hv]

end
end UnifiedTheory.Clay.YangMills.OSVacuumSector
