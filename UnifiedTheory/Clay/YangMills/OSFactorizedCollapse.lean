/- Exact factorization of the bare hierarchy collapses its actual reflected
Hilbert completion to the normalized vacuum line. The weak-coupling Wilson
application is supplied separately, from a proved concentration theorem. -/
import UnifiedTheory.Clay.YangMills.OSScalarDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSFactorizedCollapse
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion KernelHilbertRealization OSScalarDynamics
open SchwartzConfigurationTensor SchwartzConfigurationConjugation AffineCellReflection
open WilsonReflectedTensor
open scoped NNReal

def vacuumTest : CorrelationTest 0 :=
  (show HasCompactSupport (fun _ : Configuration 0 => (1 : ℂ)) from
    Set.subsingleton_of_subsingleton.isCompact).toSchwartzMap contDiff_const

@[simp] theorem vacuumTest_apply (x : Configuration 0) : vacuumTest x = 1 := rfl

def vacuumLabel : Label := ⟨0,vacuumTest,⟨0,fun _ _ j => Fin.elim0 j⟩⟩

def amplitude (d : ℕ) (i : Label) : ℂ := (d : ℂ)^i.1 * ∫ x, i.2.1 x

@[simp] theorem amplitude_vacuum (d : ℕ) : amplitude d vacuumLabel = 1 := by
  simp only [amplitude, vacuumLabel, pow_zero, one_mul, vacuumTest_apply]
  change (∫ _ : EuclideanSpace ℝ (Fin 0 × Fin 4), (1 : ℂ)) = 1
  rw [volume_euclideanSpace_eq_dirac]
  simp

theorem amplitude_shift (d : ℕ) (t : ℝ≥0) (i : Label) :
    amplitude d (shift t i) = amplitude d i := by
  unfold amplitude shift
  dsimp only
  congr 1
  exact integral_sub_right_eq_self (fun x => i.2.1 x)
    (CellTranslationCovariance.timeVector i.1 t)

theorem integral_reflectedTensor (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    (∫ z, reflectedTensor m n 0 plane f g z) = star (∫ x, f x) * ∫ y, g y := by
  rw [reflectedTensor, ← integral_concat]
  simp only [tensor_apply, split_concat]
  trans (∫ x, conjugation m (reflectionPullback m 0 plane f) x) * ∫ y, g y
  · exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x => conjugation m (reflectionPullback m 0 plane f) x) (fun y => g y)
  congr 1
  simp only [conjugation_apply, Complex.star_def]
  rw [integral_conj]
  congr 1
  simpa only [reflectionEquiv_apply, reflectionPullback_apply] using
    (reflection_preserves_volume m 0 plane).integral_comp
      (reflectionEquiv m 0 plane).measurableEmbedding (fun x => f x)

variable (W : Hierarchy) (plane : Plane) (d : ℕ)
  (hf : ∀ m (f : CorrelationTest m), W.correlation m f = (d : ℂ) ^ m * ∫ x, f x)
  (hp : Positive W plane)

include hf in
theorem kernel_factorized (i j : Label) :
    kernel W plane (i,j) = star (amplitude d i) * amplitude d j := by
  unfold kernel
  rw [hf, integral_reflectedTensor, pow_add]
  simp only [amplitude, star_mul, star_pow, star_natCast]
  ring

include hf in
theorem amplitude_inner (i j : Label) :
    inner ℂ (amplitude d i) (amplitude d j) = (positiveKernel W plane hp).value (i,j) := by
  rw [RCLike.inner_apply]
  simpa only [Complex.star_def, mul_comm] using (kernel_factorized W plane d hf i j).symm

/-- The map is defined on the actual null quotient's Hilbert completion. -/
def scalarRealization : Hilbert (positiveKernel W plane hp) →ₗᵢ[ℂ] ℂ :=
  realization _ (amplitude d) (amplitude_inner W plane d hf hp)

@[simp] theorem scalarRealization_canonical (i : Label) :
    scalarRealization W plane d hf hp (canonical (positiveKernel W plane hp) i) = amplitude d i :=
  realization_canonical _ _ _ i

/-- Every completed state is a multiple of the actual order-zero vacuum. -/
theorem every_state_vacuum_multiple (v : Hilbert (positiveKernel W plane hp)) :
    v = (scalarRealization W plane d hf hp v) •
      canonical (positiveKernel W plane hp) vacuumLabel := by
  apply (scalarRealization W plane d hf hp).injective
  rw [map_smul, scalarRealization_canonical, amplitude_vacuum, smul_eq_mul, mul_one]

include hf in
theorem vacuum_norm : ‖canonical (positiveKernel W plane hp) vacuumLabel‖ = 1 := by
  rw [← (scalarRealization W plane d hf hp).norm_map, scalarRealization_canonical, amplitude_vacuum]
  exact norm_one

include hf in
/-- There is no nonzero state orthogonal to the vacuum in this sector. -/
theorem vacuum_orthogonal_eq_zero (v : Hilbert (positiveKernel W plane hp))
    (hv : inner ℂ (canonical (positiveKernel W plane hp) vacuumLabel) v = 0) : v = 0 := by
  have he := every_state_vacuum_multiple W plane d hf hp v
  have hn : inner ℂ (canonical (positiveKernel W plane hp) vacuumLabel)
      (canonical (positiveKernel W plane hp) vacuumLabel) = 1 := by
    rw [canonical_inner]
    change kernel W plane (vacuumLabel,vacuumLabel) = 1
    rw [kernel_factorized W plane d hf, amplitude_vacuum]
    simp
  rw [he, inner_smul_right, hn, mul_one] at hv
  rw [he, hv, zero_smul]

include hf in
/-- Any OS evolution implementing these actual test shifts is the identity. -/
theorem evolution_identity (D : Evolution W plane hp) (t : ℝ≥0)
    (v : Hilbert (positiveKernel W plane hp)) : D.operator t v = v := by
  have hvac : D.operator t (canonical (positiveKernel W plane hp) vacuumLabel) =
      canonical (positiveKernel W plane hp) vacuumLabel := by
    rw [D.canonical_action]
    apply (scalarRealization W plane d hf hp).injective
    rw [scalarRealization_canonical, scalarRealization_canonical, amplitude_shift]
  rw [every_state_vacuum_multiple W plane d hf hp v, map_smul, hvac]

end
end UnifiedTheory.Clay.YangMills.OSFactorizedCollapse
