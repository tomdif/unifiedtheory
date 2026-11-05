/- Existing OS dynamics transported through the proved unitary enlargement
of its test space. The transported operators implement forward translations
of every positive-time Schwartz label, with no upper time restriction. -/
import UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert
import UnifiedTheory.Clay.YangMills.OSScalarDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullPositiveTimeDynamics
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open CellTranslationCovariance SchwartzTranslations KernelHilbertCompletion
open FullPositiveTimeHilbert PositiveTimeCutoff
open scoped Topology NNReal

def shift (t : ℝ≥0) (i : FullPositiveTimeReflection.Label) :
    FullPositiveTimeReflection.Label :=
  ⟨i.1, translationCLM (timeVector i.1 t) i.2.1, by
    intro x hx j
    have h := i.2.2 (x-timeVector i.1 t) hx j
    change 0 ≤ x (j,0)
    change 0 ≤ (x-timeVector i.1 t) (j,0) at h
    have he : (x-timeVector i.1 t) (j,0) = x (j,0)-t := by simp [timeVector]
    rw [he] at h
    linarith [t.coe_nonneg]⟩

@[simp] theorem shift_inclusion (t : ℝ≥0) (i : OSPositiveTimeKernel.Label) :
    shift t (inclusion i) = inclusion (OSPositiveTimeKernel.shift t i) := rfl

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)
  (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B)
  (E : OSScalarDynamics.Evolution W plane hp)

/-- This is exactly conjugation of the existing evolution, not a second
independently reconstructed semigroup. -/
def operator (t : ℝ≥0) : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) →L[ℂ]
    Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) :=
  let e := equivalence W plane hp hfull B hb
  e.toLinearIsometry.toContinuousLinearMap.comp
    ((E.operator t).comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem operator_apply (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull B hb E t v =
      equivalence W plane hp hfull B hb
        (E.operator t ((equivalence W plane hp hfull B hb).symm v)) := rfl

theorem operator_intertwines (t : ℝ≥0)
    (v : Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp)) :
    operator W plane hp hfull B hb E t (equivalence W plane hp hfull B hb v) =
      equivalence W plane hp hfull B hb (E.operator t v) := by
  rw [operator_apply, LinearIsometryEquiv.symm_apply_apply]

theorem operator_canonical_inclusion (t : ℝ≥0) (i : OSPositiveTimeKernel.Label) :
    operator W plane hp hfull B hb E t
      (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i)) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
        (inclusion (OSPositiveTimeKernel.shift t i)) := by
  rw [← equivalence_canonical W plane hp hfull B hb i, operator_intertwines,
    E.canonical_action, equivalence_canonical]

include B hb in
/-- Translating the explicit cutoff sequence also converges in the full
reflected Hilbert norm, by exact translation invariance of its L1 error. -/
theorem translated_approximation_tendsto (t : ℝ≥0) (i : FullPositiveTimeReflection.Label) :
    Tendsto (fun R => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      (shift t (inclusion (approximation R i)))) atTop
        (𝓝 (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (shift t i))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (R : ℕ) : ‖canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      (shift t (inclusion (approximation R i))) -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (shift t i)‖^2 ≤
      (B : ℝ)^(i.1+i.1) *
        (BoundedKernelDistribution.l1Seminorm volume (cutoff i.1 R i.2.1 - i.2.1))^2 := by
    have h := canonical_difference_bound W plane hfull B hb i.1
      (translationCLM (timeVector i.1 t) (cutoff i.1 R i.2.1))
      (translationCLM (timeVector i.1 t) i.2.1)
      (shift t (inclusion (approximation R i))).2.2 (shift t i).2.2
    rw [← map_sub, OSTestTranslation.l1_translation] at h
    exact h
  have hs := squeeze_zero (fun R => sq_nonneg _) hbound
    (by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      ((cutoff_l1_tendsto i.1 i.2.1).pow 2).const_mul ((B : ℝ)^(i.1+i.1)))
  have hh := Real.continuous_sqrt.tendsto 0 |>.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hh

/-- The existing evolution now acts on every unrestricted positive-time test
by its actual forward time translation. -/
theorem operator_canonical (t : ℝ≥0) (i : FullPositiveTimeReflection.Label) :
    operator W plane hp hfull B hb E t
      (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (shift t i) := by
  have hleft := (operator W plane hp hfull B hb E t).continuous.tendsto
    (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) |>.comp
      (canonical_approximation_tendsto W plane hfull B hb i)
  apply tendsto_nhds_unique hleft
  convert translated_approximation_tendsto W plane hfull B hb t i using 1
  ext R
  simp only [Function.comp_def, operator_canonical_inclusion, shift_inclusion]

theorem operator_zero
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull B hb E 0 v = v := by
  rw [operator_apply, E.zero, LinearIsometryEquiv.apply_symm_apply]

theorem operator_add (s t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull B hb E s (operator W plane hp hfull B hb E t v) =
      operator W plane hp hfull B hb E (s+t) v := by
  simp only [operator_apply, LinearIsometryEquiv.symm_apply_apply, E.add]

theorem operator_contraction (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    ‖operator W plane hp hfull B hb E t v‖ ≤ ‖v‖ := by
  rw [operator_apply, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    E.contraction t ((equivalence W plane hp hfull B hb).symm v)

theorem operator_symmetric (t : ℝ≥0)
    (v w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    inner ℂ (operator W plane hp hfull B hb E t v) w =
      inner ℂ v (operator W plane hp hfull B hb E t w) := by
  let e := equivalence W plane hp hfull B hb
  change inner ℂ (e (E.operator t (e.symm v))) w = inner ℂ v (e (E.operator t (e.symm w)))
  rw [e.inner_map_eq_flip, E.symmetric]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (e.inner_map_map (e.symm v) (E.operator t (e.symm w))).symm

theorem operator_positive (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    0 ≤ (inner ℂ v (operator W plane hp hfull B hb E t v)).re := by
  let e := equivalence W plane hp hfull B hb
  have he := e.inner_map_map (e.symm v) (E.operator t (e.symm v))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  change 0 ≤ (inner ℂ v (e (E.operator t (e.symm v)))).re
  rw [he]
  exact E.positive t (e.symm v)

theorem operator_strongly_continuous
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    Continuous (fun t => operator W plane hp hfull B hb E t v) :=
  (equivalence W plane hp hfull B hb).continuous.comp
    (E.strongly_continuous ((equivalence W plane hp hfull B hb).symm v))

end
end UnifiedTheory.Clay.YangMills.FullPositiveTimeDynamics
