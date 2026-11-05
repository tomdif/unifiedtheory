/- Time evolution on the full positive-time Schwartz Hilbert space.
The proved Schwartz-density equivalence removes the earlier bare L1 hypothesis. -/
import UnifiedTheory.Clay.YangMills.FullSchwartzHilbert
import UnifiedTheory.Clay.YangMills.FullPositiveTimeDynamics
import UnifiedTheory.Clay.YangMills.OSScalarDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullSchwartzDynamics
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open CellTranslationCovariance SchwartzTranslations KernelHilbertCompletion
open FullPositiveTimeHilbert (inclusion)
open FullSchwartzHilbert
open FullPositiveTimeDynamics (shift shift_inclusion)
open scoped Topology NNReal

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)
  (E : OSScalarDynamics.Evolution W plane hp)

/-- This is exactly conjugation of the existing evolution, not a second
independently reconstructed semigroup. -/
def operator (t : ℝ≥0) : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) →L[ℂ]
    Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) :=
  let e := equivalence W plane hp hfull
  e.toLinearIsometry.toContinuousLinearMap.comp
    ((E.operator t).comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem operator_apply (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull E t v =
      equivalence W plane hp hfull
        (E.operator t ((equivalence W plane hp hfull).symm v)) := rfl

theorem operator_intertwines (t : ℝ≥0)
    (v : Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp)) :
    operator W plane hp hfull E t (equivalence W plane hp hfull v) =
      equivalence W plane hp hfull (E.operator t v) := by
  rw [operator_apply, LinearIsometryEquiv.symm_apply_apply]

theorem operator_canonical_inclusion (t : ℝ≥0) (i : OSPositiveTimeKernel.Label) :
    operator W plane hp hfull E t
      (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i)) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
        (inclusion (OSPositiveTimeKernel.shift t i)) := by
  rw [← equivalence_canonical W plane hp hfull i, operator_intertwines,
    E.canonical_action, equivalence_canonical]

/-- Translation of the constructed cutoff sequence converges by continuity
in the full Schwartz topology. -/
theorem translated_approximation_tendsto (t : ℝ≥0) (i : FullPositiveTimeReflection.Label) :
    Tendsto (fun R => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      (shift t (inclusion (approximation R i)))) atTop
      (𝓝 (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (shift t i))) :=
  canonical_tendsto W plane hfull i.1 _ _
    (fun R => (shift t (inclusion (approximation R i))).2.2) (shift t i).2.2
    ((translationCLM (timeVector i.1 t)).continuous.continuousAt.tendsto.comp
      (SchwartzCutoffDensity.cutoff_tendsto (Configuration i.1) i.2.1))

/-- The existing evolution now acts on every unrestricted positive-time test
by its actual forward time translation. -/
theorem operator_canonical (t : ℝ≥0) (i : FullPositiveTimeReflection.Label) :
    operator W plane hp hfull E t
      (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (shift t i) := by
  have hleft := (operator W plane hp hfull E t).continuous.tendsto
    (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) |>.comp
      (canonical_approximation_tendsto W plane hfull i)
  apply tendsto_nhds_unique hleft
  convert translated_approximation_tendsto W plane hfull t i using 1
  ext R
  simp only [Function.comp_def, operator_canonical_inclusion, shift_inclusion]

theorem operator_zero
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull E 0 v = v := by
  rw [operator_apply, E.zero, LinearIsometryEquiv.apply_symm_apply]

theorem operator_add (s t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    operator W plane hp hfull E s (operator W plane hp hfull E t v) =
      operator W plane hp hfull E (s+t) v := by
  simp only [operator_apply, LinearIsometryEquiv.symm_apply_apply, E.add]

theorem operator_contraction (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    ‖operator W plane hp hfull E t v‖ ≤ ‖v‖ := by
  rw [operator_apply, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    E.contraction t ((equivalence W plane hp hfull).symm v)

theorem operator_symmetric (t : ℝ≥0)
    (v w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    inner ℂ (operator W plane hp hfull E t v) w =
      inner ℂ v (operator W plane hp hfull E t w) := by
  let e := equivalence W plane hp hfull
  change inner ℂ (e (E.operator t (e.symm v))) w = inner ℂ v (e (E.operator t (e.symm w)))
  rw [e.inner_map_eq_flip, E.symmetric]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (e.inner_map_map (e.symm v) (E.operator t (e.symm w))).symm

theorem operator_positive (t : ℝ≥0)
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    0 ≤ (inner ℂ v (operator W plane hp hfull E t v)).re := by
  let e := equivalence W plane hp hfull
  have he := e.inner_map_map (e.symm v) (E.operator t (e.symm v))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  change 0 ≤ (inner ℂ v (e (E.operator t (e.symm v)))).re
  rw [he]
  exact E.positive t (e.symm v)

theorem operator_strongly_continuous
    (v : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)) :
    Continuous (fun t => operator W plane hp hfull E t v) :=
  (equivalence W plane hp hfull).continuous.comp
    (E.strongly_continuous ((equivalence W plane hp hfull).symm v))

end
end UnifiedTheory.Clay.YangMills.FullSchwartzDynamics
