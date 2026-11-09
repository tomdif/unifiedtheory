/- Strong convergence of the complete positive-real-cutoff family.
Integer cutoffs converge by compactness and uniqueness; the proved nearby
cutoff estimate bridges every real cutoff to its next integer. The clock
floor remains fixed. No rate of convergence to the unbounded evolution is
assumed or asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
import UnifiedTheory.Audit.KFCausalClockFloorAveragedCutoffComparison
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedRealConvergence
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCutoffComparison
open UnifiedTheory.Audit.KFCausalDenseIsometryLimit

def roundCutoff (a : ℝ) : ℝ := cutoff ⌊a⌋₊

theorem roundCutoff_pos (a : ℝ) : 0 < roundCutoff a := cutoff_pos _

theorem roundCutoff_tendsto : Tendsto roundCutoff atTop atTop :=
  cutoff_tendsto.comp tendsto_nat_floor_atTop

theorem roundCutoff_nearby (a : ℝ) (ha : 0 < a) : |a-roundCutoff a| ≤ 1 := by
  have hl := Nat.floor_le ha.le
  have hu := Nat.lt_floor_add_one a
  unfold roundCutoff cutoff
  exact abs_le.mpr ⟨by linarith,by linarith⟩

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "F" => dynamics ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "W" => windowEnergy ε hε hbar hh hbound mass2 quartic vacuum

/-- Identity outside the positive-cutoff region only makes a total real-indexed
function for the limit at infinity. Every positive cutoff is the actual dynamics. -/
def approximation (a s t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  if ha : 0 < a then F a ha s t else 1

theorem approximation_of_pos (a : ℝ) (ha : 0 < a) (s t : ℝ) :
    approximation ε hε hbar hh hbound mass2 quartic vacuum a s t = F a ha s t := by
  simp only [approximation,dif_pos ha]

theorem approximation_isometry (a s t : ℝ) :
    Isometry (approximation ε hε hbar hh hbound mass2 quartic vacuum a s t) := by
  by_cases ha : 0 < a
  · rw [approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum a ha]
    exact AddMonoidHomClass.isometry_of_norm (F a ha s t).toLinearMap
      (dynamics_norm ε hε hbar hh hbound mass2 quartic vacuum a ha s t)
  · simp only [approximation,dif_neg ha]
    exact isometry_id

theorem nearby_error_tendsto_zero (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun a : ℝ => (|1/hbar| *(2*Real.sqrt (W s (max |s| |t|) w/roundCutoff a)))*|t-s|)
      atTop (𝓝 0) := by
  have hd : Tendsto (fun a => W s (max |s| |t|) w/roundCutoff a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp roundCutoff_tendsto).const_mul (W s (max |s| |t|) w)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hd
  simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
    ((hs.const_mul 2).const_mul |1/hbar|).mul_const |t-s|

theorem dynamics_strong_limit_form (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun a => approximation ε hε hbar hh hbound mass2 quartic vacuum a s t (J w))
      atTop (𝓝 (U s t (J w))) := by
  have hb : Tendsto (fun a => F (roundCutoff a) (roundCutoff_pos a) s t (J w))
      atTop (𝓝 (U s t (J w))) :=
    (cutoff_dynamics_strong_limit_form ε hε hbar hh hbound mass2 quartic vacuum s t w).comp
      tendsto_nat_floor_atTop
  have he : ∀ᶠ a : ℝ in atTop,
      ‖approximation ε hε hbar hh hbound mass2 quartic vacuum a s t (J w)-
        F (roundCutoff a) (roundCutoff_pos a) s t (J w)‖ ≤
      (|1/hbar| *(2*Real.sqrt (W s (max |s| |t|) w/roundCutoff a)))*|t-s| := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
    have hc := dynamics_nearby_cutoff_bound ε hε hbar hh hbound mass2 quartic vacuum
      a (roundCutoff a) ha (roundCutoff_pos a) s t (roundCutoff_nearby a ha) w
    simpa only [approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum a ha] using hc
  have hn := squeeze_zero' (Eventually.of_forall (fun a : ℝ => norm_nonneg
    (approximation ε hε hbar hh hbound mass2 quartic vacuum a s t (J w)-
      F (roundCutoff a) (roundCutoff_pos a) s t (J w)))) he
    (nearby_error_tendsto_zero ε hε hbar hh hbound mass2 quartic vacuum s t w)
  have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa only [sub_add_cancel,zero_add] using hz.add hb

theorem dynamics_strong_limit (s t : ℝ) (f : Hilbert) :
    Tendsto (fun a => approximation ε hε hbar hh hbound mass2 quartic vacuum a s t f)
      atTop (𝓝 (U s t f)) := by
  apply tendsto_of_dense_isometries (J) (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (fun a => approximation ε hε hbar hh hbound mass2 quartic vacuum a s t) (U s t)
    (fun a => approximation_isometry ε hε hbar hh hbound mass2 quartic vacuum a s t)
    (U s t).isometry atTop _ f
  exact dynamics_strong_limit_form ε hε hbar hh hbound mass2 quartic vacuum s t

/-- Every sufficiently large positive real cutoff is close, not just a subsequence. -/
theorem dynamics_eventually_close (s t : ℝ) (f : Hilbert) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a → ∀ ha : 0 < a,
      ‖F a ha s t f-U s t f‖ < δ := by
  have he := Metric.tendsto_nhds.mp
    (dynamics_strong_limit ε hε hbar hh hbound mass2 quartic vacuum s t f) δ hδ
  obtain ⟨A,hA⟩ := eventually_atTop.mp he
  refine ⟨max A 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a hAa ha
  have hl := hA a ((le_max_left A 1).trans hAa)
  simpa only [dist_eq_norm,approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum a ha] using hl

/-- Any positive cutoff path tending to infinity has the same strong limit. -/
theorem dynamics_along_positive_parameters {ι : Type*} (l : Filter ι) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hl : Tendsto a l atTop) (s t : ℝ) (f : Hilbert) :
    Tendsto (fun i => F (a i) (ha i) s t f) l (𝓝 (U s t f)) := by
  have hc := (dynamics_strong_limit ε hε hbar hh hbound mass2 quartic vacuum s t f).comp hl
  exact hc.congr' (Eventually.of_forall fun i => congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f)
    (approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum (a i) (ha i) s t))

#print axioms roundCutoff_tendsto
#print axioms roundCutoff_nearby
#print axioms approximation_of_pos
#print axioms approximation_isometry
#print axioms nearby_error_tendsto_zero
#print axioms dynamics_strong_limit_form
#print axioms dynamics_strong_limit
#print axioms dynamics_eventually_close
#print axioms dynamics_along_positive_parameters

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedRealConvergence
