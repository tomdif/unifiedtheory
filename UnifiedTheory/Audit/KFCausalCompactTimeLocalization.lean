/- Compact time cutoffs turn uniform interval approximation into global
bounded-continuous approximation. Support of the cutoff derivative is derived. -/
import UnifiedTheory.Audit.KFCausalBernsteinC1Approximation
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.ContinuousMap.CompactlySupported

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactTimeLocalization
noncomputable section
open Set Filter Function BoundedContinuousFunction
open scoped Topology unitInterval CompactlySupported
open UnifiedTheory.Audit.KFCausalBernsteinC1Approximation (unitCurve)

structure Cutoff where
  value : ℝ →ᵇ ℝ
  derivative : ℝ →ᵇ ℝ
  hasDeriv : ∀ t, HasDerivAt value (derivative t) t
  support : tsupport value ⊆ Icc 0 1

theorem Cutoff.derivative_support (χ : Cutoff) : tsupport χ.derivative ⊆ Icc 0 1 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  apply χ.support
  apply support_deriv_subset
  change deriv χ.value t ≠ 0
  rw [(χ.hasDeriv t).deriv]
  exact ht

theorem compact_of_window_support (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1) :
    HasCompactSupport χ :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hχ

theorem zero_off_window (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1)
    (t : ℝ) (ht : t ∉ Icc 0 1) : χ t = 0 := by
  by_contra hz
  exact ht (hχ (subset_tsupport χ hz))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weighted (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1)
    (F : ℝ → E) (hF : Continuous F) : ℝ →ᵇ E :=
  (⟨⟨fun t => χ t • F t,χ.continuous.smul hF⟩,
    (compact_of_window_support χ hχ).smul_right⟩ : C_c(ℝ,E)).toBoundedContinuousFunction

theorem weighted_apply (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1)
    (F : ℝ → E) (hF : Continuous F) (t : ℝ) :
    weighted χ hχ F hF t = χ t • F t := rfl

theorem weighted_error_bound (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1)
    (F G : ℝ → E) (hF : Continuous F) (hG : Continuous G) :
    ‖weighted χ hχ F hF-weighted χ hχ G hG‖ ≤
      ‖χ‖*‖unitCurve F hF-unitCurve G hG‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro t
  change ‖χ t • F t-χ t • G t‖ ≤ _
  rw [← smul_sub,norm_smul]
  by_cases ht : t ∈ Icc 0 1
  · exact mul_le_mul (χ.norm_coe_le_norm t)
      ((unitCurve F hF-unitCurve G hG).norm_coe_le_norm ⟨t,ht⟩)
      (norm_nonneg _) (norm_nonneg _)
  · rw [zero_off_window χ hχ t ht,norm_zero,zero_mul]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem weighted_tendsto (χ : ℝ →ᵇ ℝ) (hχ : tsupport χ ⊆ Icc 0 1)
    (F : ℕ → ℝ → E) (G : ℝ → E) (hF : ∀ n, Continuous (F n)) (hG : Continuous G)
    (h : Tendsto (fun n => unitCurve (F n) (hF n)) atTop (𝓝 (unitCurve G hG))) :
    Tendsto (fun n => weighted χ hχ (F n) (hF n)) atTop (𝓝 (weighted χ hχ G hG)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => weighted_error_bound χ hχ (F n) G (hF n) hG)
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp h))

def localizedDerivative (χ : Cutoff) (F F' : ℝ → E)
    (hF : Continuous F) (hF' : Continuous F') : ℝ →ᵇ E :=
  weighted χ.derivative χ.derivative_support F hF + weighted χ.value χ.support F' hF'

theorem weighted_derivative (χ : Cutoff) (F F' : ℝ → E)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ t, HasDerivAt F (F' t) t) (t : ℝ) :
    HasDerivAt (weighted χ.value χ.support F hF)
      (localizedDerivative χ F F' hF hF' t) t := by
  change HasDerivAt (⇑χ.value • F) (χ.derivative t • F t+χ.value t • F' t) t
  simpa only [add_comm] using (χ.hasDeriv t).smul (hd t)

theorem localizedDerivative_tendsto (χ : Cutoff) (F D : ℕ → ℝ → E) (G G' : ℝ → E)
    (hF : ∀ n, Continuous (F n)) (hD : ∀ n, Continuous (D n))
    (hG : Continuous G) (hG' : Continuous G')
    (hv : Tendsto (fun n => unitCurve (F n) (hF n)) atTop (𝓝 (unitCurve G hG)))
    (hd : Tendsto (fun n => unitCurve (D n) (hD n)) atTop (𝓝 (unitCurve G' hG'))) :
    Tendsto (fun n => localizedDerivative χ (F n) (D n) (hF n) (hD n)) atTop
      (𝓝 (localizedDerivative χ G G' hG hG')) :=
  (weighted_tendsto χ.derivative χ.derivative_support F G hF hG hv).add
    (weighted_tendsto χ.value χ.support D G' hD hG' hd)

#print axioms Cutoff.derivative_support
#print axioms compact_of_window_support
#print axioms zero_off_window
#print axioms weighted_apply
#print axioms weighted_error_bound
#print axioms weighted_tendsto
#print axioms weighted_derivative
#print axioms localizedDerivative_tendsto
end
end UnifiedTheory.Audit.KFCausalCompactTimeLocalization
