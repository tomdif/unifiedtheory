/- The quartic polynomial arising in the Gamma(1/2) angular endpoint has a
strict global coercive bound. Five sufficiently small coefficient errors
preserve a uniform bound on the entire real line. This is a polynomial
supplier; no angular moment convergence or response estimate is assumed
or concluded here. -/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalAngularQuarticEndpoint
noncomputable section
open Filter
open scoped Topology

def endpoint (s : ℝ) : ℝ := s^4-4*s^3+(15/2)*s^2-12*s+165/16

def endpointCoefficients : Fin 5 → ℝ := ![165/16,-12,15/2,-4,1]

def evaluate (c : Fin 5 → ℝ) (s : ℝ) : ℝ := ∑ i, c i*s^i.val

theorem endpoint_sos (s : ℝ) :
    endpoint s = ((s-1)^2-3/4)^2+3*(s-1-5/6)^2+1/6 := by
  unfold endpoint
  ring

theorem endpoint_coercive (s : ℝ) : (1+s^4)/108 ≤ endpoint s := by
  have he : 108*endpoint s-(1+s^4) =
      92*((s-1)^2-3/4)^2+324*(s-1-5/6)^2+
      (s-2)^2*(7*(s-1+5/7)^2+24/7)+8*((s-1)^2-3/2)^2 := by
    unfold endpoint
    ring
  have hn : 0 ≤ 108*endpoint s-(1+s^4) := by rw [he]; positivity
  linarith

theorem endpoint_positive (s : ℝ) : 0 < endpoint s := by
  have hp : 0 < (1+s^4)/108 := by positivity
  exact hp.trans_le (endpoint_coercive s)

theorem endpoint_eq_evaluate (s : ℝ) : endpoint s=evaluate endpointCoefficients s := by
  norm_num [evaluate,endpointCoefficients,Fin.sum_univ_succ,endpoint]
  ring

theorem power_bound (s : ℝ) (i : Fin 5) : |s^i.val| ≤ 1+s^4 := by
  rw [abs_pow]
  have h4 : |s|^4=s^4 := by rw [← abs_pow,abs_of_nonneg (by positivity)]
  by_cases hs : |s| ≤ 1
  · have hp : |s|^i.val ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
    have hn : 0 ≤ s^4 := by positivity
    linarith
  · have hp : |s|^i.val ≤ |s|^4 :=
      pow_le_pow_right₀ (le_of_not_ge hs) (by omega)
    rw [h4] at hp
    linarith

theorem coefficient_error_bound (c : Fin 5 → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hc : ∀ i, |c i-endpointCoefficients i| ≤ e) (s : ℝ) :
    |evaluate c s-endpoint s| ≤ 5*e*(1+s^4) := by
  have hs : evaluate c s-endpoint s =
      ∑ i, (c i-endpointCoefficients i)*s^i.val := by
    rw [endpoint_eq_evaluate]
    unfold evaluate
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  calc
    |∑ i, (c i-endpointCoefficients i)*s^i.val| ≤
        ∑ i, |(c i-endpointCoefficients i)*s^i.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, e*(1+s^4) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hc i) (power_bound s i) (abs_nonneg _) he
    _ = 5*e*(1+s^4) := by simp; ring

theorem stable_lower (c : Fin 5 → ℝ)
    (hc : ∀ i, |c i-endpointCoefficients i| ≤ 1/1080) (s : ℝ) :
    (1+s^4)/216 ≤ evaluate c s := by
  have he := coefficient_error_bound c (1/1080) (by norm_num) hc s
  have hl := (abs_le.mp he).1
  have hp := endpoint_coercive s
  linarith

theorem stable_positive (c : Fin 5 → ℝ)
    (hc : ∀ i, |c i-endpointCoefficients i| ≤ 1/1080) (s : ℝ) :
    0 < evaluate c s := by
  exact (show 0 < (1+s^4)/216 by positivity).trans_le (stable_lower c hc s)

theorem eventually_uniform_coercive {ι : Type*} (l : Filter ι)
    (c : ι → Fin 5 → ℝ)
    (hc : ∀ i, Tendsto (fun z => c z i) l (𝓝 (endpointCoefficients i))) :
    ∀ᶠ z in l, ∀ s : ℝ, (1+s^4)/216 ≤ evaluate (c z) s := by
  have hi (i : Fin 5) : ∀ᶠ z in l, |c z i-endpointCoefficients i| ≤ 1/1080 := by
    filter_upwards [(Metric.tendsto_nhds.mp (hc i)) (1/1080) (by norm_num)] with z hz
    simpa only [Real.dist_eq] using hz.le
  filter_upwards [Filter.eventually_all.mpr hi] with z hz
  exact stable_lower (c z) hz

#print axioms endpoint_sos
#print axioms endpoint_coercive
#print axioms endpoint_positive
#print axioms endpoint_eq_evaluate
#print axioms power_bound
#print axioms coefficient_error_bound
#print axioms stable_lower
#print axioms stable_positive
#print axioms eventually_uniform_coercive
end
end UnifiedTheory.Audit.KFCausalAngularQuarticEndpoint
