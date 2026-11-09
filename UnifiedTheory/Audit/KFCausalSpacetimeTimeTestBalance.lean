/- The interval balance implies a time-dependent weak equation for separated
tests. Integrability is derived from the balance, not assumed for the curve. -/
import UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeTimeTestBalance
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
open UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

theorem window_positive_support (J : Force) (a b : ℝ) :
    ∀ᵐ z ∂(J.window a b).positive, z.1 ∈ Icc a b := by
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
  exact hz.1

theorem window_negative_support (J : Force) (a b : ℝ) :
    ∀ᵐ z ∂(J.window a b).negative, z.1 ∈ Icc a b := by
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
  exact hz.1

theorem cumulative_interval (J : Force) (a b t : ℝ) (ht : t ≤ b) (q : ℝ →ᵇ ℂ) :
    (cumulative (J.window a b).positive a t (momentumTest q) -
      cumulative (J.window a b).negative a t (momentumTest q))/2 =
        (J.interval a t).evaluate q := by
  rw [J.interval_evaluate,← J.window_restrict a b a t le_rfl ht]
  rfl

theorem weighted_balance_integrable (J : Force) (a b : ℝ) (E : ℝ → ℂ)
    (q : ℝ →ᵇ ℂ)
    (hE : ∀ t ∈ Icc a b, E t-E a = (J.interval a t).evaluate q)
    (η' : ℝ →ᵇ ℂ) :
    Integrable (fun t => η' t*E t) (volume.restrict (Icc a b)) := by
  have hP := weighted_cumulative_integrable (J.window a b).positive a b
    (window_positive_support J a b) η' (momentumTest q)
  have hN := weighted_cumulative_integrable (J.window a b).negative a b
    (window_negative_support J a b) η' (momentumTest q)
  apply (((η'.integrable (volume.restrict (Icc a b))).mul_const (E a)).add
    ((hP.sub hN).div_const 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he := hE t ht
  rw [← cumulative_interval J a b t ht.2 q] at he
  change η' t*E a + (η' t*cumulative (J.window a b).positive a t (momentumTest q)-
    η' t*cumulative (J.window a b).negative a t (momentumTest q))/2 = η' t*E t
  rw [← sub_add_cancel (E t) (E a),he]
  ring

theorem time_test_balance (J : Force) (a b : ℝ) (hab : a ≤ b) (E : ℝ → ℂ)
    (q : ℝ →ᵇ ℂ)
    (hE : ∀ t ∈ Icc a b, E t-E a = (J.interval a t).evaluate q)
    (η η' : ℝ →ᵇ ℂ) (hη : ∀ t : ℝ, HasDerivAt η (η' t) t) :
    (∫ t in Icc a b, η' t*E t) +
      (J.window a b).evaluate (timeWeight η (momentumTest q)) =
        η b*E b-η a*E a := by
  have hP := weighted_cumulative_integrable (J.window a b).positive a b
    (window_positive_support J a b) η' (momentumTest q)
  have hN := weighted_cumulative_integrable (J.window a b).negative a b
    (window_negative_support J a b) η' (momentumTest q)
  have hsplit : (∫ t in Icc a b, η' t*E t) =
      (∫ t in Icc a b, η' t)*E a +
        ((∫ t in Icc a b, η' t*cumulative (J.window a b).positive a t (momentumTest q))-
          (∫ t in Icc a b, η' t*cumulative (J.window a b).negative a t (momentumTest q)))/2 := by
    have hPN : Integrable (fun t =>
        (η' t*cumulative (J.window a b).positive a t (momentumTest q)-
          η' t*cumulative (J.window a b).negative a t (momentumTest q))/2)
        (volume.restrict (Icc a b)) := (hP.sub hN).div_const 2
    calc
      _ = ∫ t in Icc a b, η' t*E a +
          (η' t*cumulative (J.window a b).positive a t (momentumTest q)-
            η' t*cumulative (J.window a b).negative a t (momentumTest q))/2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have he := hE t ht
        rw [← cumulative_interval J a b t ht.2 q] at he
        rw [← sub_add_cancel (E t) (E a),he]
        ring
      _ = _ := by
        rw [integral_add ((η'.integrable (volume.restrict (Icc a b))).mul_const (E a)) hPN,
          integral_div,integral_sub hP hN,integral_mul_const]
  have hftc : (∫ t in Icc a b, η' t) = η b-η a := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hη t)
      (η'.continuous.intervalIntegrable a b)
  rw [hsplit,hftc,
    triangular_linear_identity (J.window a b).positive a b
      (window_positive_support J a b) η η' hη (momentumTest q),
    triangular_linear_identity (J.window a b).negative a b
      (window_negative_support J a b) η η' hη (momentumTest q)]
  have he := hE b ⟨hab,le_rfl⟩
  rw [J.interval_evaluate] at he
  unfold Pair.evaluate at he ⊢
  rw [← sub_add_cancel (E b) (E a),he]
  ring

theorem time_test_balance_zero_boundary (J : Force) (a b : ℝ) (hab : a ≤ b)
    (E : ℝ → ℂ) (q : ℝ →ᵇ ℂ)
    (hE : ∀ t ∈ Icc a b, E t-E a = (J.interval a t).evaluate q)
    (η η' : ℝ →ᵇ ℂ) (hη : ∀ t : ℝ, HasDerivAt η (η' t) t)
    (ha : η a = 0) (hb : η b = 0) :
    (∫ t in Icc a b, η' t*E t) +
      (J.window a b).evaluate (timeWeight η (momentumTest q)) = 0 := by
  simpa only [ha,hb,zero_mul,sub_zero] using time_test_balance J a b hab E q hE η η' hη

#print axioms window_positive_support
#print axioms window_negative_support
#print axioms cumulative_interval
#print axioms weighted_balance_integrable
#print axioms time_test_balance
#print axioms time_test_balance_zero_boundary
end
end UnifiedTheory.Audit.KFCausalSpacetimeTimeTestBalance
