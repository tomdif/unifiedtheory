/- A global spacetime force consists of two positive measures finite on
every bounded time window. Global total mass is not assumed finite. -/
import UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
import UnifiedTheory.Audit.KFCausalSpacetimeWindowTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
noncomputable section
open MeasureTheory Set BoundedContinuousFunction
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (pullback)
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction (restrictPair)
open UnifiedTheory.Audit.KFCausalSpacetimeWindowTests

theorem pair_ext (F G : Pair) (hp : F.positive = G.positive) (hn : F.negative = G.negative) :
    F = G := by
  cases F
  cases G
  cases hp
  cases hn
  rfl

structure Force where
  positive : Measure (ℝ × ℝ)
  negative : Measure (ℝ × ℝ)
  positive_finite_window : ∀ b c : ℝ, IsFiniteMeasure (positive.restrict (Icc b c ×ˢ univ))
  negative_finite_window : ∀ b c : ℝ, IsFiniteMeasure (negative.restrict (Icc b c ×ˢ univ))

attribute [instance] Force.positive_finite_window Force.negative_finite_window

def Force.window (J : Force) (b c : ℝ) : Pair where
  positive := J.positive.restrict (Icc b c ×ˢ univ)
  negative := J.negative.restrict (Icc b c ×ˢ univ)
  positive_finite := inferInstance
  negative_finite := inferInstance

theorem sigmaFinite_of_finite_windows (μ : Measure (ℝ × ℝ))
    (hμ : ∀ b c : ℝ, IsFiniteMeasure (μ.restrict (Icc b c ×ˢ univ))) : SigmaFinite μ := by
  refine ⟨⟨⟨KFCausalSpacetimeExhaustion.window 0,(fun _ => trivial),?_,
    KFCausalSpacetimeExhaustion.window_cover 0⟩⟩⟩
  intro n
  letI : IsFiniteMeasure (μ.restrict (KFCausalSpacetimeExhaustion.window 0 n)) :=
    hμ (KFCausalSpacetimeExhaustion.left 0 n) (KFCausalSpacetimeExhaustion.right 0 n)
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using
    measure_lt_top (μ.restrict (KFCausalSpacetimeExhaustion.window 0 n)) univ

theorem locallyFinite_of_finite_windows (μ : Measure (ℝ × ℝ))
    (hμ : ∀ b c : ℝ, IsFiniteMeasure (μ.restrict (Icc b c ×ˢ univ))) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun z => ?_⟩
  obtain ⟨n,hn⟩ := KFCausalSpacetimeExhaustion.window_neighborhood 0 z
  letI : IsFiniteMeasure (μ.restrict (KFCausalSpacetimeExhaustion.window 0 n)) :=
    hμ (KFCausalSpacetimeExhaustion.left 0 n) (KFCausalSpacetimeExhaustion.right 0 n)
  refine ⟨KFCausalSpacetimeExhaustion.window 0 n,hn,?_⟩
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using
    measure_lt_top (μ.restrict (KFCausalSpacetimeExhaustion.window 0 n)) univ

instance Force.positive_sigmaFinite (J : Force) : SigmaFinite J.positive :=
  sigmaFinite_of_finite_windows J.positive J.positive_finite_window
instance Force.negative_sigmaFinite (J : Force) : SigmaFinite J.negative :=
  sigmaFinite_of_finite_windows J.negative J.negative_finite_window
instance Force.positive_locallyFinite (J : Force) : IsLocallyFiniteMeasure J.positive :=
  locallyFinite_of_finite_windows J.positive J.positive_finite_window
instance Force.negative_locallyFinite (J : Force) : IsLocallyFiniteMeasure J.negative :=
  locallyFinite_of_finite_windows J.negative J.negative_finite_window

theorem Force.window_restrict (J : Force) (b c u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    restrictPair (J.window b c) u v = J.window u v := by
  have hs : (Icc u v ×ˢ (univ : Set ℝ)) ∩ (Icc b c ×ˢ univ) = Icc u v ×ˢ univ :=
    inter_eq_left.mpr (prod_mono (Icc_subset_Icc hu hv) subset_rfl)
  unfold restrictPair Force.window
  simp only [Measure.restrict_restrict (measurableSet_Icc.prod MeasurableSet.univ),hs]

def Force.interval (J : Force) (b c : ℝ) : FluxPair where
  positive := (J.window b c).positive.map Prod.snd
  negative := (J.window b c).negative.map Prod.snd
  positive_finite := inferInstance
  negative_finite := inferInstance

def momentumTest (f : ℝ →ᵇ ℂ) : (ℝ × ℝ) →ᵇ ℂ := f.compContinuous ⟨Prod.snd,continuous_snd⟩

theorem Force.interval_evaluate (J : Force) (b c : ℝ) (f : ℝ →ᵇ ℂ) :
    (J.interval b c).evaluate f = (J.window b c).evaluate (momentumTest f) := by
  unfold FluxPair.evaluate Pair.evaluate Force.interval
  rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
  rfl

theorem Force.window_lift_test (J : Force) (b c : ℝ) (χ : Spectrum →ᵇ ℂ)
    (hχ : ∀ t ∈ Icc b c, χ (KFCausalCompactifiedForceMeasure.embed t) = 1)
    (f : C₀(ℝ,ℂ)) :
    (J.window b c).evaluate (pullback (liftTest χ f)) = (J.interval b c).evaluate f.toBCF := by
  rw [J.interval_evaluate b c f.toBCF]
  unfold Pair.evaluate
  congr 2
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    exact liftTest_on_window b c χ hχ f z.1 z.2 hz.1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    exact liftTest_on_window b c χ hχ f z.1 z.2 hz.1

#print axioms pair_ext
#print axioms sigmaFinite_of_finite_windows
#print axioms locallyFinite_of_finite_windows
#print axioms Force.positive_sigmaFinite
#print axioms Force.negative_sigmaFinite
#print axioms Force.positive_locallyFinite
#print axioms Force.negative_locallyFinite
#print axioms Force.window_restrict
#print axioms Force.interval_evaluate
#print axioms Force.window_lift_test
end
end UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
