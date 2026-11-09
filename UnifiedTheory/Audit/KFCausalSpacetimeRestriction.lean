/- Actual spacetime force measures agree exactly under restriction to
any smaller time window, before taking a semiclassical limit. -/
import UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
import UnifiedTheory.Audit.KFCausalCompactTimeRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeRestriction
noncomputable section
open MeasureTheory ProbabilityTheory Set
open UnifiedTheory.Audit.KFCausalFiniteKernelSpacetime
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair
open UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (Square)
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests (finitePair)
open UnifiedTheory.Audit.KFCausalCompactTimeRestriction

def restrictPair (F : Pair) (u v : ℝ) : Pair where
  positive := F.positive.restrict (Icc u v ×ˢ univ)
  negative := F.negative.restrict (Icc u v ×ˢ univ)
  positive_finite := inferInstance
  negative_finite := inferInstance

theorem spacetime_restrict (κ : Kernel ℝ ℝ) [∀ t, IsFiniteMeasure (κ t)]
    (hm : Continuous (fun t => (κ t).real univ)) (b c u v : ℝ)
    (hu : b ≤ u) (hv : v ≤ c) :
    (spacetime κ b c).restrict (Icc u v ×ˢ univ) = spacetime κ u v := by
  letI := spacetime_finite κ hm b c
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.restrict_apply (hA.prod hB)]
  have he : (A ×ˢ B) ∩ (Icc u v ×ˢ (univ : Set ℝ)) = (A ∩ Icc u v) ×ˢ B := by
    ext z
    simp only [mem_inter_iff,mem_prod,mem_univ,and_true]
    tauto
  rw [he,spacetime_rectangle κ hm b c _ B (hA.inter measurableSet_Icc) hB,
    spacetime_rectangle κ hm u v A B hA hB,
    Measure.restrict_restrict (hA.inter measurableSet_Icc),Measure.restrict_restrict hA]
  have hs : (A ∩ Icc u v) ∩ Icc b c = A ∩ Icc u v :=
    inter_eq_left.mpr (inter_subset_right.trans (Icc_subset_Icc hu hv))
  rw [hs]

theorem fromCurve_restrict {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : ℝ) (w : Fin 8 → ℂ)
    (y : ℝ → Lp KFCausalNeutralTranslationOutput.Outputs 2 μ) (hy : Continuous y)
    (b c u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    restrictPair (fromCurve μ h w y hy b c) u v = fromCurve μ h w y hy u v := by
  have hp := spacetime_restrict _ (positive_mass_continuous μ h w y hy) b c u v hu hv
  have hn := spacetime_restrict _ (negative_mass_continuous μ h w y hy) b c u v hu hv
  unfold restrictPair fromCurve
  simp only [hp,hn]

theorem forceWindow_restrict (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
    (r : ℝ) (hr : 0 < r) (b c u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    restrictPair (forceWindow ε a h hε ha hne hh m g k s p r hr b c) u v =
      forceWindow ε a h hε ha hne hh m g k s p r hr u v :=
  fromCurve_restrict _ _ _ _ _ b c u v hu hv

theorem finitePair_restrict (P N : FiniteMeasure Square) (u v : ℝ) :
    finitePair (P.restrict (timeStrip u v)) (N.restrict (timeStrip u v)) =
      restrictPair (finitePair P N) u v := by
  unfold finitePair restrictPair
  simp only [finitePart_time_restrict,FiniteMeasure.restrict_measure_eq]

#print axioms spacetime_restrict
#print axioms fromCurve_restrict
#print axioms forceWindow_restrict
#print axioms finitePair_restrict
end
end UnifiedTheory.Audit.KFCausalSpacetimeRestriction
