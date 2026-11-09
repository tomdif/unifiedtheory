/- Time strips are continuity sets for dominated spacetime limits.
Restriction commutes with compactification and recovery of finite points. -/
import UnifiedTheory.Audit.KFCausalCompactWeakRestriction
import UnifiedTheory.Audit.KFCausalLocalTimeMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactTimeRestriction
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalCompactTimeMarginal

def timeStrip (u v : ℝ) : Set Square :=
  (fun z : Square => (z.1:ℝ)) ⁻¹' Icc (Real.arctan u) (Real.arctan v)

theorem timeStrip_closed (u v : ℝ) : IsClosed (timeStrip u v) :=
  isClosed_Icc.preimage (continuous_subtype_val.comp continuous_fst)

theorem embed_preimage_timeStrip (u v : ℝ) :
    embed ⁻¹' timeStrip u v = Icc u v ×ˢ (univ : Set ℝ) := by
  ext z
  simp [timeStrip,embed,KFCausalCompactifiedForceMeasure.embed,Real.arctan_le_arctan_iff]

theorem timeStrip_frontier (u v : ℝ) (huv : u ≤ v) :
    frontier (timeStrip u v) ⊆
      ({KFCausalCompactifiedForceMeasure.embed u} ×ˢ (univ : Set Spectrum)) ∪
      ({KFCausalCompactifiedForceMeasure.embed v} ×ˢ (univ : Set Spectrum)) := by
  intro z hz
  have he := (continuous_subtype_val.comp continuous_fst).frontier_preimage_subset
    (Icc (Real.arctan u) (Real.arctan v)) hz
  rw [frontier_Icc (Real.arctan_mono huv)] at he
  rcases he with he | he
  · exact Or.inl ⟨Subtype.ext he,mem_univ _⟩
  · exact Or.inr ⟨Subtype.ext he,mem_univ _⟩

theorem dominated_frontier_zero (P N : FiniteMeasure Square) (b c C u v : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum))
    (huv : u ≤ v) :
    (P:Measure Square) (frontier (timeStrip u v)) = 0 ∧
      (N:Measure Square) (frontier (timeStrip u v)) = 0 := by
  have hu := dominated_time_slice_zero P N b c C hb (KFCausalCompactifiedForceMeasure.embed u)
  have hv := dominated_time_slice_zero P N b c C hb (KFCausalCompactifiedForceMeasure.embed v)
  rw [add_eq_zero] at hu hv
  exact ⟨measure_mono_null (timeStrip_frontier u v huv) (measure_union_null hu.1 hv.1),
    measure_mono_null (timeStrip_frontier u v huv) (measure_union_null hu.2 hv.2)⟩

theorem weak_time_restriction (μ η : ℕ → FiniteMeasure Square) (P N : FiniteMeasure Square)
    (hP : Tendsto μ atTop (𝓝 P)) (hN : Tendsto η atTop (𝓝 N)) (b c C u v : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum))
    (huv : u ≤ v) :
    Tendsto (fun n => (μ n).restrict (timeStrip u v)) atTop (𝓝 (P.restrict (timeStrip u v))) ∧
      Tendsto (fun n => (η n).restrict (timeStrip u v)) atTop (𝓝 (N.restrict (timeStrip u v))) := by
  have hz := dominated_frontier_zero P N b c C u v hb huv
  exact ⟨KFCausalCompactWeakRestriction.weak_restrict μ P hP _ (timeStrip_closed u v).measurableSet hz.1,
    KFCausalCompactWeakRestriction.weak_restrict η N hN _ (timeStrip_closed u v).measurableSet hz.2⟩

theorem compactify_time_restrict (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (u v : ℝ) :
    compactify (μ.restrict (Icc u v ×ˢ univ)) = (compactify μ).restrict (timeStrip u v) := by
  apply FiniteMeasure.toMeasure_injective
  change (μ.restrict (Icc u v ×ˢ univ)).map embed = (μ.map embed).restrict (timeStrip u v)
  rw [Measure.restrict_map embed_continuous.measurable (timeStrip_closed u v).measurableSet,
    embed_preimage_timeStrip]

theorem finitePart_time_restrict (P : FiniteMeasure Square) (u v : ℝ) :
    KFCausalLocalSpacetimeTests.finitePart (P.restrict (timeStrip u v)) =
      (KFCausalLocalSpacetimeTests.finitePart P).restrict (Icc u v ×ˢ univ) := by
  apply FiniteMeasure.toMeasure_injective
  change (((P:Measure Square).restrict (timeStrip u v)).restrict
    KFCausalLocalSpacetimeTests.interior).map KFCausalLocalSpacetimeTests.inverse =
      (((P:Measure Square).restrict KFCausalLocalSpacetimeTests.interior).map
        KFCausalLocalSpacetimeTests.inverse).restrict (Icc u v ×ˢ univ)
  rw [Measure.restrict_map KFCausalLocalSpacetimeTests.inverse_measurable
    (measurableSet_Icc.prod MeasurableSet.univ),
    Measure.restrict_restrict KFCausalLocalSpacetimeTests.interior_open.measurableSet,
    Measure.restrict_restrict ((measurableSet_Icc.prod MeasurableSet.univ).preimage
      KFCausalLocalSpacetimeTests.inverse_measurable)]
  congr 2
  ext z
  by_cases hz : z ∈ KFCausalLocalSpacetimeTests.interior
  · have he : KFCausalLocalSpacetimeTests.inverse z ∈ Icc u v ×ˢ (univ : Set ℝ) ↔
        z ∈ timeStrip u v := by
      rw [← embed_preimage_timeStrip]
      simp only [mem_preimage,KFCausalLocalSpacetimeTests.embed_inverse z hz]
    simp only [mem_inter_iff,mem_preimage,hz,true_and,and_true,he]
  · simp only [mem_inter_iff,hz,false_and,and_false]

#print axioms timeStrip_closed
#print axioms embed_preimage_timeStrip
#print axioms timeStrip_frontier
#print axioms dominated_frontier_zero
#print axioms weak_time_restriction
#print axioms compactify_time_restrict
#print axioms finitePart_time_restrict
end
end UnifiedTheory.Audit.KFCausalCompactTimeRestriction
