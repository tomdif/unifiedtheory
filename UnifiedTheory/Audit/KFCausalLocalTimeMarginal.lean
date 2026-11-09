/- Returning to finite time and momentum preserves the physical time
domination. The limiting force has no time atoms and stays in its window. -/
import UnifiedTheory.Audit.KFCausalCompactTimeMarginal
import UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalLocalTimeMarginal
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (Square)
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
open UnifiedTheory.Audit.KFCausalCompactTimeMarginal

theorem local_rectangle_bound (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum))
    (A : Set ℝ) (hA : MeasurableSet A) :
    (finitePair P N).positive (A ×ˢ univ)+(finitePair P N).negative (A ×ˢ univ) ≤
      ENNReal.ofReal C*volume (A ∩ Icc b c) := by
  let B : Set Spectrum := KFCausalLocalForceMeasure.interior ∩
    (fun x : Spectrum => Real.tan (x:ℝ)) ⁻¹' A
  have hB : MeasurableSet B := KFCausalLocalForceMeasure.interior_measurable.inter
    (hA.preimage KFCausalLocalForceMeasure.tangent_measurable)
  have hpre : KFCausalCompactifiedForceMeasure.embed ⁻¹' B = A := by
    ext t
    change (KFCausalCompactifiedForceMeasure.embed t ∈ KFCausalLocalForceMeasure.interior ∧
      Real.tan (Real.arctan t) ∈ A) ↔ t ∈ A
    simp only [Real.tan_arctan,KFCausalVanishingForceTests.embed_interior,true_and]
  have hs : inverse ⁻¹' (A ×ˢ (univ : Set ℝ)) ∩ interior ⊆ Prod.fst ⁻¹' B := by
    intro z hz
    exact ⟨hz.2.1,hz.1.1⟩
  change (((P:Measure Square).restrict interior).map inverse) (A ×ˢ univ)+
    (((N:Measure Square).restrict interior).map inverse) (A ×ˢ univ) ≤ _
  rw [Measure.map_apply inverse_measurable (hA.prod .univ),
    Measure.map_apply inverse_measurable (hA.prod .univ),
    Measure.restrict_apply ((hA.prod .univ).preimage inverse_measurable),
    Measure.restrict_apply ((hA.prod .univ).preimage inverse_measurable),
    ← Measure.add_apply]
  calc
    _ ≤ ((P:Measure Square)+(N:Measure Square)) (Prod.fst ⁻¹' B) := measure_mono hs
    _ = (timeMarginal (P+N) : Measure Spectrum) B :=
      (Measure.map_apply measurable_fst hB).symm
    _ ≤ (timeBound b c C : Measure Spectrum) B := hb B
    _ = _ := by rw [timeBound_apply b c C B hB,hpre]

def localTimeMarginal (P N : FiniteMeasure Square) : Measure ℝ :=
  ((finitePair P N).positive+(finitePair P N).negative).map Prod.fst

theorem local_time_domination (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum)) :
    localTimeMarginal P N ≤ ENNReal.ofReal C • volume.restrict (Icc b c) := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [localTimeMarginal,Measure.map_apply measurable_fst hA,
    Measure.smul_apply,Measure.restrict_apply hA]
  have he : Prod.fst ⁻¹' A = A ×ˢ (univ : Set ℝ) := by ext z; simp
  rw [he,Measure.add_apply]
  exact local_rectangle_bound P N b c C hb A hA

theorem local_time_absolutelyContinuous (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum)) :
    localTimeMarginal P N ≪ volume.restrict (Icc b c) :=
  Measure.absolutelyContinuous_of_le_smul (local_time_domination P N b c C hb)

theorem local_time_slice_zero (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum))
    (t : ℝ) :
    (finitePair P N).positive ({t} ×ˢ univ)+(finitePair P N).negative ({t} ×ˢ univ) = 0 := by
  have hs := local_rectangle_bound P N b c C hb {t} (measurableSet_singleton t)
  have hv : volume ({t} ∩ Icc b c) = 0 := measure_mono_null inter_subset_left (measure_singleton t)
  rw [hv,mul_zero] at hs
  exact le_antisymm hs (zero_le _)

theorem local_outside_window_zero (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum)) :
    (finitePair P N).positive ((Icc b c)ᶜ ×ˢ univ)+
      (finitePair P N).negative ((Icc b c)ᶜ ×ˢ univ) = 0 := by
  have hs := local_rectangle_bound P N b c C hb (Icc b c)ᶜ measurableSet_Icc.compl
  simpa using hs

#print axioms local_rectangle_bound
#print axioms local_time_domination
#print axioms local_time_absolutelyContinuous
#print axioms local_time_slice_zero
#print axioms local_outside_window_zero
end
end UnifiedTheory.Audit.KFCausalLocalTimeMarginal
