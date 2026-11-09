/- Physical time-marginal domination passes to weak compactified
spacetime limits, excluding atoms on every compactified time slice. -/
import UnifiedTheory.Audit.KFCausalCompactWeakDomination
import UnifiedTheory.Audit.KFCausalCompactSpacetimeForce

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactTimeMarginal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

def timeMarginal (μ : FiniteMeasure Square) : FiniteMeasure Spectrum := μ.map Prod.fst

def timeBound (b c C : ℝ) : FiniteMeasure Spectrum :=
  Real.toNNReal C • KFCausalCompactifiedForceMeasure.compactify (volume.restrict (Icc b c))

theorem timeMarginal_add (μ ν : FiniteMeasure Square) :
    timeMarginal (μ+ν) = timeMarginal μ+timeMarginal ν :=
  FiniteMeasure.map_add measurable_fst μ ν

theorem compact_time_apply (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (A : Set Spectrum) (hA : MeasurableSet A) :
    (timeMarginal (compactify μ) : Measure Spectrum) A =
      μ ((KFCausalCompactifiedForceMeasure.embed ⁻¹' A) ×ˢ univ) := by
  change ((μ.map embed).map Prod.fst) A = _
  rw [Measure.map_map measurable_fst embed_continuous.measurable,
    Measure.map_apply (measurable_fst.comp embed_continuous.measurable) hA]
  congr 1
  ext z
  simp [embed]

theorem timeBound_apply (b c C : ℝ) (A : Set Spectrum) (hA : MeasurableSet A) :
    (timeBound b c C : Measure Spectrum) A = ENNReal.ofReal C *
      volume ((KFCausalCompactifiedForceMeasure.embed ⁻¹' A) ∩ Icc b c) := by
  change (Real.toNNReal C) •
    ((volume.restrict (Icc b c)).map KFCausalCompactifiedForceMeasure.embed) A = _
  rw [Measure.map_apply KFCausalCompactifiedForceMeasure.embed_continuous.measurable hA,
    Measure.restrict_apply (hA.preimage KFCausalCompactifiedForceMeasure.embed_continuous.measurable)]
  rfl

theorem compact_time_domination (F : Pair) (b c C : ℝ)
    (hb : ∀ A : Set ℝ, MeasurableSet A →
      F.positive (A ×ˢ univ)+F.negative (A ×ˢ univ) ≤ ENNReal.ofReal C*volume (A ∩ Icc b c)) :
    (timeMarginal (compactify F.positive+compactify F.negative) : Measure Spectrum) ≤
      (timeBound b c C : Measure Spectrum) := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [timeMarginal_add,FiniteMeasure.toMeasure_add,Measure.add_apply,
    compact_time_apply _ A hA,compact_time_apply _ A hA,timeBound_apply b c C A hA]
  exact hb _ (hA.preimage KFCausalCompactifiedForceMeasure.embed_continuous.measurable)

theorem weak_time_domination (F : ℕ → Pair) (P N : FiniteMeasure Square)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (b c C : ℝ)
    (hb : ∀ᶠ n in atTop, ∀ A : Set ℝ, MeasurableSet A →
      (F n).positive (A ×ˢ univ)+(F n).negative (A ×ˢ univ) ≤
        ENNReal.ofReal C*volume (A ∩ Icc b c)) :
    (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum) := by
  apply KFCausalCompactWeakDomination.weak_limit_le
    (fun n => timeMarginal (compactify (F n).positive+compactify (F n).negative))
    (timeMarginal (P+N)) (timeBound b c C)
  · exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hP.add hN) continuous_fst
  · exact hb.mono (fun n hn => compact_time_domination (F n) b c C hn)

theorem timeBound_no_atoms (b c C : ℝ) (x : Spectrum) :
    (timeBound b c C : Measure Spectrum) {x} = 0 := by
  rw [timeBound_apply b c C {x} (measurableSet_singleton x)]
  have hi : Function.Injective KFCausalCompactifiedForceMeasure.embed := by
    intro u v huv
    have he : Real.arctan u = Real.arctan v := congrArg (fun x : Spectrum => (x:ℝ)) huv
    simpa only [Real.tan_arctan] using congrArg Real.tan he
  have hs : (KFCausalCompactifiedForceMeasure.embed ⁻¹' {x}).Subsingleton := by
    intro u hu v hv
    exact hi (hu.trans hv.symm)
  have hz : volume ((KFCausalCompactifiedForceMeasure.embed ⁻¹' {x}) ∩ Icc b c) = 0 :=
    (show (((KFCausalCompactifiedForceMeasure.embed ⁻¹' {x}) ∩ Icc b c)).Subsingleton from
      fun _ hu _ hv => hs hu.1 hv.1).measure_zero volume
  rw [hz,mul_zero]

theorem dominated_time_slice_zero (P N : FiniteMeasure Square) (b c C : ℝ)
    (hb : (timeMarginal (P+N) : Measure Spectrum) ≤ (timeBound b c C : Measure Spectrum))
    (x : Spectrum) :
    (P : Measure Square) ({x} ×ˢ univ)+(N : Measure Square) ({x} ×ˢ univ) = 0 := by
  have hs := hb {x}
  rw [timeBound_no_atoms] at hs
  have he : (timeMarginal (P+N) : Measure Spectrum) {x} =
      (P : Measure Square) ({x} ×ˢ univ)+(N : Measure Square) ({x} ×ˢ univ) := by
    change ((P+N : FiniteMeasure Square) : Measure Square).map Prod.fst {x} = _
    rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
    have hset : Prod.fst ⁻¹' {x} = ({x} ×ˢ (univ : Set Spectrum)) := by ext z; simp
    rw [hset,FiniteMeasure.toMeasure_add,Measure.add_apply]
  exact le_antisymm (he ▸ hs) (zero_le _)

#print axioms timeMarginal_add
#print axioms compact_time_apply
#print axioms timeBound_apply
#print axioms compact_time_domination
#print axioms weak_time_domination
#print axioms timeBound_no_atoms
#print axioms dominated_time_slice_zero
end
end UnifiedTheory.Audit.KFCausalCompactTimeMarginal
