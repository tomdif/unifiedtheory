/- A fixed probability window preserves escape to positive infinity.
Explicit bounds keep the window tails separate from the evolving law. -/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalProbabilityWindowEscape
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

def difference (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun z : ℝ × ℝ => z.1-z.2)

theorem upper_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S R : ℝ) :
    difference μ ν (Iic S) ≤ μ (Iic (S+R))+ν (Icc (-R) R)ᶜ := by
  rw [difference,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hs : {z : ℝ × ℝ | z.1-z.2 ≤ S} ⊆
      ((Iic (S+R)) ×ˢ univ) ∪ (univ ×ˢ (Icc (-R) R)ᶜ) := by
    intro z hz
    by_cases hy : z.2 ∈ Icc (-R) R
    · apply Or.inl
      refine ⟨?_,mem_univ _⟩
      change z.1 ≤ S+R
      have hxy : z.1-z.2 ≤ S := hz
      have hy' : z.2 ≤ R := hy.2
      linarith only [hxy,hy']
    · exact Or.inr ⟨mem_univ _,hy⟩
  exact (measure_mono hs).trans ((measure_union_le _ _).trans_eq (by simp))

theorem reverse_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S R : ℝ) :
    μ (Iic S) ≤ difference μ ν (Iic (S+R))+ν (Icc (-R) R)ᶜ := by
  rw [difference,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hs : (Iic S) ×ˢ (univ : Set ℝ) ⊆
      {z : ℝ × ℝ | z.1-z.2 ≤ S+R} ∪ (univ ×ˢ (Icc (-R) R)ᶜ) := by
    intro z hz
    by_cases hy : z.2 ∈ Icc (-R) R
    · apply Or.inl
      change z.1-z.2 ≤ S+R
      have hx : z.1 ≤ S := hz.1
      have hy' : -R ≤ z.2 := hy.1
      linarith only [hx,hy']
    · exact Or.inr ⟨mem_univ _,hy⟩
  have ht := (measure_mono (μ := μ.prod ν) hs).trans (measure_union_le _ _)
  simpa only [Measure.prod_prod,measure_univ,mul_one,one_mul] using ht

theorem window_tail (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ν (Icc (-(n:ℝ)) n)ᶜ) atTop (𝓝 0) := by
  have ha : Antitone (fun n : ℕ => (Icc (-(n:ℝ)) n)ᶜ) := by
    intro n m hnm
    apply compl_subset_compl.mpr
    exact Icc_subset_Icc (neg_le_neg (by exact_mod_cast hnm)) (by exact_mod_cast hnm)
  have he : (⋂ n : ℕ, (Icc (-(n:ℝ)) n)ᶜ) = (∅ : Set ℝ) := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n,hn⟩ := exists_nat_gt |x|
    have hnx := mem_iInter.mp hx n
    exact hnx ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n : ℕ => (measurableSet_Icc.compl).nullMeasurableSet) ha
    ⟨0,measure_ne_top ν _⟩
  simpa only [Function.comp_def,he,measure_empty] using ht

private theorem transfer {ι : Type*} (l : Filter ι) (a b : ι → ℝ → ℝ≥0∞)
    (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ (S : ℝ) (R : ℕ) t, a t S ≤ b t (S+(R:ℝ))+e R)
    (ht : ∀ S, Tendsto (fun t => b t S) l (𝓝 0)) (S : ℝ) :
    Tendsto (fun t => a t S) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  have hp : 0 < η/2 := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨R,hR⟩ := (ENNReal.tendsto_nhds_zero.mp he (η/2) hp).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (ht (S+(R:ℝ))) (η/2) hp] with t htime
  exact (hb S R t).trans ((add_le_add htime hR).trans_eq (ENNReal.add_halves η))

theorem escape_iff {ι : Type*} (l : Filter ι) (μ : ι → Measure ℝ)
    (ν : Measure ℝ) [∀ t, IsProbabilityMeasure (μ t)] [IsProbabilityMeasure ν] :
    (∀ S, Tendsto (fun t => difference (μ t) ν (Iic S)) l (𝓝 0)) ↔
      (∀ S, Tendsto (fun t => μ t (Iic S)) l (𝓝 0)) := by
  constructor
  · intro ht S
    exact transfer l (fun t S => μ t (Iic S)) (fun t S => difference (μ t) ν (Iic S))
      (fun R => ν (Icc (-(R:ℝ)) R)ᶜ) (window_tail ν)
      (fun S R t => reverse_bound (μ t) ν S R) ht S
  · intro ht S
    exact transfer l (fun t S => difference (μ t) ν (Iic S)) (fun t S => μ t (Iic S))
      (fun R => ν (Icc (-(R:ℝ)) R)ᶜ) (window_tail ν)
      (fun S R t => upper_bound (μ t) ν S R) ht S

#print axioms upper_bound
#print axioms reverse_bound
#print axioms window_tail
#print axioms escape_iff

end
end UnifiedTheory.Audit.KFCausalProbabilityWindowEscape
