/- Characteristic convergence to a continuous normalized limit derives
uniform tightness of the whole sequence in finite-dimensional Euclidean
spaces. Eventual projection tails and the finitely many earlier measures
are both controlled. -/
import UnifiedTheory.Audit.KFCausalCharacteristicTailControl
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCharacteristicTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

 theorem projection_tail_tendsto (μ : ℕ → ProbabilityMeasure E) (a : E)
    (ha : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (μ n : Measure E).real {x | r < |inner ℝ a x|} ≤ η) :
    Tendsto (fun r : ℝ => ⨆ n : ℕ, (μ n : Measure E) {x | r < ‖inner ℝ a x‖}) atTop (𝓝 0) := by
  have hs (n : ℕ) : Tendsto (fun r : ℝ =>
      (μ n : Measure E) {x | r < ‖inner ℝ a x‖}) atTop (𝓝 0) := by
    simpa using (isTightMeasureSet_iff_inner_tendsto ℝ).mp
      (isTightMeasureSet_singleton (μ := (μ n : Measure E))) a
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · subst ε
    exact ⟨0,fun _ _ => le_top⟩
  have hp : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨r,_,hN⟩ := ha ε.toReal hp
  obtain ⟨N,hN⟩ := eventually_atTop.mp hN
  have hfinite : ∀ᶠ R : ℝ in atTop, ∀ n ∈ Finset.range N,
      (μ n : Measure E) {x | R < ‖inner ℝ a x‖} ≤ ε := by
    apply (eventually_all_finset (Finset.range N)).mpr
    intro n _
    exact ((hs n).eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  obtain ⟨R,hR⟩ := hfinite.exists
  refine ⟨max r R,fun u hu => iSup_le (fun n => ?_)⟩
  by_cases hn : n < N
  · exact (measure_mono (fun x hx => lt_of_le_of_lt
      ((le_max_right r R).trans hu) hx)).trans (hR n (Finset.mem_range.mpr hn))
  · have hbound : (μ n : Measure E) {x | r < ‖inner ℝ a x‖} ≤ ε := by
      have he := ENNReal.ofReal_le_ofReal (hN n (Nat.le_of_not_gt hn))
      simpa only [Measure.real,Real.norm_eq_abs,ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal htop] using he
    exact (measure_mono (fun x hx => lt_of_le_of_lt
      ((le_max_left r R).trans hu) hx)).trans hbound

 theorem tight_of_characteristic_limit (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z))) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) := by
  apply isTightMeasureSet_of_inner_tendsto (𝕜 := ℝ)
  intro a
  simpa only [iSup_range] using projection_tail_tendsto μ a
    (KFCausalCharacteristicTailControl.eventual_projection_tail μ f hf hf0 hc a)

 theorem exists_weak_subsequence (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z))) :
    ∃ ν : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ν) := by
  have ht := tight_of_characteristic_limit μ f hf hf0 hc
  have he : {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range μ} =
      Set.range (fun n => (μ n : Measure E)) := by
    ext ν
    constructor
    · rintro ⟨ν',⟨n,rfl⟩,rfl⟩
      exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩
      exact ⟨μ n,⟨n,rfl⟩,rfl⟩
  rw [← he] at ht
  obtain ⟨ν,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet ht).isSeqCompact
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨ν,φ,hφ,hlim⟩

#print axioms projection_tail_tendsto
#print axioms tight_of_characteristic_limit
#print axioms exists_weak_subsequence

end
end UnifiedTheory.Audit.KFCausalCharacteristicTightness
