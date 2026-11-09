/- A common weakly converging subsequence for countably many finite
measures on a compact metric space. Bounds may hold only eventually and
separately for each family member. Zero masses are allowed. -/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactFiniteMeasureSubsequence
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem global_mass_bound (a : ℕ → ℝ≥0) (C : ℝ) (hb : ∀ᶠ n in atTop, (a n : ℝ) ≤ C) :
    ∃ D : ℝ≥0, ∀ n, a n ≤ D := by
  have he : ∀ᶠ n in atTop, a n ≤ Real.toNNReal C :=
    hb.mono (fun n hn => NNReal.coe_le_coe.mp (hn.trans (Real.le_coe_toNNReal C)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max (Real.toNNReal C) ((Finset.range N).sup a),fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.mpr hn))
  · exact le_max_of_le_left (hN n hn)

variable {E K : Type*} [MetricSpace E] [CompactSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [Nonempty E] [Countable K]

theorem common_subsequence (μ : ℕ → K → FiniteMeasure E)
    (hb : ∀ k, ∃ C : ℝ, ∀ᶠ n in atTop, ((μ n k).mass : ℝ) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : K → FiniteMeasure E,
      ∀ k, Tendsto (fun n => μ (φ n) k) atTop (𝓝 (ν k)) := by
  have hg : ∀ k, ∃ C : ℝ≥0, ∀ n, (μ n k).mass ≤ C := by
    intro k
    obtain ⟨C,hC⟩ := hb k
    exact global_mass_bound (fun n => (μ n k).mass) C hC
  choose C hC using hg
  let z (n : ℕ) (k : K) : ℝ≥0 × ProbabilityMeasure E := ((μ n k).mass,(μ n k).normalize)
  have hcompact : IsCompact {f : K → ℝ≥0 × ProbabilityMeasure E |
      ∀ k, f k ∈ Icc 0 (C k) ×ˢ (univ : Set (ProbabilityMeasure E))} :=
    isCompact_pi_infinite (fun k => isCompact_Icc.prod isCompact_univ)
  have hz (n : ℕ) : z n ∈ {f : K → ℝ≥0 × ProbabilityMeasure E |
      ∀ k, f k ∈ Icc 0 (C k) ×ˢ (univ : Set (ProbabilityMeasure E))} := by
    intro k
    exact ⟨⟨zero_le _,hC k n⟩,mem_univ _⟩
  obtain ⟨f,_,φ,hφ,ht⟩ := hcompact.tendsto_subseq hz
  refine ⟨φ,hφ,fun k => (f k).1 • (f k).2.toFiniteMeasure,fun k => ?_⟩
  have hk := tendsto_pi_nhds.mp ht k
  have hp := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto (f k).2 |>.comp
    ((continuous_snd.tendsto (f k)).comp hk)
  have hs := ((continuous_fst.tendsto (f k)).comp hk).smul hp
  simpa only [Function.comp_apply,z,← FiniteMeasure.self_eq_mass_smul_normalize] using hs

#print axioms global_mass_bound
#print axioms common_subsequence
end
end UnifiedTheory.Audit.KFCausalCompactFiniteMeasureSubsequence
