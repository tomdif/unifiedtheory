/- A countable family of finite spacetime limits with derived physical
time bounds and exact agreement on common subwindows. -/
import UnifiedTheory.Audit.KFCausalSpacetimeRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (Square)
open UnifiedTheory.Audit.KFCausalCompactTimeMarginal
open UnifiedTheory.Audit.KFCausalLocalTimeMarginal
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests (finitePair)
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction
open UnifiedTheory.Audit.KFCausalCompactTimeRestriction

structure Family {K : Type*} (b c : K → ℝ) (s : ℝ) (budget : ℝ → ℝ) where
  positive : K → FiniteMeasure Square
  negative : K → FiniteMeasure Square
  time_bound : ∀ T i, |b i-s| ≤ T → |c i-s| ≤ T →
    (timeMarginal (positive i+negative i) : Measure Spectrum) ≤
      (timeBound (b i) (c i) (budget T) : Measure Spectrum)
  full_window : ∀ i, (positive i).restrict (timeStrip (b i) (c i)) = positive i ∧
    (negative i).restrict (timeStrip (b i) (c i)) = negative i
  overlap : ∀ i j u v, u ≤ v → b i ≤ u → v ≤ c i → b j ≤ u → v ≤ c j →
    (positive i).restrict (timeStrip u v) = (positive j).restrict (timeStrip u v) ∧
    (negative i).restrict (timeStrip u v) = (negative j).restrict (timeStrip u v)

variable {K : Type*} {b c : K → ℝ} {s : ℝ} {budget : ℝ → ℝ}

def Family.local (G : Family b c s budget) (i : K) : Pair :=
  finitePair (G.positive i) (G.negative i)

theorem Family.local_overlap (G : Family b c s budget) (i j : K) (u v : ℝ)
    (huv : u ≤ v) (hiu : b i ≤ u) (hvi : v ≤ c i) (hju : b j ≤ u) (hvj : v ≤ c j) :
    restrictPair (G.local i) u v = restrictPair (G.local j) u v := by
  have he := G.overlap i j u v huv hiu hvi hju hvj
  exact (finitePair_restrict _ _ u v).symm.trans
    ((congrArg₂ finitePair he.1 he.2).trans (finitePair_restrict _ _ u v))

theorem Family.local_full_window (G : Family b c s budget) (i : K) :
    restrictPair (G.local i) (b i) (c i) = G.local i := by
  have he := G.full_window i
  exact (finitePair_restrict _ _ _ _).symm.trans (congrArg₂ finitePair he.1 he.2)

theorem Family.compact_nested (G : Family b c s budget) (i j : K)
    (hj : b j ≤ c j) (hb : b i ≤ b j) (hc : c j ≤ c i) :
    (G.positive i).restrict (timeStrip (b j) (c j)) = G.positive j ∧
      (G.negative i).restrict (timeStrip (b j) (c j)) = G.negative j := by
  have he := G.overlap i j (b j) (c j) hj hb hc le_rfl le_rfl
  exact ⟨he.1.trans (G.full_window j).1,he.2.trans (G.full_window j).2⟩

theorem Family.local_nested (G : Family b c s budget) (i j : K)
    (hj : b j ≤ c j) (hb : b i ≤ b j) (hc : c j ≤ c i) :
    restrictPair (G.local i) (b j) (c j) = G.local j :=
  (G.local_overlap i j (b j) (c j) hj hb hc le_rfl le_rfl).trans (G.local_full_window j)

theorem Family.local_time_bound (G : Family b c s budget) (T : ℝ) (i : K)
    (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) :
    localTimeMarginal (G.positive i) (G.negative i) ≤
      ENNReal.ofReal (budget T) • volume.restrict (Icc (b i) (c i)) :=
  local_time_domination _ _ _ _ _ (G.time_bound T i hb hc)

theorem Family.dominates (G : Family b c s budget) (i : K) :
    ∃ C, (timeMarginal (G.positive i+G.negative i) : Measure Spectrum) ≤
      (timeBound (b i) (c i) C : Measure Spectrum) := by
  refine ⟨budget (|b i-s|+|c i-s|),G.time_bound _ i ?_ ?_⟩
  · linarith [abs_nonneg (c i-s)]
  · linarith [abs_nonneg (b i-s)]

theorem Family.no_time_atoms (G : Family b c s budget) (i : K) (t : ℝ) :
    (G.local i).positive ({t} ×ˢ univ)+(G.local i).negative ({t} ×ˢ univ) = 0 := by
  obtain ⟨C,hC⟩ := G.dominates i
  exact local_time_slice_zero _ _ _ _ C hC t

theorem Family.time_absolutelyContinuous (G : Family b c s budget) (i : K) :
    localTimeMarginal (G.positive i) (G.negative i) ≪ volume.restrict (Icc (b i) (c i)) := by
  obtain ⟨C,hC⟩ := G.dominates i
  exact local_time_absolutelyContinuous _ _ _ _ C hC

#print axioms Family.local_overlap
#print axioms Family.local_full_window
#print axioms Family.compact_nested
#print axioms Family.local_nested
#print axioms Family.local_time_bound
#print axioms Family.dominates
#print axioms Family.no_time_atoms
#print axioms Family.time_absolutelyContinuous
end
end UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows
