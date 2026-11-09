/- Symmetric finite time windows cover real spacetime and eventually
contain every point in their interior and every finite time interval. -/
import UnifiedTheory.Audit.KFCausalCompatibleMeasureGluing
import UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def left (s : ℝ) (n : ℕ) : ℝ := s-(n:ℝ)
def right (s : ℝ) (n : ℕ) : ℝ := s+(n:ℝ)
def window (s : ℝ) (n : ℕ) : Set (ℝ × ℝ) := Icc (left s n) (right s n) ×ˢ univ

theorem ordered (s : ℝ) (n : ℕ) : left s n ≤ right s n := by
  dsimp [left,right]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem left_antitone (s : ℝ) : Antitone (left s) := by
  intro i j hij
  exact sub_le_sub_left (by exact_mod_cast hij) s

theorem right_monotone (s : ℝ) : Monotone (right s) := by
  intro i j hij
  change s+(i:ℝ) ≤ s+(j:ℝ)
  have hh : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
  linarith

theorem window_monotone (s : ℝ) : Monotone (window s) := by
  intro i j hij
  exact prod_mono (Icc_subset_Icc (left_antitone s hij) (right_monotone s hij)) subset_rfl

theorem window_measurable (s : ℝ) (n : ℕ) : MeasurableSet (window s n) :=
  measurableSet_Icc.prod MeasurableSet.univ

theorem exists_enclosing (s b c : ℝ) : ∃ n, left s n ≤ b ∧ c ≤ right s n := by
  obtain ⟨n,hn⟩ := exists_nat_ge (max |b-s| |c-s|)
  have hb := le_trans (le_max_left |b-s| |c-s|) hn
  have hc := le_trans (le_max_right |b-s| |c-s|) hn
  refine ⟨n,?_,?_⟩
  · dsimp [left]
    linarith [(abs_le.mp hb).1]
  · dsimp [right]
    linarith [(abs_le.mp hc).2]

theorem window_cover (s : ℝ) : ⋃ n, window s n = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨n,hn⟩ := exists_enclosing s z.1 z.1
  exact mem_iUnion.mpr ⟨n,hn,mem_univ _⟩

theorem window_neighborhood (s : ℝ) (z : ℝ × ℝ) : ∃ n, window s n ∈ 𝓝 z := by
  obtain ⟨n,hn⟩ := exists_nat_gt |z.1-s|
  have hmem : z ∈ Prod.fst ⁻¹' Ioo (left s n) (right s n) := by
    dsimp [left,right]
    exact ⟨by linarith [(abs_lt.mp hn).1],by linarith [(abs_lt.mp hn).2]⟩
  refine ⟨n,mem_of_superset ((isOpen_Ioo.preimage continuous_fst).mem_nhds hmem) ?_⟩
  intro y hy
  exact ⟨⟨hy.1.le,hy.2.le⟩,mem_univ _⟩

#print axioms ordered
#print axioms left_antitone
#print axioms right_monotone
#print axioms window_monotone
#print axioms window_measurable
#print axioms exists_enclosing
#print axioms window_cover
#print axioms window_neighborhood
end
end UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
