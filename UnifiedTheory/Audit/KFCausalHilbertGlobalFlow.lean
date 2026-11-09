/- Global bounded-operator propagators on a complex Hilbert space, constructed by gluing the
arbitrarily long interval solutions using uniqueness on overlaps. -/
import UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertGlobalFlow
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

def intervalFlow (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, star (A t)= -A t)
    (T : ℝ) (hT : 0 ≤ T) : ℝ → M :=
  Classical.choose (exists_interval_propagator A hA hskew T hT)

theorem intervalFlow_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (T : ℝ) (hT : 0 ≤ T) :
    intervalFlow A hA hskew T hT 0=1 :=
  (Classical.choose_spec (exists_interval_propagator A hA hskew T hT)).1

theorem intervalFlow_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (T : ℝ) (hT : 0 ≤ T) (t : ℝ)
    (ht : t ∈ Icc (-T) T) :
    HasDerivWithinAt (intervalFlow A hA hskew T hT)
      (A t*intervalFlow A hA hskew T hT t) (Icc (-T) T) t :=
  (Classical.choose_spec (exists_interval_propagator A hA hskew T hT)).2 t ht

theorem intervalFlow_agree (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (t : ℝ) (hs : t ∈ Icc (-S) S) (ht : t ∈ Icc (-T) T) :
    intervalFlow A hA hskew S hS t=intervalFlow A hA hskew T hT t := by
  have hST : 0 ≤ min S T := le_min hS hT
  have hsubS : Icc (-min S T) (min S T) ⊆ Icc (-S) S :=
    Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsubT : Icc (-min S T) (min S T) ⊆ Icc (-T) T :=
    Icc_subset_Icc (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  apply interval_unique A _ _ hskew (min S T) hST
  · intro s hs
    exact (intervalFlow_derivative A hA hskew S hS s (hsubS hs)).mono hsubS
  · intro s hs
    exact (intervalFlow_derivative A hA hskew T hT s (hsubT hs)).mono hsubT
  · rw [intervalFlow_initial,intervalFlow_initial]
  · refine ⟨?_,le_min hs.2 ht.2⟩
    rcases le_total S T with h | h
    · simpa only [min_eq_left h] using hs.1
    · simpa only [min_eq_right h] using ht.1

/-- Each point is evaluated in an interval containing it in its interior.
Uniqueness makes these choices agree on every overlap. -/
def globalFlow (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, star (A t)= -A t) : ℝ → M :=
  fun t => intervalFlow A hA hskew (|t|+1) (by positivity) t

theorem globalFlow_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) : globalFlow A hA hskew 0=1 :=
  intervalFlow_initial A hA hskew _ _

theorem globalFlow_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (t : ℝ) :
    HasDerivAt (globalFlow A hA hskew) (A t*globalFlow A hA hskew t) t := by
  let T := |t|+2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ht : t ∈ Ioo (-T) T := by
    constructor <;> dsimp [T] <;> linarith [le_abs_self t,neg_abs_le t]
  have he : globalFlow A hA hskew =ᶠ[𝓝 t] intervalFlow A hA hskew T hT := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    apply intervalFlow_agree A hA hskew (|s|+1) T (by positivity) hT s
    · constructor <;> linarith [le_abs_self s,neg_abs_le s]
    · exact ⟨hs.1.le,hs.2.le⟩
  have hd := (intervalFlow_derivative A hA hskew T hT t ⟨ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hg := hd.congr_of_eventuallyEq he
  simpa only [he.eq_of_nhds] using hg

theorem exists_global_propagator (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) :
    ∃ U : ℝ → M, U 0=1 ∧ ∀ t, HasDerivAt U (A t*U t) t :=
  ⟨globalFlow A hA hskew,globalFlow_initial A hA hskew,globalFlow_derivative A hA hskew⟩

theorem global_solution_unique (A U V : ℝ → M) (hskew : ∀ t, star (A t)= -A t)
    (hU : ∀ t, HasDerivAt U (A t*U t) t) (hV : ∀ t, HasDerivAt V (A t*V t) t)
    (hinit : U 0=V 0) : U=V := by
  funext t
  exact interval_unique A U V hskew |t| (abs_nonneg t)
    (fun s _ => (hU s).hasDerivWithinAt) (fun s _ => (hV s).hasDerivWithinAt)
    hinit t ⟨neg_abs_le t,le_abs_self t⟩

theorem existsUnique_global_propagator (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) :
    ∃! U : ℝ → M, U 0=1 ∧ ∀ t, HasDerivAt U (A t*U t) t := by
  obtain ⟨U,hinit,hU⟩ := exists_global_propagator A hA hskew
  refine ⟨U,⟨hinit,hU⟩,?_⟩
  intro V hV
  exact global_solution_unique A V U hskew hV.2 hU (hV.1.trans hinit.symm)

theorem globalFlow_gram (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (t : ℝ) :
    star (globalFlow A hA hskew t)*globalFlow A hA hskew t=1 := by
  have hg := linear_gram_constant A (globalFlow A hA hskew) hskew |t| (abs_nonneg t)
    (fun s _ => (globalFlow_derivative A hA hskew s).hasDerivWithinAt)
    t ⟨neg_abs_le t,le_abs_self t⟩
  simpa [globalFlow_initial] using hg

/-- Uniqueness at an arbitrary initial time. -/
theorem global_solution_unique_at (A U V : ℝ → M) (hskew : ∀ t, star (A t)= -A t)
    (hU : ∀ t, HasDerivAt U (A t*U t) t) (hV : ∀ t, HasDerivAt V (A t*V t) t)
    (s : ℝ) (hinit : U s=V s) : U=V := by
  have he : (fun u => U (s+u)) = (fun u => V (s+u)) := by
    apply global_solution_unique (fun u => A (s+u)) _ _ (fun u => hskew (s+u))
    · intro u
      simpa using (hU (s+u)).scomp u ((hasDerivAt_id u).const_add s)
    · intro u
      simpa using (hV (s+u)).scomp u ((hasDerivAt_id u).const_add s)
    · simpa using hinit
  funext t
  simpa using congrFun he (t-s)

#print axioms intervalFlow_agree
#print axioms globalFlow_derivative
#print axioms existsUnique_global_propagator
#print axioms globalFlow_gram
#print axioms global_solution_unique_at

end
end UnifiedTheory.Audit.KFCausalHilbertGlobalFlow
