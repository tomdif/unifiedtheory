/- Global finite-dimensional propagators, constructed by gluing the
arbitrarily long interval solutions using uniqueness on overlaps. -/
import UnifiedTheory.Audit.KFCausalIntervalPropagator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGlobalPropagator
noncomputable section
open Matrix Set Filter
open scoped Matrix.Norms.L2Operator Topology
open UnifiedTheory.Audit.KFCausalIntervalPropagator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

def intervalFlow (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, (A t)ᴴ= -A t)
    (T : ℝ) (hT : 0 ≤ T) : ℝ → M :=
  Classical.choose (exists_interval_propagator A hA hskew T hT)

theorem intervalFlow_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (T : ℝ) (hT : 0 ≤ T) :
    intervalFlow A hA hskew T hT 0=1 :=
  (Classical.choose_spec (exists_interval_propagator A hA hskew T hT)).1

theorem intervalFlow_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (T : ℝ) (hT : 0 ≤ T) (t : ℝ)
    (ht : t ∈ Icc (-T) T) :
    HasDerivWithinAt (intervalFlow A hA hskew T hT)
      (A t*intervalFlow A hA hskew T hT t) (Icc (-T) T) t :=
  (Classical.choose_spec (exists_interval_propagator A hA hskew T hT)).2 t ht

theorem intervalFlow_agree (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
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
def globalFlow (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, (A t)ᴴ= -A t) : ℝ → M :=
  fun t => intervalFlow A hA hskew (|t|+1) (by positivity) t

theorem globalFlow_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) : globalFlow A hA hskew 0=1 :=
  intervalFlow_initial A hA hskew _ _

theorem globalFlow_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (t : ℝ) :
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
    (hskew : ∀ t, (A t)ᴴ= -A t) :
    ∃ U : ℝ → M, U 0=1 ∧ ∀ t, HasDerivAt U (A t*U t) t :=
  ⟨globalFlow A hA hskew,globalFlow_initial A hA hskew,globalFlow_derivative A hA hskew⟩

omit [Nonempty n] in
theorem global_solution_unique (A U V : ℝ → M) (hskew : ∀ t, (A t)ᴴ= -A t)
    (hU : ∀ t, HasDerivAt U (A t*U t) t) (hV : ∀ t, HasDerivAt V (A t*V t) t)
    (hinit : U 0=V 0) : U=V := by
  funext t
  exact interval_unique A U V hskew |t| (abs_nonneg t)
    (fun s _ => (hU s).hasDerivWithinAt) (fun s _ => (hV s).hasDerivWithinAt)
    hinit t ⟨neg_abs_le t,le_abs_self t⟩

theorem existsUnique_global_propagator (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) :
    ∃! U : ℝ → M, U 0=1 ∧ ∀ t, HasDerivAt U (A t*U t) t := by
  obtain ⟨U,hinit,hU⟩ := exists_global_propagator A hA hskew
  refine ⟨U,⟨hinit,hU⟩,?_⟩
  intro V hV
  exact global_solution_unique A V U hskew hV.2 hU (hV.1.trans hinit.symm)

theorem globalFlow_unitary (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (t : ℝ) :
    (globalFlow A hA hskew t)ᴴ*globalFlow A hA hskew t=1 ∧
    globalFlow A hA hskew t*(globalFlow A hA hskew t)ᴴ=1 := by
  have hg := linear_gram_constant A (globalFlow A hA hskew) hskew |t| (abs_nonneg t)
    (fun s _ => (globalFlow_derivative A hA hskew s).hasDerivWithinAt)
    t ⟨neg_abs_le t,le_abs_self t⟩
  have hh : (globalFlow A hA hskew t)ᴴ*globalFlow A hA hskew t=1 := by
    simpa [globalFlow_initial] using hg
  exact ⟨hh,mul_eq_one_comm.mp hh⟩

/-- Evolution between arbitrary initial and final times. For a
time-dependent generator, composition uses the intermediate time. -/
def evolution (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, (A t)ᴴ= -A t)
    (s t : ℝ) : M :=
  globalFlow A hA hskew t*(globalFlow A hA hskew s)ᴴ

theorem evolution_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (s : ℝ) : evolution A hA hskew s s=1 :=
  (globalFlow_unitary A hA hskew s).2

theorem evolution_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (s t : ℝ) :
    HasDerivAt (evolution A hA hskew s) (A t*evolution A hA hskew s t) t := by
  simpa only [evolution,mul_assoc] using
    (globalFlow_derivative A hA hskew t).mul_const (globalFlow A hA hskew s)ᴴ

theorem evolution_compose (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (r s t : ℝ) :
    evolution A hA hskew s t*evolution A hA hskew r s=evolution A hA hskew r t := by
  unfold evolution
  calc
    _ = globalFlow A hA hskew t*
        ((globalFlow A hA hskew s)ᴴ*globalFlow A hA hskew s)*
        (globalFlow A hA hskew r)ᴴ := by simp only [mul_assoc]
    _ = _ := by rw [(globalFlow_unitary A hA hskew s).1,mul_one]

theorem evolution_reverse (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (s t : ℝ) :
    (evolution A hA hskew s t)ᴴ=evolution A hA hskew t s := by
  simp only [evolution,conjTranspose_mul,conjTranspose_conjTranspose]

theorem evolution_unitary (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, (A t)ᴴ= -A t) (s t : ℝ) :
    (evolution A hA hskew s t)ᴴ*evolution A hA hskew s t=1 ∧
    evolution A hA hskew s t*(evolution A hA hskew s t)ᴴ=1 := by
  rw [evolution_reverse,evolution_compose,evolution_compose,
    evolution_initial,evolution_initial]
  exact ⟨rfl,rfl⟩

#print axioms intervalFlow_agree
#print axioms globalFlow_derivative
#print axioms exists_global_propagator
#print axioms global_solution_unique
#print axioms existsUnique_global_propagator
#print axioms globalFlow_unitary
#print axioms evolution_initial
#print axioms evolution_derivative
#print axioms evolution_compose
#print axioms evolution_reverse
#print axioms evolution_unitary

end
end UnifiedTheory.Audit.KFCausalGlobalPropagator
