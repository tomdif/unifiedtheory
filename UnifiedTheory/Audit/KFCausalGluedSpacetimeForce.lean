/- The consistent force family on expanding windows constructs a unique
global force. Its restriction to every finite time window is finite. -/
import UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalGluedSpacetimeForce
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
open UnifiedTheory.Audit.KFCausalCompatibleMeasureGluing
open UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows (Family)
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction (restrictPair)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)

variable {s : ℝ} {budget : ℝ → ℝ}

def component (G : Family (left s) (right s) s budget) (d : Bool) (n : ℕ) : Measure (ℝ × ℝ) :=
  if d then (G.local n).positive else (G.local n).negative

instance component_finite (G : Family (left s) (right s) s budget) (d : Bool) (n : ℕ) :
    IsFiniteMeasure (component G d n) := by
  cases d <;> dsimp [component] <;> infer_instance

theorem component_nested (G : Family (left s) (right s) s budget) (d : Bool)
    (i j : ℕ) (hij : i ≤ j) : (component G d j).restrict (window s i) = component G d i := by
  have he := G.local_nested j i (ordered s i) (left_antitone s hij) (right_monotone s hij)
  cases d
  · exact congrArg Pair.negative he
  · exact congrArg Pair.positive he

def globalComponent (G : Family (left s) (right s) s budget) (d : Bool) : Measure (ℝ × ℝ) :=
  glue (window s) (component G d)

theorem globalComponent_restrict (G : Family (left s) (right s) s budget) (d : Bool) (n : ℕ) :
    (globalComponent G d).restrict (window s n) = component G d n :=
  glue_restrict_eq (window s) (component G d) (window_measurable s) (window_cover s)
    (overlap_of_nested (window s) (component G d) (window_monotone s) (component_nested G d))
    (fun i => component_nested G d i i le_rfl) n

theorem globalComponent_window_finite (G : Family (left s) (right s) s budget) (d : Bool)
    (b c : ℝ) : IsFiniteMeasure ((globalComponent G d).restrict (Icc b c ×ˢ univ)) := by
  obtain ⟨n,hb,hc⟩ := exists_enclosing s b c
  have hs : Icc b c ×ˢ (univ : Set ℝ) ⊆ window s n :=
    prod_mono (Icc_subset_Icc hb hc) subset_rfl
  rw [← Measure.restrict_restrict_of_subset hs,globalComponent_restrict G d n]
  infer_instance

def globalForce (G : Family (left s) (right s) s budget) : Force where
  positive := globalComponent G true
  negative := globalComponent G false
  positive_finite_window := globalComponent_window_finite G true
  negative_finite_window := globalComponent_window_finite G false

theorem globalForce_window (G : Family (left s) (right s) s budget) (n : ℕ) :
    (globalForce G).window (left s n) (right s n) = G.local n := by
  exact KFCausalGlobalSpacetimeForce.pair_ext _ _
    (globalComponent_restrict G true n) (globalComponent_restrict G false n)

theorem globalForce_subwindow (G : Family (left s) (right s) s budget) (n : ℕ) (b c : ℝ)
    (hb : left s n ≤ b) (hc : c ≤ right s n) :
    (globalForce G).window b c = restrictPair (G.local n) b c := by
  rw [← globalForce_window G n]
  exact ((globalForce G).window_restrict (left s n) (right s n) b c hb hc).symm

theorem globalComponent_unique (G : Family (left s) (right s) s budget) (d : Bool)
    (μ : Measure (ℝ × ℝ)) (hμ : ∀ n, μ.restrict (window s n) = component G d n) :
    μ = globalComponent G d :=
  glue_unique (window s) (component G d) (window_measurable s) (window_cover s)
    (overlap_of_nested (window s) (component G d) (window_monotone s) (component_nested G d))
    (fun i => component_nested G d i i le_rfl) μ hμ

theorem globalForce_unique (G : Family (left s) (right s) s budget) (J : Force)
    (hJ : ∀ n, J.window (left s n) (right s n) = G.local n) :
    J.positive = (globalForce G).positive ∧ J.negative = (globalForce G).negative := by
  constructor
  · exact globalComponent_unique G true J.positive (fun n => congrArg Pair.positive (hJ n))
  · exact globalComponent_unique G false J.negative (fun n => congrArg Pair.negative (hJ n))

theorem globalComponent_apply (G : Family (left s) (right s) s budget) (d : Bool) (n : ℕ)
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hsub : A ⊆ window s n) :
    globalComponent G d A = component G d n A := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ A) (globalComponent_restrict G d n)
  simpa only [Measure.restrict_apply hA,inter_eq_left.mpr hsub] using he

theorem globalForce_no_time_atoms (G : Family (left s) (right s) s budget) (t : ℝ) :
    (globalForce G).positive ({t} ×ˢ univ)+(globalForce G).negative ({t} ×ˢ univ) = 0 := by
  obtain ⟨n,hb,hc⟩ := exists_enclosing s t t
  have hs : {t} ×ˢ (univ : Set ℝ) ⊆ window s n := by
    rintro z ⟨hz,_⟩
    exact ⟨by simpa only [mem_singleton_iff.mp hz] using And.intro hb hc,mem_univ _⟩
  change globalComponent G true _+globalComponent G false _ = 0
  rw [globalComponent_apply G true n _ ((measurableSet_singleton t).prod .univ) hs,
    globalComponent_apply G false n _ ((measurableSet_singleton t).prod .univ) hs]
  exact G.no_time_atoms n t

theorem globalComponent_time_absolutelyContinuous (G : Family (left s) (right s) s budget)
    (d : Bool) : (globalComponent G d).map Prod.fst ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply measurable_fst hA,globalComponent,glue,
    Measure.sum_apply _ (hA.preimage measurable_fst),ENNReal.tsum_eq_zero]
  intro n
  have hc := ((G.time_absolutelyContinuous n).trans Measure.absolutelyContinuous_restrict) hzero
  change (((G.local n).positive+(G.local n).negative).map Prod.fst) A = 0 at hc
  rw [Measure.map_apply measurable_fst hA,Measure.add_apply,add_eq_zero] at hc
  have hn : component G d n (Prod.fst ⁻¹' A) = 0 := by
    cases d
    · exact hc.2
    · exact hc.1
  rw [Measure.restrict_apply (hA.preimage measurable_fst)]
  exact measure_mono_null inter_subset_left hn

#print axioms component_finite
#print axioms component_nested
#print axioms globalComponent_restrict
#print axioms globalComponent_window_finite
#print axioms globalForce_window
#print axioms globalForce_subwindow
#print axioms globalComponent_unique
#print axioms globalForce_unique
#print axioms globalComponent_apply
#print axioms globalForce_no_time_atoms
#print axioms globalComponent_time_absolutelyContinuous
end
end UnifiedTheory.Audit.KFCausalGluedSpacetimeForce
