/- Compatible measures on a countable measurable cover assemble into one
measure. The construction sums restrictions to disjoint pieces of the cover. -/
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompatibleMeasureGluing
noncomputable section
open MeasureTheory Set

variable {E : Type*} [MeasurableSpace E]

def glue (S : ℕ → Set E) (μ : ℕ → Measure E) : Measure E :=
  Measure.sum (fun n => (μ n).restrict (disjointed S n))

theorem glue_restrict (S : ℕ → Set E) (μ : ℕ → Measure E)
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j)) (n : ℕ) :
    (glue S μ).restrict (S n) = (μ n).restrict (S n) := by
  have hd (i : ℕ) : MeasurableSet (disjointed S i) := MeasurableSet.disjointed hS i
  have he (i : ℕ) : ((μ i).restrict (disjointed S i)).restrict (S n) =
      ((μ n).restrict (S n)).restrict (disjointed S i) := by
    rw [Measure.restrict_restrict (hS n),Measure.restrict_restrict (hd i)]
    have hh : S n ∩ disjointed S i ⊆ S i ∩ S n := by
      intro x hx
      exact ⟨disjointed_subset S i hx.2,hx.1⟩
    rw [inter_comm (disjointed S i) (S n)]
    exact Measure.restrict_congr_mono hh (hcompat i n)
  rw [glue,Measure.restrict_sum _ (hS n)]
  simp_rw [he]
  rw [← Measure.restrict_iUnion (disjoint_disjointed S) hd,iUnion_disjointed,hcover,
    Measure.restrict_univ]

theorem glue_restrict_eq (S : ℕ → Set E) (μ : ℕ → Measure E)
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j))
    (hfull : ∀ n, (μ n).restrict (S n) = μ n) (n : ℕ) :
    (glue S μ).restrict (S n) = μ n :=
  (glue_restrict S μ hS hcover hcompat n).trans (hfull n)

theorem glue_restrict_finite (S : ℕ → Set E) (μ : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (μ n)]
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j)) (n : ℕ) :
    IsFiniteMeasure ((glue S μ).restrict (S n)) := by
  rw [glue_restrict S μ hS hcover hcompat n]
  infer_instance

theorem glue_sigmaFinite (S : ℕ → Set E) (μ : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (μ n)]
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j)) :
    SigmaFinite (glue S μ) := by
  refine ⟨⟨⟨S,(fun _ => trivial),?_,hcover⟩⟩⟩
  intro n
  letI := glue_restrict_finite S μ hS hcover hcompat n
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using
    measure_lt_top ((glue S μ).restrict (S n)) univ

theorem glue_unique (S : ℕ → Set E) (μ : ℕ → Measure E)
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j))
    (hfull : ∀ n, (μ n).restrict (S n) = μ n)
    (ν : Measure E) (hν : ∀ n, ν.restrict (S n) = μ n) : ν = glue S μ := by
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro n
  exact (hν n).trans (glue_restrict_eq S μ hS hcover hcompat hfull n).symm

theorem overlap_of_nested (S : ℕ → Set E) (μ : ℕ → Measure E) (hS : Monotone S)
    (hnested : ∀ i j, i ≤ j → (μ j).restrict (S i) = μ i) (i j : ℕ) :
    (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j) := by
  rcases le_total i j with hij | hji
  · rw [inter_eq_left.mpr (hS hij),hnested i i le_rfl,hnested i j hij]
  · rw [inter_eq_right.mpr (hS hji),hnested j i hji,hnested j j le_rfl]

theorem glue_locallyFinite [TopologicalSpace E] (S : ℕ → Set E) (μ : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (μ n)]
    (hS : ∀ n, MeasurableSet (S n)) (hcover : ⋃ n, S n = univ)
    (hcompat : ∀ i j, (μ i).restrict (S i ∩ S j) = (μ j).restrict (S i ∩ S j))
    (hnhds : ∀ x : E, ∃ n, S n ∈ nhds x) : IsLocallyFiniteMeasure (glue S μ) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨n,hn⟩ := hnhds x
  letI := glue_restrict_finite S μ hS hcover hcompat n
  refine ⟨S n,hn,?_⟩
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using
    measure_lt_top ((glue S μ).restrict (S n)) univ

#print axioms glue_restrict
#print axioms glue_restrict_eq
#print axioms glue_restrict_finite
#print axioms glue_sigmaFinite
#print axioms glue_unique
#print axioms overlap_of_nested
#print axioms glue_locallyFinite
end
end UnifiedTheory.Audit.KFCausalCompatibleMeasureGluing
