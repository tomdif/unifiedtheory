/- Finite support propagation for the actual Wilson random-color update.
The graph is defined by actual shared plaquettes; sparse conditional influences
and finite coordinate telescoping prove locality, rather than assuming it.
The iteration count is auxiliary sampler time, not physical transfer time. -/
import UnifiedTheory.Clay.YangMills.WilsonParallelContraction
import Mathlib.Logic.Function.DependsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSupportPropagation
noncomputable section
open MeasureTheory WilsonIndependentBlocks WilsonInfluenceGeometry
open FiniteProductInfluence ParallelOscillation WilsonParallelContraction

section Support
variable {I X Y : Type*} [Finite I]

/-- Finite coordinate telescoping turns one-coordinate invariance into genuine support. -/
theorem dependsOn_of_single_changes (F : (I → X) → Y) (A : Finset I)
    (hF : ∀ i, i ∉ A → ∀ x y : I → X,
      (∀ j, j ≠ i → x j = y j) → F x = F y) : DependsOn F (A : Set I) := by
  classical
  letI := Fintype.ofFinite I
  intro x y hxy
  let z (S : Finset I) (i : I) := if i ∈ S then x i else y i
  have ht : ∀ S : Finset I, (∀ i ∈ S, i ∉ A) → F (z S) = F y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have hz : z ∅ = y := by funext i; simp [z]
      rw [hz]
    | @insert i S hi ih =>
      intro hS
      have he : F (z (insert i S)) = F (z S) := by
        apply hF i (hS i (Finset.mem_insert_self _ _))
        intro j hj
        simp [z, hj]
      exact he.trans (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
  have hz : z Aᶜ = x := by
    funext i
    by_cases hi : i ∈ A
    · simp only [z, Finset.mem_compl, hi, not_true_eq_false, if_false]
      exact (hxy i hi).symm
    · simp [z, hi]
  rw [← hz]
  exact ht Aᶜ (fun _ hi => Finset.mem_compl.mp hi)

/-- Dependence on A is equivalent to insensitivity to every coordinate outside A. -/
theorem dependsOn_iff_single_changes (F : (I → X) → Y) (A : Finset I) :
    DependsOn F (A : Set I) ↔ ∀ i, i ∉ A → ∀ x y : I → X,
      (∀ j, j ≠ i → x j = y j) → F x = F y := by
  constructor
  · intro hF i hi x y hxy
    apply hF
    intro j hj
    apply hxy j
    intro he
    subst j
    exact hi hj
  · exact dependsOn_of_single_changes F A

/-- Vanishing one-coordinate oscillations outside A give actual finite support. -/
theorem dependsOn_of_oscBound (F : (I → X) → ℝ) (d : I → ℝ)
    (hF : OscBound F d) (A : Finset I) (hd : ∀ i, i ∉ A → d i = 0) :
    DependsOn F (A : Set I) := by
  apply dependsOn_of_single_changes F A
  intro i hi x y hxy
  have h := hF i x y hxy
  rw [hd i hi] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

variable [DecidableEq I] [TopologicalSpace X] [CompactSpace X]

/-- A supported continuous observable has a sparse finite oscillation budget. -/
theorem supported_oscillation (F : C(I → X, ℝ)) (A : Finset I)
    (hF : DependsOn (F : (I → X) → ℝ) (A : Set I)) :
    OscBound F (fun i => if i ∈ A then 2 * ‖F‖ else 0) := by
  classical
  intro i x y hxy
  dsimp only
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    exact uniform_oscillation F i x y hxy
  · rw [if_neg hi, (dependsOn_iff_single_changes F A).mp hF i hi x y hxy]
    simp

end Support

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance colorDecidableEq : DecidableEq WilsonParallelColors.Color := Classical.decEq _

/-- One closed graph layer, using the repository's actual shared oriented plaquettes. -/
def layer (A : Finset (Link n)) : Finset (Link n) := by
  classical
  exact Finset.univ.filter (fun b => b ∈ A ∨ ∃ a ∈ A, (sharedPlaquettes n a b).Nonempty)

@[simp] theorem mem_layer (A : Finset (Link n)) (b : Link n) :
    b ∈ layer n A ↔ b ∈ A ∨ ∃ a ∈ A, (sharedPlaquettes n a b).Nonempty := by
  classical
  simp [layer]

theorem subset_layer (A : Finset (Link n)) : A ⊆ layer n A :=
  fun _ ha => (mem_layer n A _).mpr (Or.inl ha)

theorem layer_mono {A B : Finset (Link n)} (hAB : A ⊆ B) : layer n A ⊆ layer n B := by
  intro b hb
  rcases (mem_layer n A b).mp hb with hb | ⟨a, ha, hp⟩
  · exact (mem_layer n B b).mpr (Or.inl (hAB hb))
  · exact (mem_layer n B b).mpr (Or.inr ⟨a, hAB ha, hp⟩)

/-- Leaving the one-layer neighborhood forces every incoming geometric multiplicity to vanish. -/
theorem multiplicity_zero_of_outside (A : Finset (Link n)) (a b : Link n)
    (ha : a ∈ A) (hb : b ∉ layer n A) : WilsonInfluenceGeometry.multiplicity n a b = 0 := by
  unfold WilsonInfluenceGeometry.multiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hp
  exact hb ((mem_layer n A b).mpr (Or.inr ⟨a, ha, hp⟩))

theorem coefficient_zero_of_outside (β : ℝ) (A : Finset (Link n)) (a b : Link n)
    (ha : a ∈ A) (hb : b ∉ layer n A) : coefficient n β a b = 0 := by
  rw [coefficient, multiplicity_zero_of_outside n A a b ha hb]
  simp

/-- A finite graph neighborhood of an actual link support. -/
def neighborhood (A : Finset (Link n)) : ℕ → Finset (Link n)
  | 0 => A
  | k + 1 => layer n (neighborhood A k)

@[simp] theorem neighborhood_zero (A : Finset (Link n)) : neighborhood n A 0 = A := rfl

@[simp] theorem neighborhood_succ (A : Finset (Link n)) (k : ℕ) :
    neighborhood n A (k + 1) = layer n (neighborhood n A k) := rfl

theorem neighborhood_step_subset (A : Finset (Link n)) (k : ℕ) :
    neighborhood n A k ⊆ neighborhood n A (k + 1) := subset_layer n _

theorem neighborhood_mono (A : Finset (Link n)) {k l : ℕ} (hkl : k ≤ l) :
    neighborhood n A k ⊆ neighborhood n A l := by
  have hm : Monotone (neighborhood n A) :=
    monotone_nat_of_le_succ (neighborhood_step_subset n A)
  exact hm hkl

theorem neighborhood_mono_support {A B : Finset (Link n)} (hAB : A ⊆ B) (k : ℕ) :
    neighborhood n A k ⊆ neighborhood n B k := by
  induction k with
  | zero => exact hAB
  | succ k ih => exact layer_mono n ih

theorem neighborhood_add (A : Finset (Link n)) (k l : ℕ) :
    neighborhood n A (k + l) = neighborhood n (neighborhood n A k) l := by
  induction l with
  | zero => simp
  | succ l ih => simp only [Nat.add_succ, neighborhood_succ, ih]

/-- The actual sparse influence budget has no coordinates outside one plaquette layer. -/
theorem colorBound_zero_of_outside (β : ℝ) (A : Finset (Link n)) (d : Link n → ℝ)
    (hd : ∀ a, a ∉ A → d a = 0) (b : Link n) (hb : b ∉ layer n A) :
    colorBound (Color := WilsonParallelColors.Color) (coefficient n β) d b = 0 := by
  have hbA : b ∉ A := fun ha => hb (subset_layer n A ha)
  have hs : ∑ a, coefficient n β a b * d a = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a ∈ A
    · rw [coefficient_zero_of_outside n β A a b ha hb, zero_mul]
    · rw [hd a ha, mul_zero]
  simp only [colorBound, hd b hbA, hs, mul_zero, add_zero]

omit [NeZero n] in
/-- An actual Wilson plaquette term depends only on its four incident positive-link coordinates. -/
theorem plaquetteTerm_dependsOn (p : PeriodicLattice4.PlaquetteIndex n) :
    DependsOn (fun U : State n => plaquetteTerm n Q WilsonSingleLinkStaples.character 2
      (WilsonCoordinateInfluence.toConfiguration n U) p)
      (incidentLinks n p : Set (Link n)) := by
  intro U V hUV
  have hh := plaquette_congr n Q p (WilsonCoordinateInfluence.toConfiguration n U)
    (WilsonCoordinateInfluence.toConfiguration n V) (fun e he =>
      hUV (edgeCoord n e) ((mem_incidentLinks n p _).mpr he))
  exact congrArg (fun q : Q => 2 - (WilsonSingleLinkStaples.character q).re) hh

/-- The actual union of the incident coordinates of a finite plaquette support. -/
def plaquetteSupport (P : Finset (PeriodicLattice4.PlaquetteIndex n)) : Finset (Link n) :=
  P.biUnion (incidentLinks n)

/-- Sparse Wilson source coefficients give a proved coordinate support for the full source. -/
theorem source_dependsOn (f : PeriodicLattice4.PlaquetteIndex n → ℝ)
    (P : Finset (PeriodicLattice4.PlaquetteIndex n)) (hf : ∀ p, p ∉ P → f p = 0) :
    DependsOn (fun U : State n => WilsonBlockIntegration.source n Q
      WilsonSingleLinkStaples.character 2 f (WilsonCoordinateInfluence.toConfiguration n U))
      (plaquetteSupport n P : Set (Link n)) := by
  classical
  intro U V hUV
  unfold WilsonBlockIntegration.source
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ P
  · have hh := plaquetteTerm_dependsOn n p (fun a ha =>
      hUV a (Finset.mem_biUnion.mpr ⟨p, hp, ha⟩))
    exact congrArg (fun r : ℝ => f p * r) hh
  · rw [hf p hp]
    simp

variable [Fact (1 < n)]
local instance coordinateProbability (β : ℝ) (a : Link n) (U : State n) :
    IsProbabilityMeasure (WilsonCoordinateInfluence.coordinateLaw n β U a) :=
  WilsonCoordinateInfluence.coordinateLaw_probability n β U a

/-- Locality of the original Wilson color update follows from its proved conditional influences. -/
theorem update_dependsOn (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (A : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n))) :
    DependsOn (update n β heven F : State n → ℝ) (layer n A : Set (Link n)) := by
  classical
  let d : Link n → ℝ := fun a => if a ∈ A then 2 * ‖F‖ else 0
  have hd : ∀ a, a ∉ A → d a = 0 := fun a ha => if_neg ha
  have hosc : OscBound (update n β heven F)
      (colorBound (Color := WilsonParallelColors.Color) (coefficient n β) d) := by
    intro j x y hxy
    rw [update_eq_colorAverage, update_eq_colorAverage]
    exact color_oscillation (fun a U => WilsonCoordinateInfluence.coordinateLaw n β U a)
      (WilsonParallelColors.color n heven) (coefficient n β) (localInfluence n β hβ)
      F d (supported_oscillation F A hF) j x y hxy
  exact dependsOn_of_oscBound _ _ hosc (layer n A)
    (colorBound_zero_of_outside n β A d hd)

/-- Every actual auxiliary iterate stays within its finite shared-plaquette neighborhood. -/
theorem iterate_dependsOn (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (A : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n))) (k : ℕ) :
    DependsOn (updateIterate (update n β heven) k F : State n → ℝ)
      (neighborhood n A k : Set (Link n)) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    exact update_dependsOn n β hβ heven (updateIterate (update n β heven) k F)
      (neighborhood n A k) ih

end
end UnifiedTheory.Clay.YangMills.WilsonSupportPropagation
