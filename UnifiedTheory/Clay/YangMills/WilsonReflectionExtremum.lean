/- Finite extremal formulation of the actual Wilson reflection problem.
At a maximum both reflected copies retain the maximum, so a minimizing
geometric rank rules out any cut that strictly lowers its average. -/
import UnifiedTheory.Clay.YangMills.WilsonFramedDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonReflectionExtremum
noncomputable section
open SpatialPlaquetteCutGeometry WilsonPlaquetteFrames WilsonFramedDeletion

theorem schwarz_at_max {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbmax : b ≤ a) (hcmax : c ≤ a) (h : a ^ 2 ≤ b * c) : b = a ∧ c = a := by
  by_cases hz : a = 0
  · constructor <;> linarith
  · have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hcmax hb]
    · nlinarith [mul_le_mul_of_nonneg_right hbmax hc]

theorem finite_max_min_rank {X : Type*} [Finite X] [Nonempty X]
    (value : X → ℝ) (rank : X → ℕ) :
    ∃ x, (∀ y, value y ≤ value x) ∧ (∀ y, value y = value x → rank x ≤ rank y) := by
  classical
  letI := Fintype.ofFinite X
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image Finset.univ value Finset.univ_nonempty
  let ties : Finset X := Finset.univ.filter (fun y => value y = value x)
  have ht : ties.Nonempty := ⟨x,by simp [ties]⟩
  obtain ⟨z,hz,hmin⟩ := Finset.exists_min_image ties rank ht
  have he : value z = value x := (Finset.mem_filter.mp hz).2
  refine ⟨z,fun y => he ▸ hx y (Finset.mem_univ _),?_⟩
  intro y hy
  apply hmin y
  simp only [ties, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hy.trans he

variable (n : ℕ) [NeZero n]

theorem maximal_copies (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ)
    (hmax : ∀ A, priced n A s β a ≤ priced n S s β a) (F : Frame n) :
    priced n (positiveSet n F S) s β a = priced n S s β a ∧
    priced n (negativeSet n F S) s β a = priced n S s β a :=
  schwarz_at_max (priced_nonneg n S s β a) (priced_nonneg n _ s β a)
    (priced_nonneg n _ s β a) (hmax _) (hmax _) (priced_schwarz n F S s hs β hβ a)

/-- This is an actual finite-regulator Wilson maximizer, not an assumed
reflection-positive modified vacuum or an assumed numerical norm bound. -/
theorem exists_ranked_maximizer (s : ℝ) (hs : 0 ≤ s) (β : ℝ) (hβ : 0 ≤ β)
    (a : ℝ) (rank : Finset (Plaquette n) → ℕ) :
    ∃ S, (∀ A, priced n A s β a ≤ priced n S s β a) ∧
      (∀ F : Frame n,
        priced n (positiveSet n F S) s β a = priced n S s β a ∧
        priced n (negativeSet n F S) s β a = priced n S s β a ∧
        rank S ≤ rank (positiveSet n F S) ∧ rank S ≤ rank (negativeSet n F S)) := by
  obtain ⟨S,hmax,hmin⟩ := finite_max_min_rank (fun A => priced n A s β a) rank
  refine ⟨S,hmax,?_⟩
  intro F
  have h := maximal_copies n S s hs β hβ a hmax F
  exact ⟨h.1,h.2,hmin _ h.1,hmin _ h.2⟩

theorem exists_count_balanced_maximizer (s : ℝ) (hs : 0 ≤ s) (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) :
    ∃ S, (∀ A, priced n A s β a ≤ priced n S s β a) ∧
      (∀ F : Frame n, (positiveSet n F S).card = S.card ∧ (negativeSet n F S).card = S.card) := by
  obtain ⟨S,hmax,hmin⟩ := exists_ranked_maximizer n s hs β hβ a Finset.card
  refine ⟨S,hmax,?_⟩
  intro F
  have h := hmin F
  have hc := copies_card n F S
  constructor <;> omega

end
end UnifiedTheory.Clay.YangMills.WilsonReflectionExtremum
