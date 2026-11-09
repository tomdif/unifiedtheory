/- Reflection copies of arbitrary plaquette coupling profiles. Crossing
coefficients are kept unchanged; interior coefficients are copied from one
half. In particular, genuine deletion profiles remain genuine deletions. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonCutProfiles
import UnifiedTheory.Clay.YangMills.SpatialWilsonInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonHalfCopies
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels SpatialWilsonCutProfiles

variable (n : ℕ) [NeZero n]


def crossingPart (γ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if Crossing n p then γ p else 0

def interiorPart (γ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if Crossing n p then 0 else γ p

def copyPositive (γ : Plaquette n → ℝ) (p : Plaquette n) : ℝ :=
  crossingPart n γ p + doubled n (positivePart n (interiorPart n γ)) p

def copyNegative (γ : Plaquette n → ℝ) (p : Plaquette n) : ℝ :=
  crossingPart n γ p + doubled n (negativePart n (interiorPart n γ)) p

omit [NeZero n] in
theorem crossing_reflected (p : Plaquette n) :
    Crossing n (reflectPlaquette n p) ↔ Crossing n p := by
  constructor
  · intro h
    have he := SpatialWilsonInsertion.crossing_fixed n _ h
    rw [reflectPlaquette_involutive n p] at he
    rwa [← he] at h
  · intro h
    rwa [SpatialWilsonInsertion.crossing_fixed n p h]

omit [NeZero n] in
theorem crossing_invariant (γ : Plaquette n → ℝ) (p : Plaquette n) :
    crossingPart n γ (reflectPlaquette n p) = crossingPart n γ p := by
  classical
  by_cases h : Crossing n p
  · rw [SpatialWilsonInsertion.crossing_fixed n p h]
  · simp only [crossingPart, crossing_reflected, if_neg h]

omit [NeZero n] in
theorem crossing_nonneg (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p) (p : Plaquette n) :
    0 ≤ crossingPart n γ p := by
  classical
  unfold crossingPart
  split_ifs <;> simp [hγ]

omit [NeZero n] in
theorem parts_add (γ : Plaquette n → ℝ) (p : Plaquette n) :
    crossingPart n γ p + interiorPart n γ p = γ p := by
  classical
  simp only [crossingPart, interiorPart]
  split <;> simp

omit [NeZero n] in
theorem interior_crossing (γ : Plaquette n → ℝ) (p : Plaquette n) (hp : Crossing n p) :
    interiorPart n γ p = 0 := by
  classical
  simp [interiorPart, hp]

theorem vertex_reflected_side (x : SpatialVertex (2 * n)) :
    VertexPositive n (reflectVertex (2 * n) x) ↔ ¬ VertexPositive n x := by
  have hx := (x 0).val_lt
  have hn := NeZero.pos n
  have he := PeriodicHalfGeometry.val_neg_add_one (2 * n) (x 0)
  change (-(x 0 + 1)).val < n ↔ ¬ (x 0).val < n
  rw [he]
  omega

theorem interior_reflected_side (p : Plaquette n) (hp : ¬ Crossing n p) :
    VertexPositive n (reflectPlaquette n p).1 ↔ ¬ VertexPositive n p.1 := by
  simp only [reflectPlaquette, reflectLink]
  split_ifs with hi
  · rw [vertex_reflected_side, ← hi, noncrossing_side n p hp]
  · exact vertex_reflected_side n p.1

open Classical in
theorem copyPositive_value (γ : Plaquette n → ℝ) (p : Plaquette n) :
    copyPositive n γ p = if Crossing n p then γ p else
      if VertexPositive n p.1 then γ p else γ (reflectPlaquette n p) := by
  classical
  by_cases hc : Crossing n p
  · simp [copyPositive, crossingPart, doubled, positivePart, reflected,
      interiorPart, hc, SpatialWilsonInsertion.crossing_fixed n p hc]
  · have hr := interior_reflected_side n p hc
    by_cases hs : VertexPositive n p.1 <;>
      simp [copyPositive, crossingPart, doubled, positivePart, reflected,
        interiorPart, hc, crossing_reflected, hr, hs]

open Classical in
theorem copyNegative_value (γ : Plaquette n → ℝ) (p : Plaquette n) :
    copyNegative n γ p = if Crossing n p then γ p else
      if VertexPositive n p.1 then γ (reflectPlaquette n p) else γ p := by
  classical
  by_cases hc : Crossing n p
  · simp [copyNegative, crossingPart, doubled, negativePart, reflected,
      interiorPart, hc, SpatialWilsonInsertion.crossing_fixed n p hc]
  · have hr := interior_reflected_side n p hc
    by_cases hs : VertexPositive n p.1 <;>
      simp [copyNegative, crossingPart, doubled, negativePart, reflected,
        interiorPart, hc, crossing_reflected, hr, hs]

theorem copies_range (γ : Plaquette n → ℝ) (A : Set ℝ) (hγ : ∀ p, γ p ∈ A)
    (p : Plaquette n) : copyPositive n γ p ∈ A ∧ copyNegative n γ p ∈ A := by
  classical
  rw [copyPositive_value, copyNegative_value]
  split_ifs <;> exact ⟨hγ _,hγ _⟩

omit [NeZero n] in
theorem copies_invariant (γ : Plaquette n → ℝ) (p : Plaquette n) :
    copyPositive n γ (reflectPlaquette n p) = copyPositive n γ p ∧
    copyNegative n γ (reflectPlaquette n p) = copyNegative n γ p := by
  simp only [copyPositive, copyNegative, crossing_invariant, doubled_invariant, and_self]

omit [NeZero n] in
theorem perturbation_original (γ : Plaquette n → ℝ) (p : Plaquette n) :
    crossingPart n γ p - (-interiorPart n γ p) = γ p := by
  simpa only [sub_neg_eq_add] using parts_add n γ p

omit [NeZero n] in
theorem perturbation_copies (γ : Plaquette n → ℝ) (p : Plaquette n) :
    crossingPart n γ p - doubled n (positivePart n (fun q => -interiorPart n γ q)) p =
      copyPositive n γ p ∧
    crossingPart n γ p - doubled n (negativePart n (fun q => -interiorPart n γ q)) p =
      copyNegative n γ p := by
  classical
  simp only [copyPositive, copyNegative, doubled, reflected, positivePart, negativePart]
  split_ifs <;> constructor <;> ring

theorem sum_reflected (γ : Plaquette n → ℝ) :
    ∑ p, reflected n γ p = ∑ p, γ p :=
  Equiv.sum_comp (plaquetteEquiv n) γ

theorem sum_doubled (γ : Plaquette n → ℝ) :
    ∑ p, doubled n γ p = 2 * ∑ p, γ p := by
  simp only [doubled, Finset.sum_add_distrib, sum_reflected]
  ring

theorem copies_sum (γ : Plaquette n → ℝ) :
    (∑ p, copyPositive n γ p) + (∑ p, copyNegative n γ p) = 2 * ∑ p, γ p := by
  simp only [copyPositive, copyNegative, Finset.sum_add_distrib, sum_doubled]
  have hi : (∑ p, positivePart n (interiorPart n γ) p) +
      (∑ p, negativePart n (interiorPart n γ) p) = ∑ p, interiorPart n γ p := by
    rw [← Finset.sum_add_distrib]
    simp only [SpatialWilsonCutProfiles.parts_add]
  have hc : (∑ p, crossingPart n γ p) + (∑ p, interiorPart n γ p) = ∑ p, γ p := by
    rw [← Finset.sum_add_distrib]
    simp only [parts_add]
  linarith

theorem copies_deficit (γ : Plaquette n → ℝ) (s : ℝ) :
    (∑ p, (s - copyPositive n γ p)) + (∑ p, (s - copyNegative n γ p)) =
      2 * ∑ p, (s - γ p) := by
  simp only [Finset.sum_sub_distrib]
  linarith [copies_sum n γ]

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonHalfCopies
