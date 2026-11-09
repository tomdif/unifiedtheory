/- Literal finite-set deletion under one reflection. Both seam deletions
are retained. The two reflected sets conserve deletion count in average,
and satisfy the actual transfer norm comparison with their own endpoints. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonNormSchwarz
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDeletionReflection
noncomputable section
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels SpatialWilsonHalfCopies
open SpatialWilsonPatchWeights SpatialWilsonColumnTransfer SpatialWilsonNormSchwarz

variable (n : ℕ) [NeZero n]

def positiveIndex (p : Plaquette n) : Plaquette n := by
  classical
  exact if Crossing n p then p else if VertexPositive n p.1 then p else reflectPlaquette n p

def negativeIndex (p : Plaquette n) : Plaquette n := by
  classical
  exact if Crossing n p then p else if VertexPositive n p.1 then reflectPlaquette n p else p

def positiveSet (S : Finset (Plaquette n)) : Finset (Plaquette n) := by
  classical
  exact Finset.univ.filter (fun p => positiveIndex n p ∈ S)

def negativeSet (S : Finset (Plaquette n)) : Finset (Plaquette n) := by
  classical
  exact Finset.univ.filter (fun p => negativeIndex n p ∈ S)

theorem copyPositive_index (γ : Plaquette n → ℝ) (p : Plaquette n) :
    copyPositive n γ p = γ (positiveIndex n p) := by
  classical
  rw [copyPositive_value]
  unfold positiveIndex
  split_ifs <;> rfl

theorem copyNegative_index (γ : Plaquette n → ℝ) (p : Plaquette n) :
    copyNegative n γ p = γ (negativeIndex n p) := by
  classical
  rw [copyNegative_value]
  unfold negativeIndex
  split_ifs <;> rfl

theorem positiveSet_mem (S : Finset (Plaquette n)) (p : Plaquette n) :
    p ∈ positiveSet n S ↔ positiveIndex n p ∈ S := by
  classical
  simp [positiveSet]

theorem negativeSet_mem (S : Finset (Plaquette n)) (p : Plaquette n) :
    p ∈ negativeSet n S ↔ negativeIndex n p ∈ S := by
  classical
  simp [negativeSet]

theorem copyPositive_omitted (S : Finset (Plaquette n)) (s : ℝ) :
    copyPositive n (omitted n S s) = omitted n (positiveSet n S) s := by
  classical
  funext p
  simp only [copyPositive_index, omitted, positiveSet_mem]

theorem copyNegative_omitted (S : Finset (Plaquette n)) (s : ℝ) :
    copyNegative n (omitted n S s) = omitted n (negativeSet n S) s := by
  classical
  funext p
  simp only [copyNegative_index, omitted, negativeSet_mem]

theorem deficit_card (S : Finset (Plaquette n)) (s : ℝ) :
    (∑ p, (s - omitted n S s p)) = (S.card : ℝ) * s := by
  classical
  have he (p : Plaquette n) : s - omitted n S s p = if p ∈ S then s else 0 := by
    by_cases hp : p ∈ S <;> simp [omitted, hp]
  simp only [he]
  simp

theorem copies_card (S : Finset (Plaquette n)) :
    (positiveSet n S).card + (negativeSet n S).card = 2 * S.card := by
  have h := copies_deficit n (omitted n S 1) 1
  rw [copyPositive_omitted, copyNegative_omitted, deficit_card, deficit_card, deficit_card] at h
  simp only [mul_one] at h
  exact_mod_cast h

/-- No alignment or coplanarity assumption is made on the deleted set. -/
theorem deletion_norm_schwarz (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n (omitted n S s) β‖^2 ≤
      ‖transfer n (omitted n (positiveSet n S) s) β‖ *
      ‖transfer n (omitted n (negativeSet n S) s) β‖ := by
  have h := norm_schwarz n (omitted n S s) (omitted_nonneg n S s hs) β hβ
  rwa [copyPositive_omitted, copyNegative_omitted] at h

theorem deletion_priced_choice (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) :
    ‖transfer n (omitted n S s) β‖ * Real.exp (-a * ((S.card : ℝ) * s)) ≤
      ‖transfer n (omitted n (positiveSet n S) s) β‖ *
        Real.exp (-a * (((positiveSet n S).card : ℝ) * s)) ∨
    ‖transfer n (omitted n S s) β‖ * Real.exp (-a * ((S.card : ℝ) * s)) ≤
      ‖transfer n (omitted n (negativeSet n S) s) β‖ *
        Real.exp (-a * (((negativeSet n S).card : ℝ) * s)) := by
  have h := priced_choice n (omitted n S s) (omitted_nonneg n S s hs) β hβ s a
  rwa [copyPositive_omitted, copyNegative_omitted, pricedNorm, pricedNorm, pricedNorm,
    deficit_card, deficit_card, deficit_card] at h

end
end UnifiedTheory.Clay.YangMills.WilsonDeletionReflection
