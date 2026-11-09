/- Exact additive decomposition of the actual open-cylinder Wilson action
when every plaquette contains at most one selected link. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderCoordinates
import UnifiedTheory.Clay.YangMills.WilsonCylinderColors

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderBlockAction
noncomputable section
open WilsonCylinderGeometry WilsonCylinderColors WilsonCylinderCoordinates

section Local
variable {I X : Type*} [DecidableEq I]

def overwrite (S : Finset I) (U V : I → X) : I → X :=
  fun i => if i ∈ S then V i else U i

/-- A supported interaction changes through its sole selected coordinate, if any. -/
theorem supported_decomposition (F : (I → X) → ℝ) (A S : Finset I)
    (hF : DependsOn F (A : Set I))
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ∈ A → b ∈ A → a = b)
    (U V : I → X) :
    F (overwrite S U V) - F U =
      ∑ a ∈ S, (F (Function.update U a (V a)) - F U) := by
  by_cases h : ∃ a ∈ S, a ∈ A
  · obtain ⟨a, haS, haA⟩ := h
    have he : F (overwrite S U V) = F (Function.update U a (V a)) := by
      apply hF
      intro i hi
      by_cases hiS : i ∈ S
      · have hia : i = a := hS i hiS a haS hi haA
        subst i
        simp [overwrite, haS]
      · have hia : i ≠ a := fun hi => hiS (hi ▸ haS)
        simp [overwrite, hiS, Function.update_of_ne hia]
    rw [he]
    symm
    apply Finset.sum_eq_single a
    · intro b hb hba
      have hnot : b ∉ A := fun hbA => hba (hS b hb a haS hbA haA)
      have hf : F (Function.update U b (V b)) = F U := by
        apply hF
        intro i hi
        have hib : i ≠ b := fun hib => hnot (hib ▸ hi)
        exact Function.update_of_ne hib _ _
      rw [hf, sub_self]
    · exact fun hnot => (hnot haS).elim
  · have hnone (a : I) (ha : a ∈ S) : a ∉ A := fun hA => h ⟨a, ha, hA⟩
    have he : F (overwrite S U V) = F U := by
      apply hF
      intro i hi
      have hiS : i ∉ S := fun hiS => hnone i hiS hi
      simp [overwrite, hiS]
    rw [he, sub_self]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hf : F (Function.update U a (V a)) = F U := by
      apply hF
      intro i hi
      have hia : i ≠ a := fun hia => hnone a ha (hia ▸ hi)
      exact Function.update_of_ne hia _ _
    rw [hf, sub_self]
end Local

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
variable (G : Type*) [Group G] [MeasurableSpace G]

omit [NeZero n] [MeasurableSpace G] in
/-- Only the four actual boundary coordinates enter a cylinder plaquette. -/
theorem plaquette_dependsOn (χ : G → ℂ) (c : ℝ) (p : Plaquette n L) :
    DependsOn (fun U : Link n L → G => c - (χ (plaquetteProduct n L U p)).re)
      (incidentLinks n L p : Set (Link n L)) := by
  intro U V hUV
  have he (k : Fin 4) : U (boundary n L p k) = V (boundary n L p k) :=
    hUV _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  simp only [plaquetteProduct, he]

omit [NeZero n] [MeasurableSpace G] in
/-- Each actual plaquette contributes additively under an independent block update. -/
theorem plaquette_decomposition (χ : G → ℂ) (c : ℝ) (p : Plaquette n L)
    (S : Finset (Link n L)) (hS : Independent n L S) (U V : Link n L → G) :
    (c - (χ (plaquetteProduct n L (overwrite S U V) p)).re) -
      (c - (χ (plaquetteProduct n L U p)).re) =
      ∑ a ∈ S, ((c - (χ (plaquetteProduct n L (Function.update U a (V a)) p)).re) -
        (c - (χ (plaquetteProduct n L U p)).re)) :=
  supported_decomposition _ (incidentLinks n L p) S (plaquette_dependsOn n L G χ c p)
    (hS p) U V

omit [MeasurableSpace G] in
/-- Exact full-action difference; no conditional-law independence is assumed. -/
theorem action_decomposition (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Link n L)) (hS : Independent n L S) (U V : Link n L → G) :
    flatAction n L G χ β c (overwrite S U V) - flatAction n L G χ β c U =
      ∑ a ∈ S, (flatAction n L G χ β c (Function.update U a (V a)) -
        flatAction n L G χ β c U) := by
  unfold flatAction
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [plaquette_decomposition n L G χ c _ S hS U V]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_sub_distrib, mul_sub]

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderBlockAction
