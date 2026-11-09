/- A volume-independent entrywise Lipschitz constant for the actual Wilson
action when one positive link varies. The six-plaquette geometry is retained. -/
import UnifiedTheory.Clay.YangMills.SingleLinkWilsonOscillation
import UnifiedTheory.Clay.YangMills.UnitaryHaarCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SingleLinkWilsonLipschitz
noncomputable section
open Matrix RegulatedGauge PeriodicLattice4 WilsonUniformVariance SingleLinkWilsonOscillation
open UnitaryCharacterObservables UnitaryEntryEstimates WilsonMomentBounds WilsonCrossingKernel

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem right_mul_entry (A : Matrix.unitaryGroup d ℂ) (M : Matrix d d ℂ) (r : ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ r) (i j : d) :
    ‖(M*(A : Matrix d d ℂ)) i j‖ ≤ (Fintype.card d : ℝ)*r := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖M i k*A k j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : d, r := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (unitary_entry_bound A k j) (norm_nonneg _)).trans
        (by simpa using hM i k)
    _ = _ := by simp

theorem pair_product (A B C D : Matrix.unitaryGroup d ℂ) (r s : ℝ)
    (hA : ∀ i j, ‖A i j-C i j‖ ≤ r) (hB : ∀ i j, ‖B i j-D i j‖ ≤ s) (i j : d) :
    ‖(A*B) i j-(C*D) i j‖ ≤ (Fintype.card d : ℝ)*(r+s) := by
  have he : ((A*B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)-
      ((C*D : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) =
      ((A : Matrix d d ℂ)-(C : Matrix d d ℂ))*(B : Matrix d d ℂ)+
      (C : Matrix d d ℂ)*((B : Matrix d d ℂ)-(D : Matrix d d ℂ)) := by
    simp only [UnitaryGroup.mul_val, sub_mul, mul_sub]
    abel
  change ‖((((A*B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)-
    ((C*D : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)) i j)‖ ≤ _
  rw [he, Matrix.add_apply]
  have hr := right_mul_entry B ((A : Matrix d d ℂ)-(C : Matrix d d ℂ)) r hA i j
  have hs := left_mul_entry C ((B : Matrix d d ℂ)-(D : Matrix d d ℂ)) s hB i j
  exact (norm_add_le _ _).trans (by linarith)

theorem inverse_pair (A B : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (h : ∀ i j, ‖A i j-B i j‖ ≤ r) (i j : d) : ‖A⁻¹ i j-B⁻¹ i j‖ ≤ r := by
  change ‖star (A j i)-star (B j i)‖ ≤ r
  rw [← star_sub, norm_star]
  exact h j i

theorem four_product (A B C D E F G H : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hA : ∀ i j, ‖A i j-E i j‖ ≤ r) (hB : ∀ i j, ‖B i j-F i j‖ ≤ r)
    (hC : ∀ i j, ‖C i j-G i j‖ ≤ r) (hD : ∀ i j, ‖D i j-H i j‖ ≤ r)
    (i j : d) : ‖(A*B*C⁻¹*D⁻¹) i j-(E*F*G⁻¹*H⁻¹) i j‖ ≤
      4*(Fintype.card d : ℝ)^2*r := by
  have hab := pair_product A B E F r r hA hB
  have hcd := pair_product C⁻¹ D⁻¹ G⁻¹ H⁻¹ r r (inverse_pair C G r hC) (inverse_pair D H r hD)
  have hh := pair_product (A*B) (C⁻¹*D⁻¹) (E*F) (G⁻¹*H⁻¹)
    ((Fintype.card d : ℝ)*(r+r)) ((Fintype.card d : ℝ)*(r+r)) hab hcd i j
  simp only [← mul_assoc] at hh
  convert hh using 1 <;> ring

theorem four_trace (A B C D E F G H : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hA : ∀ i j, ‖A i j-E i j‖ ≤ r) (hB : ∀ i j, ‖B i j-F i j‖ ≤ r)
    (hC : ∀ i j, ‖C i j-G i j‖ ≤ r) (hD : ∀ i j, ‖D i j-H i j‖ ≤ r) :
    |(trace ((A*B*C⁻¹*D⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)).re-
      (trace ((E*F*G⁻¹*H⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)).re| ≤
      4*(Fintype.card d : ℝ)^3*r := by
  have hh := UnitaryHaarCaps.trace_difference_bound d (A*B*C⁻¹*D⁻¹) (E*F*G⁻¹*H⁻¹)
    (4*(Fintype.card d : ℝ)^2*r) (four_product A B C D E F G H r hA hB hC hD)
  have he := (Complex.abs_re_le_norm (trace ((A*B*C⁻¹*D⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)-
    trace ((E*F*G⁻¹*H⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ))).trans hh
  convert he using 1 <;> ring

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]

theorem action_lipschitz (ρ : G →* Matrix.unitaryGroup d ℂ)
    (β c : ℝ) (x : Vertex n) (μ : Fin 4) (U W : Configuration (Vertex n) G)
    (hUW : ∀ e : Edge (Vertex n), e ≠ selectedLink n x μ → U e = W e)
    (r : ℝ) (hr : 0 ≤ r)
    (hselected : ∀ i j, ‖ρ (U (selectedLink n x μ)) i j-ρ (W (selectedLink n x μ)) i j‖ ≤ r) :
    |orientedWilsonAction (Vertex n) G (unitaryCharacter ρ) (base n) (loops n) β c U -
      orientedWilsonAction (Vertex n) G (unitaryCharacter ρ) (base n) (loops n) β c W| ≤
        24*(Fintype.card d : ℝ)^3*|β| * r := by
  classical
  have hentry (e : Edge (Vertex n)) (i j : d) : ‖ρ (W e) i j-ρ (U e) i j‖ ≤ r := by
    by_cases he : e = selectedLink n x μ
    · subst e
      rw [norm_sub_rev]
      exact hselected i j
    · rw [hUW e he, sub_self, norm_zero]
      exact hr
  let diff : PlaquetteIndex n → ℝ := fun p =>
    (loopObservable (Vertex n) G (unitaryCharacter ρ) (loops n p) W).re -
      (loopObservable (Vertex n) G (unitaryCharacter ρ) (loops n p) U).re
  have he : orientedWilsonAction (Vertex n) G (unitaryCharacter ρ) (base n) (loops n) β c U -
      orientedWilsonAction (Vertex n) G (unitaryCharacter ρ) (base n) (loops n) β c W = β*∑ p, diff p := by
    unfold orientedWilsonAction wilsonAction
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    change (c-_) - (c-_) = _-_
    dsimp only [loopObservable]
    ring
  have hd0 (p : PlaquetteIndex n) (hp : p ∉ affected n x μ) : diff p = 0 := by
    have hh := plaquette_unchanged n G x μ p hp U W hUW
    change (unitaryCharacter ρ _).re - (unitaryCharacter ρ _).re = 0
    rw [← hh]
    exact sub_self _
  have hs : (∑ p, diff p) = ∑ p ∈ affected n x μ, diff p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hd0 p hp)
  have hd (p : PlaquetteIndex n) : |diff p| ≤ 4*(Fintype.card d : ℝ)^3*r := by
    dsimp only [diff, loopObservable, unitaryCharacter]
    simp only [wilson, unitaryCharacter, loops, plaquette, holonomy, link, orientedExtension, base, one_mul, map_mul, map_inv]
    exact four_trace _ _ _ _ _ _ _ _ r (hentry _) (hentry _) (hentry _) (hentry _)
  have hsum : |∑ p ∈ affected n x μ, diff p| ≤ 24*(Fintype.card d : ℝ)^3*r := by
    calc
      _ ≤ ∑ p ∈ affected n x μ, |diff p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ affected n x μ, 4*(Fintype.card d : ℝ)^3*r :=
        Finset.sum_le_sum (fun p _ => hd p)
      _ = ((affected n x μ).card : ℝ)*(4*(Fintype.card d : ℝ)^3*r) := by simp
      _ ≤ _ := by
        have hc : ((affected n x μ).card : ℝ) ≤ 6 := by exact_mod_cast affected_card n x μ
        have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ 4*(Fintype.card d : ℝ)^3*r by positivity)
        nlinarith
  rw [he, abs_mul, hs]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.SingleLinkWilsonLipschitz
