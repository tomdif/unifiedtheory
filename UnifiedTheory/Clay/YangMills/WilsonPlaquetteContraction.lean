/- The actual transfer contracts any source supported in the union of bad
spatial plaquettes, with rate equal to the explicit sum of one-plaquette
rates. This supplies coercivity on that subspace, not on the retained fields. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteCover
import UnifiedTheory.Clay.YangMills.WilsonCoverContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteContraction
noncomputable section
open WilsonSlabOperator WilsonPhysicalVariance WilsonHighFieldDecay SpatialPlaquetteCutGeometry
open WilsonPlaquetteCover WilsonCoverContraction
open WilsonPlaquetteColumnTail (rate)

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

/-- Unlike residual splitting, duality gives the full rate for a source
supported in the union, even when its mass is spread over many bad regions. -/
theorem union_decay (β : ℝ) (hβ : 3 / 4 ≤ β) (q : I → Plaquette n)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ bad n q R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (∑ i, rate β (R i)) * mass (2 * n) β (by linarith) f := by
  apply cover_decay (2 * n) β (by linarith) (cover n q R)
    (CompactCutoffCover.sum_square_le _) (fun i => rate β (R i))
    (fun i => WilsonPlaquetteColumnTail.rate_nonneg β (R i))
    (joint_output n β hβ q R hR) f
  ext u
  by_cases hu : u ∈ bad n q R
  · simp only [ContinuousMap.mul_apply, total_apply, cover_one n q R hR u hu, one_mul]
  · simp only [ContinuousMap.mul_apply, hs u hu, mul_zero]

/-- This is a proved lower bound on the bad-region subspace. Its useful range
is precisely where the stated sum of rates is smaller than one. -/
theorem union_loss (β : ℝ) (hβ : 3 / 4 ≤ β) (q : I → Plaquette n)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ bad n q R → f u = 0) :
    (1 - ∑ i, rate β (R i)) * mass (2 * n) β (by linarith) f ≤
      loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have h := union_decay n β hβ q R hR f hs
  linarith

/-- All spatial plaquettes share this actual supported-source contraction. -/
theorem all_plaquettes_decay (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ allBad n R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (3 * (2 * n : ℝ) ^ 3) * rate β R * mass (2 * n) β (by linarith) f := by
  have h := union_decay n β hβ (fun q : Plaquette n => q) (fun _ => R) (fun _ => hR) f hs
  simpa only [Finset.sum_const, Finset.card_univ, plaquette_card, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

theorem all_plaquettes_loss (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ allBad n R → f u = 0) :
    (1 - (3 * (2 * n : ℝ) ^ 3) * rate β R) * mass (2 * n) β (by linarith) f ≤
      loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have h := all_plaquettes_decay n β hβ R hR f hs
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteContraction
