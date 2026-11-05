/- Actual reflection copies at every affine spatial frame. Deletion sets,
operator norms and exact deletion counts are transported together. -/
import UnifiedTheory.Clay.YangMills.WilsonProfileNormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonFramedDeletion
noncomputable section
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights SpatialWilsonColumnTransfer
open WilsonPlaquetteFrames WilsonProfileTransport WilsonProfileNormTransport

variable (n : ℕ) [NeZero n]

def positiveSet (F : Frame n) (S : Finset (Plaquette n)) : Finset (Plaquette n) :=
  pushSet n (inverse n F) (WilsonDeletionReflection.positiveSet n (pushSet n F S))

def negativeSet (F : Frame n) (S : Finset (Plaquette n)) : Finset (Plaquette n) :=
  pushSet n (inverse n F) (WilsonDeletionReflection.negativeSet n (pushSet n F S))

theorem positiveSet_mem (F : Frame n) (S : Finset (Plaquette n)) (p : Plaquette n) :
    p ∈ positiveSet n F S ↔
      F.plaquettes.symm (WilsonDeletionReflection.positiveIndex n (F.plaquettes p)) ∈ S := by
  simp only [positiveSet, pushSet_mem, WilsonDeletionReflection.positiveSet_mem,
    inverse, Equiv.symm_symm]

theorem negativeSet_mem (F : Frame n) (S : Finset (Plaquette n)) (p : Plaquette n) :
    p ∈ negativeSet n F S ↔
      F.plaquettes.symm (WilsonDeletionReflection.negativeIndex n (F.plaquettes p)) ∈ S := by
  simp only [negativeSet, pushSet_mem, WilsonDeletionReflection.negativeSet_mem,
    inverse, Equiv.symm_symm]

theorem copies_card (F : Frame n) (S : Finset (Plaquette n)) :
    (positiveSet n F S).card + (negativeSet n F S).card = 2 * S.card := by
  simp only [positiveSet, negativeSet, pushSet_card, WilsonDeletionReflection.copies_card]

theorem norm_schwarz (F : Frame n) (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n (omitted n S s) β‖^2 ≤
      ‖transfer n (omitted n (positiveSet n F S) s) β‖ *
      ‖transfer n (omitted n (negativeSet n F S) s) β‖ := by
  have h := WilsonDeletionReflection.deletion_norm_schwarz n (pushSet n F S) s hs β hβ
  simpa only [positiveSet, negativeSet, norm_pushSet n _ _ _ β hβ] using h

def priced (S : Finset (Plaquette n)) (s β a : ℝ) : ℝ :=
  ‖transfer n (omitted n S s) β‖ * Real.exp (-a * ((S.card : ℝ) * s))

theorem priced_nonneg (S : Finset (Plaquette n)) (s β a : ℝ) :
    0 ≤ priced n S s β a := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem priced_schwarz (F : Frame n) (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) :
    (priced n S s β a)^2 ≤ priced n (positiveSet n F S) s β a *
      priced n (negativeSet n F S) s β a := by
  have h := SpatialWilsonNormSchwarz.priced_schwarz n
    (omitted n (pushSet n F S) s) (omitted_nonneg n _ s hs) β hβ s a
  rw [WilsonDeletionReflection.copyPositive_omitted,
    WilsonDeletionReflection.copyNegative_omitted] at h
  simp only [SpatialWilsonNormSchwarz.pricedNorm, WilsonDeletionReflection.deficit_card,
    norm_pushSet n _ _ _ β hβ, pushSet_card] at h
  simpa only [priced, positiveSet, negativeSet, norm_pushSet n _ _ _ β hβ, pushSet_card] using h

/-- The choice is valid at every translated/oriented cut, with the same
coupling and count price. Geometric progress of a chosen sequence is separate. -/
theorem priced_choice (F : Frame n) (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) :
    priced n S s β a ≤ priced n (positiveSet n F S) s β a ∨
      priced n S s β a ≤ priced n (negativeSet n F S) s β a := by
  have h := WilsonDeletionReflection.deletion_priced_choice n (pushSet n F S) s hs β hβ a
  simpa only [priced, positiveSet, negativeSet, norm_pushSet n _ _ _ β hβ, pushSet_card] using h

end
end UnifiedTheory.Clay.YangMills.WilsonFramedDeletion
