/- The finite block extremal theorem instantiated with actual six-plaquette
Wilson cell deletions. All score hypotheses are proved from the concrete
fine/coarse dictionaries, with no block reflection hypothesis left over. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeReflection
import UnifiedTheory.Clay.YangMills.WilsonCubeTransport
import UnifiedTheory.Clay.YangMills.BlockChessboardExtremum

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeChessboard
noncomputable section
open WilsonTimeSlab SpatialWilsonPatchWeights SpatialWilsonColumnTransfer
open WilsonCubeCells WilsonCubeReflection WilsonCubeTransport
open WilsonProfileTransport WilsonProfileNormTransport

variable (n : ℕ) [NeZero n]

def score (s β a : ℝ) (f : SpatialVertex (2 * n) → Bool) : ℝ :=
  WilsonFramedDeletion.priced (2 * n) (deleted (2 * n) f) s β a

theorem score_nonneg (s β a : ℝ) (f : SpatialVertex (2 * n) → Bool) : 0 ≤ score n s β a f :=
  WilsonFramedDeletion.priced_nonneg (2 * n) _ s β a

theorem score_affine (s β a : ℝ) (hβ : 0 ≤ β) (σ : Equiv.Perm (Fin 3))
    (t : SpatialVertex (2 * n)) (f : SpatialVertex (2 * n) → Bool) :
    score n s β a (BlockLabelSymmetry.pull n σ t f) = score n s β a f := by
  simp only [score, deleted_pull, WilsonFramedDeletion.priced,
    norm_pushSet (2 * n) _ _ _ β hβ, pushSet_card]

theorem score_schwarz (s : ℝ) (hs : 0 ≤ s) (β : ℝ) (hβ : 0 ≤ β) (a : ℝ)
    (f : SpatialVertex (2 * n) → Bool) :
    (score n s β a f)^2 ≤ score n s β a (BlockReflectionVariation.positiveCopy n f) *
      score n s β a (BlockReflectionVariation.negativeCopy n f) := by
  have h := SpatialWilsonNormSchwarz.priced_schwarz (2 * n)
    (omitted (2 * n) (deleted (2 * n) f) s) (omitted_nonneg _ _ s hs) β hβ s a
  rw [WilsonDeletionReflection.copyPositive_omitted,
    WilsonDeletionReflection.copyNegative_omitted, positive_deleted, negative_deleted] at h
  simpa only [score, WilsonFramedDeletion.priced, SpatialWilsonNormSchwarz.pricedNorm,
    WilsonDeletionReflection.deficit_card] using h

/-- An unconditional finite-regulator Wilson cell estimate: the priced
score is bounded by the actual empty and fully disseminated cell models. -/
theorem binary_bound (s : ℝ) (hs : 0 ≤ s) (β : ℝ) (hβ : 0 ≤ β) (a : ℝ)
    (f : SpatialVertex (2 * n) → Bool) :
    score n s β a f ≤ max (score n s β a (fun _ => false)) (score n s β a (fun _ => true)) :=
  BlockChessboardExtremum.binary_bound n (score n s β a) (score_nonneg n s β a)
    (score_affine n s β a hβ) (score_schwarz n s hs β hβ a) f

end
end UnifiedTheory.Clay.YangMills.WilsonCubeChessboard
