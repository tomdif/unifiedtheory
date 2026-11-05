/- Defect-count tails for arbitrary spatial regions, including full
three-dimensional regions. Only the literal binomial entropy is paid. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterCover
import UnifiedTheory.Clay.YangMills.WilsonPatchCountTail
import UnifiedTheory.Clay.YangMills.WilsonClusterActivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterCountTail
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry WilsonGroundSlabEnergy WilsonClusterSourceDecay
open WilsonPatchCountTail (event event_eq_union binomial_entropy)

variable (n : ℕ) [NeZero n]

/-- The source-sensitive bound uses the actual binomial number of candidates. -/
theorem binomial_tail (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R) (k : ℕ)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event (2 * n) A R k).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * (2 * n)) β hβ.le f := by
  have h := WilsonClusterCover.same_size_tail n β hβ (fun S : A.powersetCard k => S.val)
    k
    (fun S => (Finset.mem_powersetCard.mp S.property).2) R hmargin hR f
  rw [event_eq_union]
  simpa only [Fintype.card_coe, Finset.card_powersetCard] using h

theorem binomial_decay (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R) (k : ℕ)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hs : ∀ u, u ∉ event (2 * n) A R k → f u = 0) :
    mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * (2 * n)) β hβ.le f := by
  have h := WilsonClusterCover.union_decay n β hβ (fun S : A.powersetCard k => S.val)
    (fun _ => R) (fun _ => hmargin) (fun _ => hR) f (by simpa only [← event_eq_union] using hs)
  have he (S : A.powersetCard k) : S.val.card = k := (Finset.mem_powersetCard.mp S.property).2
  simpa only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_coe, Finset.card_powersetCard] using h
/-- At least k defects among at most b*k candidates have exponential mass error. -/
theorem density_tail (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R) (b k : ℕ)
    (hk : A.card ≤ b * k)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event (2 * n) A R k).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * ((2 : ℝ) ^ b * rate β R) ^ k * mass (2 * (2 * n)) β hβ.le f := by
  have ht := binomial_tail n A β hβ R hmargin hR k f
  have hb := mul_le_mul_of_nonneg_right (binomial_entropy A.card b k (rate β R)
    (rate_pos β R).le hk) (mass_nonneg (2 * (2 * n)) β hβ.le f)
  linarith

theorem density_loss (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R) (b k : ℕ)
    (hk : A.card ≤ b * k)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hs : ∀ u, u ∉ event (2 * n) A R k → f u = 0) :
    (1 - ((2 : ℝ) ^ b * rate β R) ^ k) * mass (2 * (2 * n)) β hβ.le f ≤
      loss (2 * (2 * n)) β hβ.le f := by
  rw [loss_mass]
  have ht := binomial_decay n A β hβ R hmargin hR k f hs
  have hb := mul_le_mul_of_nonneg_right (binomial_entropy A.card b k (rate β R)
    (rate_pos β R).le hk) (mass_nonneg (2 * (2 * n)) β hβ.le f)
  linarith


theorem weak_coupling_tail (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (b k : ℕ)
    (hk : A.card ≤ b * k)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event (2 * n) A (WilsonClusterActivity.threshold β) k).indicator
      (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * ((2 : ℝ) ^ b * (2 * β + 5)⁻¹) ^ k * mass (2 * (2 * n)) β hβ.le f := by
  have ht := density_tail n A β hβ (WilsonClusterActivity.threshold β)
    (WilsonClusterActivity.threshold_margin β hβ) 
    (WilsonClusterActivity.threshold_pos β hβ) b k hk f
  have hb := pow_le_pow_left₀
    (mul_nonneg (by positivity) (rate_pos β _).le)
    (mul_le_mul_of_nonneg_left (WilsonClusterActivity.rate_bound β hβ) (by positivity :
      0 ≤ (2 : ℝ) ^ b)) k
  have hc := mul_le_mul_of_nonneg_right hb (mass_nonneg (2 * (2 * n)) β hβ.le f)
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonClusterCountTail
