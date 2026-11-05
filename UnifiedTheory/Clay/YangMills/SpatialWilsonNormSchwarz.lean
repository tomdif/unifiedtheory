/- The spatial reflection inequality for actual compact Wilson transfer
norms, with all kinetic interactions and literal endpoint weights retained.
This is a one-cut theorem, not a completed multicut chessboard estimate. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonCutSchwarz
import UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer
import UnifiedTheory.Clay.YangMills.KernelEndpointNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonNormSchwarz
noncomputable section
open MeasureTheory WilsonTimeSlab SpatialPlaquetteCutGeometry
open SpatialWilsonColumnTransfer SpatialWilsonHalfCopies SpatialWilsonCutSchwarz
open FiniteKernelChain

variable (n : ℕ) [NeZero n]

theorem endpoint_nonneg (γ : Plaquette n → ℝ) (β : ℝ) (L : ℕ) :
    0 ≤ endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n γ β) L
      (boundary n γ) (boundary n γ) := by
  unfold endpoint
  apply integral_nonneg
  intro u
  exact mul_nonneg (mul_nonneg (boundary_pos n γ _).le
    (Finset.prod_nonneg (fun t _ => (kernelMap_pos n γ β _ _).le)))
    (boundary_pos n γ _).le

theorem endpoint_schwarz (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (β : ℝ) (hβ : 0 ≤ β) (L : ℕ) :
    (endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n γ β) L
      (boundary n γ) (boundary n γ)) ^ 2 ≤
      endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n (copyPositive n γ) β) L
        (boundary n (copyPositive n γ)) (boundary n (copyPositive n γ)) *
      endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n (copyNegative n γ) β) L
        (boundary n (copyNegative n γ)) (boundary n (copyNegative n γ)) := by
  rw [endpoint_density, endpoint_density, endpoint_density]
  exact partition_copies n (Fin (L + 1)) (fun _ => γ) (fun _ => hγ)
    (fun _ : Fin L => β) (fun _ => hβ) Fin.castSucc Fin.succ

/-- Arbitrary spatial plaquette profiles, including noncoplanar deletion
patterns, satisfy the exact reflection norm comparison. -/
theorem norm_schwarz (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n γ β‖^2 ≤ ‖transfer n (copyPositive n γ) β‖ *
      ‖transfer n (copyNegative n γ) β‖ := by
  obtain ⟨c,hc,hB⟩ := KernelPartitionNorm.positive_floor (boundary n γ) (boundary_pos n γ)
  exact KernelEndpointNorm.norm_schwarz (WilsonSlabOperator.measure (2 * n))
    (kernelMap n γ β) (kernelMap n (copyPositive n γ) β) (kernelMap n (copyNegative n γ) β)
    (transfer_positive n γ β hβ) (fun u v => (kernelMap_pos n γ β u v).le)
    (boundary n γ) (boundary n (copyPositive n γ)) (boundary n (copyNegative n γ))
    c hc hB (endpoint_nonneg n (copyNegative n γ) β) (endpoint_schwarz n γ hγ β hβ)

/-- An exponential price per unit of removed plaquette coupling. Its use is
algebraic here; no physical activity estimate is assumed or concluded. -/
def pricedNorm (γ : Plaquette n → ℝ) (β s a : ℝ) : ℝ :=
  ‖transfer n γ β‖ * Real.exp (-a * ∑ p, (s - γ p))

theorem pricedNorm_nonneg (γ : Plaquette n → ℝ) (β s a : ℝ) :
    0 ≤ pricedNorm n γ β s a := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem priced_schwarz (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (β : ℝ) (hβ : 0 ≤ β) (s a : ℝ) :
    (pricedNorm n γ β s a)^2 ≤
      pricedNorm n (copyPositive n γ) β s a * pricedNorm n (copyNegative n γ) β s a := by
  have he : (Real.exp (-a * ∑ p, (s - γ p)))^2 =
      Real.exp (-a * ∑ p, (s - copyPositive n γ p)) *
      Real.exp (-a * ∑ p, (s - copyNegative n γ p)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      _ = -a * (2 * ∑ p, (s - γ p)) := by ring
      _ = -a * ((∑ p, (s - copyPositive n γ p)) +
          (∑ p, (s - copyNegative n γ p))) := by rw [copies_deficit]
      _ = _ := by ring
  have h := mul_le_mul_of_nonneg_right (norm_schwarz n γ hγ β hβ)
    (sq_nonneg (Real.exp (-a * ∑ p, (s - γ p))))
  unfold pricedNorm
  rw [mul_pow, he]
  rw [he] at h
  convert h using 1; ring

/-- One reflection choice never decreases the priced norm. Choosing cuts
that terminate in a controlled disseminated pattern is still required. -/
theorem priced_choice (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (β : ℝ) (hβ : 0 ≤ β) (s a : ℝ) :
    pricedNorm n γ β s a ≤ pricedNorm n (copyPositive n γ) β s a ∨
      pricedNorm n γ β s a ≤ pricedNorm n (copyNegative n γ) β s a := by
  have h := priced_schwarz n γ hγ β hβ s a
  have hp := pricedNorm_nonneg n (copyPositive n γ) β s a
  have hm := pricedNorm_nonneg n (copyNegative n γ) β s a
  by_contra! hh
  have hz : 0 < pricedNorm n γ β s a := lt_of_le_of_lt hp hh.1
  have ht := (mul_le_mul_of_nonneg_right hh.1.le hm).trans_lt
    (mul_lt_mul_of_pos_left hh.2 hz)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonNormSchwarz
