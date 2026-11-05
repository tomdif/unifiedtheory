/- Reversibility converts a family of output estimates into sharp decay for
sources supported in its covered region. The bound uses the sum of the rates,
without the factor two from a residual splitting. -/
import UnifiedTheory.Clay.YangMills.WilsonCutoffCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCoverContraction
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath WilsonPhysicalVariance
open WilsonHighFieldDecay WilsonHighFieldReduction CompactDensityEntropy

variable (n : ℕ) [NeZero n]

/-- The reverse direction of cutoff duality: a source on which the cutoff is
one inherits the same rate as the localized output. -/
theorem supported_decay (β : ℝ) (hβ : 0 ≤ β) (χ : C(Slice n, ℝ)) (q : ℝ) (hq : 0 ≤ q)
    (hout : ∀ g, mass n β hβ (χ * step n β hβ g) ≤ q * mass n β hβ g)
    (f : C(Slice n, ℝ)) (hs : χ * f = f) :
    mass n β hβ (step n β hβ f) ≤ q * mass n β hβ f := by
  have hid : pairing n β hβ f (χ * step n β hβ (step n β hβ f)) =
      mass n β hβ (step n β hβ f) := by
    calc
      _ = pairing n β hβ (χ * f) (step n β hβ (step n β hβ f)) := by
        unfold pairing
        apply integral_congr_ae
        filter_upwards with u
        simp only [ContinuousMap.mul_apply]
        ring
      _ = _ := by rw [hs, pairing_step, pairing_self]
  have hc := pairing_sq n β hβ f (χ * step n β hβ (step n β hβ f))
  rw [hid] at hc
  have hh := hc.trans (mul_le_mul_of_nonneg_left (hout (step n β hβ f))
    (mass_nonneg n β hβ f))
  by_cases hz : mass n β hβ (step n β hβ f) = 0
  · rw [hz]
    exact mul_nonneg hq (mass_nonneg n β hβ f)
  · have hp : 0 < mass n β hβ (step n β hβ f) :=
      lt_of_le_of_ne (mass_nonneg n β hβ _) (Ne.symm hz)
    nlinarith

variable {I : Type*} [Fintype I]

def total (χ : I → C(Slice n, ℝ)) : C(Slice n, ℝ) := CompactCutoffCover.squareSum χ

omit [NeZero n] in
theorem total_apply (χ : I → C(Slice n, ℝ)) (u : Slice n) :
    total n χ u = ∑ i, (χ i u) ^ 2 := by
  simp only [total, CompactCutoffCover.squareSum, ContinuousMap.sum_apply, ContinuousMap.pow_apply]

omit [NeZero n] in
theorem total_range (χ : I → C(Slice n, ℝ)) (hχ : ∀ u, ∑ i, (χ i u) ^ 2 ≤ 1)
    (u : Slice n) : total n χ u ∈ Set.Icc 0 1 := by
  rw [total_apply]
  exact ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _), hχ u⟩

theorem total_mass_le (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (hχ : ∀ u, ∑ i, (χ i u) ^ 2 ≤ 1) (f : C(Slice n, ℝ)) :
    mass n β hβ (total n χ * f) ≤ ∑ i, mass n β hβ (χ i * f) := by
  letI := groundLaw_probability n β hβ
  rw [WilsonCutoffCover.sum_mass_integral]
  apply integral_mono
    (continuous_integrable (groundLaw n β hβ) _ ((total n χ * f).continuous.pow 2))
    (integrable_finset_sum _ (fun i _ =>
      continuous_integrable (groundLaw n β hβ) _ ((χ i * f).continuous.pow 2)))
  intro u
  simp only [ContinuousMap.mul_apply, mul_pow, ← Finset.sum_mul, ← total_apply]
  have hr := total_range n χ hχ u
  exact mul_le_mul_of_nonneg_right (by nlinarith [hr.1, hr.2] : (total n χ u) ^ 2 ≤ total n χ u)
    (sq_nonneg (f u))

/-- A square cover transfers the sum of its output rates to any covered source. -/
theorem cover_decay (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (hχ : ∀ u, ∑ i, (χ i u) ^ 2 ≤ 1) (q : I → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hout : ∀ g, (∑ i, mass n β hβ (χ i * step n β hβ g)) ≤
      (∑ i, q i) * mass n β hβ g)
    (f : C(Slice n, ℝ)) (hs : total n χ * f = f) :
    mass n β hβ (step n β hβ f) ≤ (∑ i, q i) * mass n β hβ f :=
  supported_decay n β hβ (total n χ) _ (Finset.sum_nonneg (fun i _ => hq i))
    (fun g => (total_mass_le n β hβ χ hχ (step n β hβ g)).trans (hout g)) f hs

end
end UnifiedTheory.Clay.YangMills.WilsonCoverContraction
