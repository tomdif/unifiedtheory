/- A fixed genuine Schwartz test detects extensive ultraviolet conditional
noise in the actual Wilson law. Identity subtraction cannot remove this
second-moment lower bound. This module keeps lattice volume explicit; it does
not claim divergence on every infinite-volume regulator sequence. -/
import UnifiedTheory.Clay.YangMills.WilsonIndependentVariance
import UnifiedTheory.Clay.YangMills.SU2PositiveSourceFloor
import UnifiedTheory.Clay.YangMills.WilsonCellWeightLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSmoothSourceObstruction
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 LocalFields WilsonIndependentBlocks
open WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- The actual second moment, allowing any real multiplicative scale and identity subtraction. -/
def secondMoment (β Z c : ℝ) (w : PlaquetteIndex n → ℝ) : ℝ :=
  ∫ U, (Z * WilsonBlockIntegration.source n Q character 2 w U - c)^2
    ∂wilsonLaw n Q character β 2

/-- The proved one-link floor adds over all actual links. -/
theorem annealed_sum_lower (β : ℝ) (w : PlaquetteIndex n → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    (∑ e : Link n, (WilsonCellWeightLower.linkWeight n w e)^2) / (384 * β^2) ≤
      ∑ e : Link n, ∫ U, SU2AnnealedVariance.originalVariance n e.1 e.2 β w U
        ∂wilsonLaw n Q character β 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Link n)))
    (fun e _ => SU2PositiveSourceFloor.annealed_variance_lower n e.1 e.2 β w hw hβ henergy)
  rw [← Finset.sum_div] at h
  exact h

/-- A uniform polynomial conditional floor and exact independent-block
noise combine into an actual lower bound. All analytic inputs are proved. -/
theorem positive_weights_lower (β Z c : ℝ) (w : PlaquetteIndex n → ℝ)
    (hw : ∀ p, 0 ≤ w p) (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    Z^2 * (∑ p, w p)^2 / (768 * (n : ℝ)^4 * β^2) ≤
      secondMoment n β Z c w := by
  have hweight := WilsonCellWeightLower.linkWeight_square_lower n w
  have hnoise := annealed_sum_lower n β w hw hβ henergy
  have htotal := WilsonIndependentVariance.renormalized_second_moment_lower n β Z c w heven
  have hden : 0 ≤ 384 * β^2 := by positivity
  calc
    _ = (Z^2 / 8) * ((4 * (∑ p, w p)^2 / (n : ℝ)^4) / (384 * β^2)) := by ring
    _ ≤ (Z^2 / 8) * ((∑ e : Link n, (WilsonCellWeightLower.linkWeight n w e)^2) /
        (384 * β^2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hweight hden) (by positivity)
    _ ≤ (Z^2 / 8) * (∑ e : Link n,
        ∫ U, SU2AnnealedVariance.originalVariance n e.1 e.2 β w U
          ∂wilsonLaw n Q character β 2) :=
      mul_le_mul_of_nonneg_left hnoise (by positivity)
    _ ≤ secondMoment n β Z c w := by
      change Z^2 * (∑ e : Link n,
        ∫ U, SU2AnnealedVariance.originalVariance n e.1 e.2 β w U
          ∂wilsonLaw n Q character β 2) ≤ 8 * secondMoment n β Z c w at htotal
      linarith

/-- The test is fixed in physical spacetime. Its actual periodic cell integrals
supply the source coefficients and their exact mass, with no cell-counting hypothesis. -/
theorem physical_test_lower (β a Z c : ℝ) (plane : Plane) (f : TestFunction)
    (hf : ∀ x, 0 ≤ (f x).re) (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    Z^2 * ((∫ x, f x).re)^2 / (768 * (n : ℝ)^4 * β^2) ≤
      secondMoment n β Z c (WilsonPhysicalCellWeights.weight n a plane f) := by
  have h := positive_weights_lower n β Z c (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonCellWeightLower.weight_nonneg n a plane f hf) heven hβ henergy
  rw [WilsonPhysicalCellWeights.weight_sum] at h
  exact h

/-- One explicit normalized nonnegative real Schwartz test discharges all
existence, positivity and nonzero-mass premises, at every regulator. -/
theorem witness_lower (β a Z c : ℝ) (plane : Plane) (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    Z^2 / (768 * (n : ℝ)^4 * β^2) ≤
      secondMoment n β Z c
        (WilsonPhysicalCellWeights.weight n a plane WilsonCellWeightLower.witnessTest) := by
  have h := physical_test_lower n β a Z c plane WilsonCellWeightLower.witnessTest
    WilsonCellWeightLower.witnessTest_nonneg heven hβ henergy
  simpa only [WilsonCellWeightLower.witnessTest_integral, Complex.one_re, one_pow, mul_one] using h

/-- Classical dimension-four rescaling retains ultraviolet noise despite
arbitrary identity counterterms. The volume factor remains explicit. -/
theorem classical_witness_lower (β a c : ℝ) (plane : Plane)
    (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    (a^8)⁻¹ / (768 * (n : ℝ)^4 * β^2) ≤
      secondMoment n β (a^4)⁻¹ c
        (WilsonPhysicalCellWeights.weight n a plane WilsonCellWeightLower.witnessTest) := by
  have h := witness_lower n β a (a^4)⁻¹ c plane heven hβ henergy
  simpa only [← inv_pow, ← pow_mul] using h

end
end UnifiedTheory.Clay.YangMills.WilsonSmoothSourceObstruction
