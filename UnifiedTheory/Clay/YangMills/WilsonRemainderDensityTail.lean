/- Exponential volume suppression of large average positive star remainder
under the actual Wilson law. This controls a high-density sector; it does
not control sparse bad clusters or prove convergence of the complementary
small-density sector. -/
import UnifiedTheory.Clay.YangMills.WilsonJointBadStarTail
import UnifiedTheory.Clay.YangMills.WilsonCellWeightLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRemainderDensityTail
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks SingleLinkWilsonOscillation SU2StarEnergy WilsonEnergyDensity
open WilsonRemainderDensity WilsonJointBadStarTail
open scoped Topology

/-- An explicit density threshold that shrinks to zero while paying the normalization cost. -/
def vanishingLevel (β : ℝ) : ℝ := envelope β / 3 + (Real.sqrt β)⁻¹

theorem vanishingLevel_tendsto : Tendsto vanishingLevel atTop (𝓝 0) := by
  simpa only [vanishingLevel, add_zero, div_zero, zero_div] using
    (envelope_tendsto.div_const 3).add (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)

theorem vanishingLevel_envelope (β : ℝ) (hβ : 0 < β) : envelope β ≤ 3 * vanishingLevel β := by
  have h : 0 ≤ (Real.sqrt β)⁻¹ := by positivity
  unfold vanishingLevel
  linarith

theorem vanishingLevel_rate (β : ℝ) (hβ : 0 < β) : 1 ≤ Real.sqrt β * vanishingLevel β := by
  unfold vanishingLevel
  rw [mul_add, mul_inv_cancel₀ (Real.sqrt_pos.mpr hβ).ne']
  have h : 0 ≤ Real.sqrt β * (envelope β / 3) :=
    mul_nonneg (Real.sqrt_nonneg β) (div_nonneg (envelope_nonneg β hβ) (by norm_num))
  linarith

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- Exact counting for the actual star energies, including period two. -/
theorem sum_starEnergy (U : Configuration (Vertex n) Q) :
    (∑ e : Link n, starEnergy n e.1 e.2 U) =
      24 * (Fintype.card (Vertex n) : ℝ) * energyDensity n U := by
  have h := WilsonCellWeightLower.sum_linkWeight n (plaquetteTerm n Q character 2 U)
  change (∑ e : Link n, starEnergy n e.1 e.2 U) = 4 * ∑ p, _ at h
  rw [h, energyDensity_eq]
  field_simp
  ring

/-- The all-link average costs energy without any independence assumption. -/
theorem density_energy_bound (β : ℝ) (hβ : 0 < β)
    (U : Configuration (Vertex n) Q) :
    density n Finset.univ β U ≤ 3 * Real.sqrt β * energyDensity n U := by
  have hc : (Fintype.card (Link n) : ℝ) = 4 * (Fintype.card (Vertex n) : ℝ) := by
    simp [Link, Fintype.card_prod, mul_comm]
  unfold density
  rw [Finset.card_univ, hc]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (Fintype.card (Vertex n) : ℝ))).mpr
  calc
    _ ≤ ∑ e : Link n, Real.sqrt β / 2 * starEnergy n e.1 e.2 U :=
      Finset.sum_le_sum (fun e _ => fractionalRemainder_energy_bound n e.1 e.2 β hβ U)
    _ = _ := by rw [← Finset.mul_sum, sum_starEnergy]; ring

/-- Configurations whose spatial mean square-root remainder exceeds a fixed level. -/
def largeDensity (β t : ℝ) : Set (Configuration (Vertex n) Q) :=
  {U | t ≤ density n Finset.univ β U}

omit [Fact (1 < n)] in
theorem largeDensity_measurable (β t : ℝ) : MeasurableSet (largeDensity n β t) :=
  isClosed_le continuous_const (density_continuous n Finset.univ β) |>.measurableSet

theorem largeDensity_action (β t : ℝ) (hβ : 0 < β)
    (U : Configuration (Vertex n) Q) (hU : U ∈ largeDensity n β t) :
    2 * Real.sqrt β * t * (Fintype.card (Vertex n) : ℝ) ≤ action n β U := by
  have h := mul_le_mul_of_nonneg_left
    ((show t ≤ density n Finset.univ β U from hU).trans (density_energy_bound n β hβ U))
    (show 0 ≤ 2 * Real.sqrt β * (Fintype.card (Vertex n) : ℝ) by positivity)
  unfold action
  ring_nf at h
  rw [Real.sq_sqrt hβ.le] at h
  nlinarith

/-- A genuine Wilson probability estimate with its explicit normalization cost. -/
theorem largeDensity_probability_grid (β t : ℝ) (hβ : 0 < β) :
    (wilsonLaw n Q character β 2).real (largeDensity n β t) ≤
      Real.exp ((6 * β * energyEnvelope β - 2 * Real.sqrt β * t) *
        (Fintype.card (Vertex n) : ℝ)) := by
  have hb : (wilsonLaw n Q character β 2).real (largeDensity n β t) ≤
      Real.exp ((Fintype.card (Vertex n) : ℝ) * entropyCost β (grid β) -
        2 * Real.sqrt β * t * (Fintype.card (Vertex n) : ℝ)) := by
    rw [← law_identification]
    apply gibbs_event_bound (referenceMeasure Q (Vertex n)) (action n β)
      (action_continuous n β) (largeDensity n β t) _ _
      (largeDensity_action n β t hβ)
    simpa only [neg_mul] using partition_lower n β hβ.le
      (grid β) (grid_pos β)
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (entropyCost_grid_le β hβ)
    (Nat.cast_nonneg (Fintype.card (Vertex n)) : (0 : ℝ) ≤ _)
  nlinarith

/-- Once the explicit envelope is small, suppression is exponential in full volume. -/
theorem largeDensity_probability_bound (β t : ℝ) (hβ : 0 < β)
    (hsmall : envelope β ≤ 3 * t) :
    (wilsonLaw n Q character β 2).real (largeDensity n β t) ≤
      Real.exp (-Real.sqrt β * t * (Fintype.card (Vertex n) : ℝ)) := by
  apply (largeDensity_probability_grid n β t hβ).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg β)
  have hs : 6 * β * energyEnvelope β ≤ Real.sqrt β * t := by
    dsimp only [envelope] at h
    ring_nf at h
    rw [Real.sq_sqrt hβ.le] at h
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hs
    (Nat.cast_nonneg (Fintype.card (Vertex n)) : (0 : ℝ) ≤ _)]

omit [Fact (1 < n)] in
theorem badFraction_subset (β ε η : ℝ) :
    {U | η ≤ badFraction n Finset.univ β ε U} ⊆
      largeDensity n β (Real.sqrt ε * η) := by
  intro U hU
  exact (mul_le_mul_of_nonneg_left hU (Real.sqrt_nonneg ε)).trans
    (badFraction_le_density n Finset.univ β ε U)

/-- A positive fraction of large exact remainders is exponentially rare. -/
theorem badFraction_probability_exponential (β ε η : ℝ) (hβ : 0 < β)
    (hsmall : envelope β ≤ 3 * (Real.sqrt ε * η)) :
    (wilsonLaw n Q character β 2).real {U | η ≤ badFraction n Finset.univ β ε U} ≤
      Real.exp (-Real.sqrt β * (Real.sqrt ε * η) * (Fintype.card (Vertex n) : ℝ)) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  exact (measureReal_mono (badFraction_subset n β ε η)).trans
    (largeDensity_probability_bound n β (Real.sqrt ε * η) hβ hsmall)

/-- Even a shrinking density threshold has exponential volume suppression. -/
theorem vanishingLevel_probability_bound (β : ℝ) (hβ : 0 < β) :
    (wilsonLaw n Q character β 2).real (largeDensity n β (vanishingLevel β)) ≤
      Real.exp (-(Fintype.card (Vertex n) : ℝ)) := by
  apply (largeDensity_probability_bound n β (vanishingLevel β) hβ
    (vanishingLevel_envelope β hβ)).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (vanishingLevel_rate β hβ)
    (Nat.cast_nonneg (Fintype.card (Vertex n)) : (0 : ℝ) ≤ _)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonRemainderDensityTail
