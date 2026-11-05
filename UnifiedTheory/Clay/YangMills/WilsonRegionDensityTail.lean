/- Regional exponential remainder-density bounds under the actual Wilson law.
The conditional estimate is uniform in all exterior configurations and keeps
the regional boundary cost. No independence or small boundary is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonRegionPartition
import UnifiedTheory.Clay.YangMills.GibbsConditionalLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRegionDensityTail
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks WilsonBlockMarginal WilsonEnergyDensity SU2StarEnergy
open WilsonRegionEnergy WilsonRegionPartition WilsonRemainderDensity
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def rate (B : Finset (Edge (Vertex n))) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  Real.sqrt β / 2 * ∑ e ∈ B, fractionalRemainder n (edgeCoord n e).1 (edgeCoord n e).2 β U

theorem rate_continuous (B : Finset (Edge (Vertex n))) (β : ℝ) : Continuous (rate n B β) :=
  continuous_const.mul (continuous_finset_sum _
    (fun e _ => fractionalRemainder_continuous n (edgeCoord n e).1 (edgeCoord n e).2 β))

omit [NeZero n] in
theorem rate_eq_density (B : Finset (Edge (Vertex n))) (β : ℝ)
    (U : Configuration (Vertex n) Q) :
    rate n B β U = Real.sqrt β / 2 * B.card * WilsonRegionEnergy.density n B β U := by
  by_cases hB : B.Nonempty
  · have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
    unfold rate WilsonRegionEnergy.density
    field_simp
  · simp [Finset.not_nonempty_iff_eq_empty.mp hB, rate, WilsonRegionEnergy.density]

variable [Fact (1 < n)]

theorem rate_energy_bound (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 < β)
    (U : Configuration (Vertex n) Q) : rate n B β U ≤ β * energy n B U := by
  have h := mul_le_mul_of_nonneg_left (WilsonRegionEnergy.density_energy_bound n B β hβ U)
    (show 0 ≤ Real.sqrt β / 2 by positivity)
  rw [rate_eq_density]
  ring_nf at h
  rw [Real.sq_sqrt hβ.le] at h
  nlinarith

/-- A normalized exponential moment bound under every genuine fixed-exterior conditional law. -/
theorem fiber_exponential_bound (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 < β)
    (K : ℕ) (hK : 0 < K) (r : Outside (G := Q) B) :
    (∫ v, Real.exp (rate n B β (assemble B (r,v))) ∂fiberLaw n B β r) ≤
      Real.exp (cost n B β K) := by
  let A := fun v : Inside (G := Q) B => β * energy n B (assemble B (r,v))
  have hA : Continuous A := continuous_const.mul ((energy_continuous n B).comp
    ((assemble_continuous B).comp (continuous_const.prodMk continuous_id)))
  rw [fiberLaw_local]
  letI := CompactGibbsContinuity.law_probability (insideMeasure B (compactHaar Q)) A hA
  calc
    _ ≤ ∫ v, Real.exp (A v) ∂CompactGibbsContinuity.law (insideMeasure B (compactHaar Q)) A := by
      apply integral_mono
        ((Real.continuous_exp.comp ((rate_continuous n B β).comp
          ((assemble_continuous B).comp (continuous_const.prodMk continuous_id))))
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        ((Real.continuous_exp.comp hA).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      intro v
      exact Real.exp_le_exp.mpr (rate_energy_bound n B β hβ _)
    _ = 1 / (∫ v, Real.exp (-A v) ∂insideMeasure B (compactHaar Q)) :=
      GibbsFreeEnergyBound.reciprocal_partition_identity _ A hA
    _ ≤ 1 / Real.exp (-cost n B β K) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _)
        (WilsonRegionPartition.partition_lower n B β hβ.le K hK r)
    _ = _ := by rw [Real.exp_neg]; simp

/-- Averaging over the true interacting exterior loses no volume factor. -/
theorem exponential_bound (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 < β)
    (K : ℕ) (hK : 0 < K) :
    (∫ U, Real.exp (rate n B β U) ∂wilsonLaw n Q character β 2) ≤
      Real.exp (cost n B β K) := by
  rw [wilson_integral_split n Q character character_continuous β 2 B]
  have h := GibbsConditionalLower.expectation_lower (insideMeasure B (compactHaar Q))
    (outsideMeasure B (compactHaar Q)) (splitAction n Q character β 2 B)
    (splitAction_continuous n Q character character_continuous β 2 B)
    (fun z => -Real.exp (rate n B β (assemble B z)))
    ((Real.continuous_exp.comp ((rate_continuous n B β).comp (assemble_continuous B))).neg)
    (-Real.exp (cost n B β K)) (by
      intro r
      rw [integral_neg]
      exact neg_le_neg (fiber_exponential_bound n B β hβ K hK r))
  rw [integral_neg] at h
  linarith

/-- Any event with a regional energy-exponential threshold has a local normalization bound. -/
theorem event_bound (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 < β)
    (K : ℕ) (hK : 0 < K) (E : Set (Configuration (Vertex n) Q)) (T : ℝ)
    (hE : ∀ U ∈ E, T ≤ rate n B β U) :
    (wilsonLaw n Q character β 2).real E ≤ Real.exp (cost n B β K - T) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hs : E ⊆ {U | Real.exp T ≤ Real.exp (rate n B β U)} :=
    fun U hU => Real.exp_le_exp.mpr (hE U hU)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun U => (Real.exp_pos (rate n B β U)).le))
    ((Real.continuous_exp.comp (rate_continuous n B β)).integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _)) (Real.exp T)
  have h := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := wilsonLaw n Q character β 2) hs)
    (Real.exp_pos T).le).trans (hm.trans (exponential_bound n B β hβ K hK))
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos T)).mpr
  simpa only [mul_comm] using h

def level (B : Finset (Edge (Vertex n))) (β : ℝ) : ℝ :=
  (2 / 3) * envelope β + 8 * Real.sqrt β * ((boundary n B).card / (B.card : ℝ)) +
    2 / Real.sqrt β

def budget (B : Finset (Edge (Vertex n))) (β : ℝ) : ℝ :=
  6 * β * energyEnvelope β * B.card + 4 * β * (boundary n B).card + B.card

def bad (B : Finset (Edge (Vertex n))) (β : ℝ) : Set (Configuration (Vertex n) Q) :=
  {U | level n B β ≤ WilsonRegionEnergy.density n B β U}

omit [Fact (1 < n)] in
theorem bad_measurable (B : Finset (Edge (Vertex n))) (β : ℝ) : MeasurableSet (bad n B β) :=
  (isClosed_le continuous_const (WilsonRegionEnergy.density_continuous n B β)).measurableSet

omit [NeZero n] [Fact (1 < n)] in
theorem bad_rate (B : Finset (Edge (Vertex n))) (hB : B.Nonempty) (β : ℝ) (hβ : 0 < β)
    (U : Configuration (Vertex n) Q) (hU : U ∈ bad n B β) :
    budget n B β ≤ rate n B β U := by
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hs := (Real.sqrt_pos.mpr hβ).ne'
  have he : Real.sqrt β / 2 * B.card * level n B β = budget n B β := by
    calc
      _ = 6 * (Real.sqrt β) ^ 2 * energyEnvelope β * B.card +
          4 * (Real.sqrt β) ^ 2 * (boundary n B).card + B.card := by
        unfold level envelope
        field_simp
        ring
      _ = _ := by rw [Real.sq_sqrt hβ.le]; rfl
  rw [← he, rate_eq_density]
  exact mul_le_mul_of_nonneg_left hU (by positivity)

theorem bad_probability_bound (B : Finset (Edge (Vertex n))) (hB : B.Nonempty)
    (β : ℝ) (hβ : 0 < β) :
    (wilsonLaw n Q character β 2).real (bad n B β) ≤ Real.exp (-(B.card : ℝ)) := by
  apply (event_bound n B β hβ (grid β) (grid_pos β) (bad n B β) (budget n B β)
    (bad_rate n B hB β hβ)).trans
  apply Real.exp_le_exp.mpr
  have h := cost_grid_bound n B β hβ
  unfold budget
  linarith

def commonLevel (β : ℝ) : ℝ := (2 / 3) * envelope β + 10 / Real.sqrt β

omit [NeZero n] [Fact (1 < n)] in
theorem commonLevel_tendsto : Tendsto commonLevel atTop (𝓝 0) := by
  have hi := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul (10 : ℝ)
  simpa only [commonLevel, div_eq_mul_inv, mul_zero, add_zero] using
    (envelope_tendsto.const_mul (2 / 3 : ℝ)).add hi

omit [NeZero n] [Fact (1 < n)] in
/-- A purely geometric surface condition suffices for a common vanishing threshold. -/
theorem level_le_common (B : Finset (Edge (Vertex n))) (hB : B.Nonempty)
    (β : ℝ) (hβ : 0 < β) (hsurface : β * (boundary n B).card ≤ B.card) :
    level n B β ≤ commonLevel β := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hs := Real.sqrt_pos.mpr hβ
  have hd : ((boundary n B).card : ℝ) / B.card ≤ 1 / β := by
    apply (div_le_div_iff₀ hc hβ).mpr
    nlinarith
  have he : Real.sqrt β * (1 / β) = 1 / Real.sqrt β := by
    apply (eq_div_iff hs.ne').mpr
    calc
      _ = (Real.sqrt β) ^ 2 / β := by ring
      _ = 1 := by rw [Real.sq_sqrt hβ.le, div_self hβ.ne']
  have h := mul_le_mul_of_nonneg_left hd hs.le
  rw [he] at h
  unfold level commonLevel
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

omit [NeZero n] [Fact (1 < n)] in
/-- A vanishing boundary-to-volume cost gives a vanishing regional density threshold. -/
theorem level_tendsto {ι : Type*} {l : Filter ι} (N : ι → ℕ) [∀ i, NeZero (N i)]
    (B : ∀ i, Finset (Edge (Vertex (N i)))) (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (hboundary : Tendsto (fun i => Real.sqrt (β i) *
      ((boundary (N i) (B i)).card / ((B i).card : ℝ))) l (𝓝 0)) :
    Tendsto (fun i => level (N i) (B i) (β i)) l (𝓝 0) := by
  have hq := (envelope_tendsto.comp hβ).const_mul (2 / 3 : ℝ)
  have hi := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hβ)).const_mul (2 : ℝ)
  simpa only [level, div_eq_mul_inv, mul_assoc, mul_zero, add_zero] using
    (hq.add (hboundary.const_mul 8)).add hi

end
end UnifiedTheory.Clay.YangMills.WilsonRegionDensityTail
