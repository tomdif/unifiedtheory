/- Positive source weights have a uniformly positive radial projection on the
actual six-staple good event. The subsequent bounds concern actual conditional
noise under the interacting Wilson measure, not separated correlations. -/
import UnifiedTheory.Clay.YangMills.SU2AnnealedVariance
import UnifiedTheory.Clay.YangMills.SU2RadialCovarianceLower

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2PositiveSourceFloor
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SingleLinkWilsonOscillation SU2AnnealedVariance
open scoped Quaternion RealInnerProductSpace BigOperators

/-- Each unit summand of six nearly aligned staples has positive radial projection. -/
theorem six_projection {ι : Type*} (s : Finset ι)
    (v : ι → ℍ) (hcard : s.card = 6) (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (i : ι) (hi : i ∈ s) :
    ‖∑ j ∈ s, v j‖ * (‖∑ j ∈ s, v j‖ - 5) ≤
      inner ℝ (∑ j ∈ s, v j) (v i) := by
  classical
  let A := ∑ j ∈ s, v j
  have hc : (s.erase i).card = 5 := by
    rw [Finset.card_erase_of_mem hi, hcard]
  have hs : (∑ j ∈ s.erase i, inner ℝ A (v j)) ≤ 5 * ‖A‖ := by
    calc
      _ ≤ ∑ _j ∈ s.erase i, ‖A‖ := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [hv j (Finset.mem_of_mem_erase hj), mul_one] using
          real_inner_le_norm A (v j)
      _ = _ := by simp [hc]
  have he : inner ℝ A (v i) + (∑ j ∈ s.erase i, inner ℝ A (v j)) = ‖A‖ ^ 2 := by
    rw [Finset.add_sum_erase s (fun j => inner ℝ A (v j)) hi, ← inner_sum]
    exact real_inner_self_eq_norm_sq A
  dsimp only [A] at hs he ⊢
  nlinarith

/-- Nonnegative weights keep the radial projection, including repeated lattice slots. -/
theorem weighted_projection {ι : Type*} (s : Finset ι)
    (v : ι → ℍ) (hcard : s.card = 6) (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hgood : 11 / 2 ≤ ‖∑ j ∈ s, v j‖) :
    ‖∑ j ∈ s, v j‖ * (∑ j ∈ s, f j) / 2 ≤
      inner ℝ (∑ j ∈ s, v j) (∑ j ∈ s, f j • v j) := by
  classical
  let A := ∑ j ∈ s, v j
  have hp (i : ι) (hi : i ∈ s) : ‖A‖ / 2 ≤ inner ℝ A (v i) := by
    have h := six_projection s v hcard hv i hi
    change ‖A‖ * (‖A‖ - 5) ≤ _ at h
    change 11 / 2 ≤ ‖A‖ at hgood
    nlinarith [norm_nonneg A]
  have h := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hf i hi))
  simp only [inner_sum, inner_smul_right] at *
  calc
    _ = ∑ j ∈ s, f j * (‖A‖ / 2) := by rw [← Finset.sum_mul]; dsimp only [A]; ring
    _ ≤ ∑ j ∈ s, f j * inner ℝ A (v j) := h
    _ = _ := rfl

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The weights in this lower bound are the actual six affected plaquette coefficients. -/
def localMass (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) : ℝ :=
  ∑ p ∈ affected n x μ, f p

omit [NeZero n] [Fact (1 < n)] in
theorem localMass_nonneg (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ)
    (hf : ∀ p, 0 ≤ f p) : 0 ≤ localMass n x μ f :=
  Finset.sum_nonneg (fun p _ => hf p)

omit [NeZero n] in
/-- A good actual Wilson exterior forces every nonnegative source radially outward. -/
theorem exterior_projection (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (f : PlaquetteIndex n → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hgood : 11 / 2 ≤ ‖exteriorStaple n x μ r‖) :
    ‖exteriorStaple n x μ r‖ * localMass n x μ f / 2 ≤
      inner ℝ (exteriorStaple n x μ r) (exteriorWeightedStaple n x μ r f) := by
  let v (p : PlaquetteIndex n) : ℍ :=
    staple n Q (exteriorConfig n x μ r) x μ p
  have hv (p : PlaquetteIndex n) (_hp : p ∈ affected n x μ) : ‖v p‖ = 1 :=
    CStarRing.norm_coe_unitary _
  have he : exteriorStaple n x μ r = ∑ p ∈ affected n x μ, v p := by
    simp only [exteriorStaple, stapleSum, weightedStaple, one_smul, v]
  rw [he] at hgood ⊢
  exact weighted_projection (affected n x μ) v (affected_card_eq_six n x μ) hv f
    (fun p _ => hf p) hgood

/-- An actual-law lower bound: the proved entropy estimate makes the good event
have probability at least one half, uniformly in the lattice volume. -/
theorem annealed_of_good_floor (x : Vertex n) (μ : Fin 4) (β C : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hC : 0 ≤ C)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72)
    (hfloor : ∀ r : Exterior n Q x μ, 11 / 2 ≤ ‖exteriorStaple n x μ r‖ →
      C ≤ fiberVariance n x μ β f r) :
    C / 2 ≤ ∫ U, originalVariance n x μ β f U ∂wilsonLaw n Q character β 2 := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  let bad := SU2StarEnergy.badEvent n x μ (11 / 2)
  have hs : MeasurableSet bad := SU2StarEnergy.badEvent_measurable n x μ (11 / 2)
  have hb : ν.real bad ≤ 1 / 2 := by
    have h := WilsonBadStapleProbability.bad_probability_bound n β hβ x μ (11 / 2)
      (by norm_num)
    change ν.real bad ≤ _ at h
    norm_num at h
    linarith
  have hv : Integrable (originalVariance n x μ β f) ν :=
    (originalVariance_continuous n x μ β f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (badᶜ.indicator (fun _ => C)) ν :=
    (integrable_const C).indicator hs.compl
  have hp (U : Configuration (Vertex n) Q) :
      badᶜ.indicator (fun _ => C) U ≤ originalVariance n x μ β f U := by
    by_cases hU : U ∈ badᶜ
    · rw [Set.indicator_of_mem hU]
      have hg : 11 / 2 ≤ ‖exteriorStaple n x μ (SU2StarEnergy.exterior n x μ U)‖ := by
        change ¬ ‖exteriorStaple n x μ (SU2StarEnergy.exterior n x μ U)‖ ≤ 11 / 2 at hU
        exact (lt_of_not_ge hU).le
      exact hfloor _ hg
    · rw [Set.indicator_of_notMem hU]
      exact originalVariance_nonneg n x μ β f U
  have h := integral_mono hi hv hp
  rw [integral_indicator_const _ hs.compl, measureReal_compl hs] at h
  simp only [probReal_univ, smul_eq_mul] at h
  have hc := mul_le_mul_of_nonneg_right hb hC
  change C / 2 ≤ ∫ U, originalVariance n x μ β f U ∂ν
  nlinarith

/-- The explicit good-event threshold is reached at weak coupling. -/
theorem eventual_good_coupling : ∀ᶠ β : ℝ in Filter.atTop,
    5 ≤ β ∧ WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72 := by
  have he := (WilsonEnergyDensity.energyEnvelope_tendsto.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 72 by norm_num)))
  filter_upwards [Filter.eventually_ge_atTop (5 : ℝ), he] with β hβ heβ
  exact ⟨hβ, heβ.le⟩

/-- The actual conditional source noise has a polynomial weak-coupling floor;
no covariance lower bound is assumed. -/
theorem fiberVariance_lower (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (hf : ∀ p, 0 ≤ f p)
    (r : Exterior n Q x μ) (hβ : 5 ≤ β)
    (hgood : 11 / 2 ≤ ‖exteriorStaple n x μ r‖) :
    (localMass n x μ f) ^ 2 / (192 * β ^ 2) ≤ fiberVariance n x μ β f r := by
  let A := exteriorStaple n x μ r
  let B := exteriorWeightedStaple n x μ r f
  let W := localMass n x μ f
  have hr : 0 < ‖A‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 2) hgood
  have hr6 : ‖A‖ ≤ 6 := exteriorStaple_norm_le_six n x μ r
  have hW : 0 ≤ W := localMass_nonneg n x μ f hf
  have hp : W / 2 ≤ inner ℝ A B / ‖A‖ := by
    apply (le_div_iff₀ hr).mpr
    have h := exterior_projection n x μ r f hf hgood
    change ‖A‖ * W / 2 ≤ inner ℝ A B at h
    nlinarith
  have hsq : (W / 2) ^ 2 ≤ (inner ℝ A B / ‖A‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr hp
  have hk : 50 ≤ 2 * β * ‖A‖ := by
    change 11 / 2 ≤ ‖A‖ at hgood
    nlinarith
  have hl := SU2RadialCovarianceLower.covariance_radial_lower β A B hk
  have hc := SU2InducedAction.covariance_self_nonneg β A B
  have hκ : (2 * β * ‖A‖) ^ 2 ≤ 144 * β ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg A) (by norm_num : (0 : ℝ) ≤ 6)).mpr hr6)
      (show 0 ≤ 4 * β ^ 2 by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hκ hc
  unfold fiberVariance
  rw [SU2WeightedRadial.conditional_source_variance]
  change W ^ 2 / (192 * β ^ 2) ≤ 4 * SU2InducedAction.covariance β A B B
  apply (div_le_iff₀ (by positivity : 0 < 192 * β ^ 2)).mpr
  nlinarith

/-- The positive conditional floor survives averaging under the original interacting law. -/
theorem annealed_variance_lower (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (hf : ∀ p, 0 ≤ f p) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    (localMass n x μ f) ^ 2 / (384 * β ^ 2) ≤
      ∫ U, originalVariance n x μ β f U ∂wilsonLaw n Q character β 2 := by
  have h := annealed_of_good_floor n x μ β
    ((localMass n x μ f) ^ 2 / (192 * β ^ 2)) f (by linarith) (by positivity)
    henergy (fun r hg => fiberVariance_lower n x μ β f hf r hβ hg)
  convert h using 1
  ring

end
end UnifiedTheory.Clay.YangMills.SU2PositiveSourceFloor
