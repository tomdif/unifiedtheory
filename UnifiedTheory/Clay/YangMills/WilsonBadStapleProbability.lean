/- A genuine volume-uniform low-staple probability estimate for the full SU(2)
Wilson measure. The estimate follows from the actual six-plaquette energy cost
and a proved entropy bound, with no assumed exterior-law concentration. -/
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity
import UnifiedTheory.Clay.YangMills.SU2StarEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open WilsonSingleLinkStaples SingleLinkWilsonOscillation WilsonIndependentBlocks
open WilsonEnergyDensity SU2StarEnergy

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- Six actual plaquette means, bounded using translation invariance. -/
theorem starEnergy_mean_bound (β : ℝ) (hβ : 0 < β) (x : Vertex n) (μ : Fin 4) :
    (∫ U, starEnergy n x μ U ∂wilsonLaw n Q character β 2) ≤
      36 * energyEnvelope β := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  unfold starEnergy
  rw [integral_finset_sum]
  · calc
      _ ≤ ∑ _p ∈ affected n x μ, 6 * energyEnvelope β :=
        Finset.sum_le_sum (fun p _ => plaquette_mean_bound n β hβ p)
      _ = 36 * energyEnvelope β := by
        simp only [Finset.sum_const, affected_card_eq_six, nsmul_eq_mul, Nat.cast_ofNat]
        ring
  · intro p _
    have hc : Continuous (fun U => plaquetteTerm n Q character 2 U p) := by
      simpa only [plaquetteDefect_eq_term] using
        WilsonAverageDefect.plaquette_continuous n Q representation representation_continuous p
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The actual original Wilson law, rather than a freely supplied marginal. -/
theorem bad_probability_bound (β : ℝ) (hβ : 0 < β) (x : Vertex n) (μ : Fin 4)
    (r₀ : ℝ) (hr₀ : r₀ < 6) :
    (wilsonLaw n Q character β 2).real (badEvent n x μ r₀) ≤
      18 * energyEnvelope β / (6 - r₀) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (starEnergy_nonneg n x μ))
    ((starEnergy_continuous n x μ).integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (2 * (6 - r₀))
  have hs := measureReal_mono (μ := wilsonLaw n Q character β 2)
    (badEvent_subset_energy n x μ r₀)
  have hb : 0 < 2 * (6 - r₀) := by linarith
  have h := (mul_le_mul_of_nonneg_left hs hb.le).trans
    (hm.trans (starEnergy_mean_bound n β hβ x μ))
  apply (le_div_iff₀ (by linarith : 0 < 6 - r₀)).mpr
  nlinarith

/-- The bound goes to zero along any diverging coupling, even when the volume varies. -/
theorem bad_probability_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (N i)) (μ : ι → Fin 4) (r₀ : ℝ) (hr₀ : r₀ < 6) :
    Filter.Tendsto
      (fun i => (wilsonLaw (N i) Q character (β i) 2).real (badEvent (N i) (x i) (μ i) r₀))
      l (nhds 0) := by
  have hu := ((energyEnvelope_tendsto.comp hβ).const_mul 18).div_const (6 - r₀)
  simp only [mul_zero, zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hβ.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with i hi
    exact bad_probability_bound (N i) (β i) hi (x i) (μ i) r₀ hr₀

end
end UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
