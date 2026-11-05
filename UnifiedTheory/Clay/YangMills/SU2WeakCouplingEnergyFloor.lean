/- A lower weak-coupling energy scale for the actual Wilson law.
The local conditional excitation is an ultraviolet observable. Its survival
and the resulting inverse-coupling energy floor do not construct a nonzero
continuum field or identify the physical running coupling. -/
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalEquipartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WeakCouplingEnergyFloor
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open WilsonSingleLinkStaples SingleLinkWilsonOscillation WilsonIndependentBlocks
open WilsonEnergyDensity SU2StarEnergy WilsonAverageDefect
open scoped Topology

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- The exact mean energy density controls each incident six-plaquette sum.
This comparison uses the actual density, not its upper envelope. -/
theorem starEnergy_mean_le_density (β : ℝ) (x : Vertex n) (μ : Fin 4) :
    (∫ U, starEnergy n x μ U ∂wilsonLaw n Q character β 2) ≤
      36 * (∫ U, energyDensity n U ∂wilsonLaw n Q character β 2) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  unfold starEnergy
  rw [integral_finset_sum]
  · calc
      _ ≤ ∑ _p ∈ affected n x μ,
          6 * (∫ U, energyDensity n U ∂wilsonLaw n Q character β 2) := by
        apply Finset.sum_le_sum
        intro p _
        have h := mean_plaquette_le_six_average n Q representation
          representation_continuous β 2 p
        simpa only [representation_character, plaquetteDefect_eq_term, energyDensity] using h
      _ = _ := by
        simp only [Finset.sum_const, affected_card_eq_six, nsmul_eq_mul, Nat.cast_ofNat]
        ring
  · intro p _
    have hc : Continuous (fun U => plaquetteTerm n Q character 2 U p) := by
      simpa only [plaquetteDefect_eq_term] using
        WilsonAverageDefect.plaquette_continuous n Q representation representation_continuous p
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The actual local excitation forces an inverse-coupling density scale. -/
theorem scaled_density_lower (β : ℝ) (hβ : 0 ≤ β) (x : Vertex n) (μ : Fin 4) :
    (∫ U, SU2WilsonLocalEquipartition.localExcess n x μ β U
      ∂wilsonLaw n Q character β 2) / 36 ≤
        β * (∫ U, energyDensity n U ∂wilsonLaw n Q character β 2) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have h := integral_mono
    ((SU2WilsonLocalEquipartition.localExcess_continuous n x μ β).integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul (starEnergy_continuous n x μ)).integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (SU2WilsonLocalEquipartition.localExcess_le_starEnergy n x μ β hβ)
  simp only [Pi.mul_apply] at h
  rw [integral_const_mul] at h
  have hd := mul_le_mul_of_nonneg_left (starEnergy_mean_le_density n β x μ) hβ
  linarith

omit n [NeZero n] [Fact (1 < n)] in
/-- This lower bound is uniform along arbitrary changing periods and links.
It requires no physical-coupling trajectory or continuum witness. -/
theorem eventual_scaled_density_floor {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4)
    (c : ℝ) (hc : c < 1 / 24) :
    ∀ᶠ i in l, c ≤ β i * (∫ U, energyDensity (period i) U
      ∂wilsonLaw (period i) Q character (β i) 2) := by
  have hm := SU2WilsonLocalEquipartition.mean_tendsto period β hβ x μ
  have ht : 36 * c < (3 / 2 : ℝ) := by linarith
  filter_upwards [hm.eventually (lt_mem_nhds ht),
    hβ.eventually (eventually_gt_atTop (0 : ℝ))] with i hi hbi
  have hl := scaled_density_lower (period i) (β i) hbi.le (x i) (μ i)
  linarith

omit n [NeZero n] [Fact (1 < n)] in
/-- The established upper envelope and the new lower floor hold under the
same actual Wilson measure. This does not assert a sharp asymptotic constant. -/
theorem eventual_density_bounds {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    ∀ᶠ i in l,
      1 / (48 * β i) ≤ (∫ U, energyDensity (period i) U
        ∂wilsonLaw (period i) Q character (β i) 2) ∧
      (∫ U, energyDensity (period i) U
        ∂wilsonLaw (period i) Q character (β i) 2) ≤ energyEnvelope (β i) := by
  filter_upwards [eventual_scaled_density_floor period β hβ x μ (1 / 48) (by norm_num),
    hβ.eventually (eventually_gt_atTop (0 : ℝ))] with i hi hbi
  refine ⟨?_, energyDensity_bound (period i) (β i) hbi⟩
  apply (div_le_iff₀ (by positivity : 0 < 48 * β i)).mpr
  nlinarith

omit n [NeZero n] [Fact (1 < n)] in
/-- The density cannot be little-o of inverse coupling, even at growing volume. -/
theorem scaled_density_not_tendsto_zero {ι : Type*} {l : Filter ι} [NeBot l]
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    ¬ Tendsto (fun i => β i * (∫ U, energyDensity (period i) U
      ∂wilsonLaw (period i) Q character (β i) 2)) l (𝓝 0) := by
  intro hzero
  have h := ge_of_tendsto hzero
    (eventual_scaled_density_floor period β hβ x μ (1 / 48) (by norm_num))
  norm_num at h

end
end UnifiedTheory.Clay.YangMills.SU2WeakCouplingEnergyFloor
