import UnifiedTheory.Clay.YangMills.QuantitativeWilsonConcentration
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples
import UnifiedTheory.Clay.YangMills.GibbsFreeEnergyBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonEnergyDensity
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open WilsonAverageDefect WilsonIdentityNeighborhood UnitaryHaarNeighborhood
open WilsonSingleLinkStaples

/-- The actual fundamental unitary representation of the quaternion SU(2) group. -/
def representation : Q →* Matrix.unitaryGroup (Fin 2) ℂ :=
  (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup).comp
    SU2QuaternionCoordinates.unitaryToSpecialUnitary

theorem representation_continuous : Continuous representation :=
  (SU2QuaternionCoordinates.toMatrix_continuous.comp continuous_subtype_val).subtype_mk
    (fun q => (representation q).property)

theorem representation_character : unitaryCharacter representation = character := rfl

/-- A conservative grid: its entropy grows only logarithmically in the coupling. -/
def grid (β : ℝ) : ℕ := ⌈β⌉₊ + 1

theorem grid_pos (β : ℝ) : 0 < grid β := by unfold grid; omega

theorem beta_le_grid (β : ℝ) : β ≤ (grid β : ℝ) := by
  have h := Nat.le_ceil β
  unfold grid
  push_cast
  linarith

theorem grid_le (β : ℝ) (hβ : 0 ≤ β) : (grid β : ℝ) ≤ β + 2 := by
  have h := (Nat.ceil_lt_add_one hβ).le
  unfold grid
  push_cast
  linarith

theorem grid_log_le (β : ℝ) (hβ : 0 < β) :
    Real.log ((2 * grid β + 1 : ℕ) : ℝ) ≤ Real.log (2 * β + 5) := by
  apply Real.log_le_log (by positivity)
  have h := grid_le β hβ.le
  push_cast
  linarith

/-- Explicit volume-independent mean energy envelope for the actual SU(2) action. -/
def energyEnvelope (β : ℝ) : ℝ :=
  1568 / β^2 + (16 / (3 * β)) * Real.log (2 * β + 5)

theorem energyEnvelope_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ energyEnvelope β := by
  have hlog : 0 ≤ Real.log (2 * β + 5) := Real.log_nonneg (by linarith)
  unfold energyEnvelope
  positivity

variable (n : ℕ) [NeZero n]

def energyDensity (U : Configuration (Vertex n) Q) : ℝ := averageDefect n Q representation U

omit [NeZero n] in
theorem plaquetteDefect_eq_term (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) :
    plaquetteDefect n Q representation p U =
      WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p := by
  unfold plaquetteDefect UnitaryHolonomyDefect.defect WilsonIndependentBlocks.plaquetteTerm
  rw [representation_character]
  norm_num [Fintype.card_fin, WilsonMomentBounds.loopObservable, wilson]

theorem energyDensity_eq (U : Configuration (Vertex n) Q) :
    energyDensity n U = (∑ p, WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p) /
      (6 * (Fintype.card (Vertex n) : ℝ)) := by
  simp only [energyDensity, averageDefect, plaquetteDefect_eq_term]

theorem energyDensity_continuous : Continuous (energyDensity n) :=
  average_continuous n Q representation representation_continuous

theorem energyDensity_nonneg (U : Configuration (Vertex n) Q) : 0 ≤ energyDensity n U :=
  average_nonneg n Q representation U

/-- The grid cap gives an entropy estimate for every positive coupling, with no
coupling-threshold assumption. Its volume factors cancel exactly. -/
theorem average_grid_entropy_bound {d : Type*} [Fintype d] [DecidableEq d]
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (β : ℝ) (hβ : 0 < β) :
    (∫ U, averageDefect n G ρ U
      ∂wilsonLaw n G (unitaryCharacter ρ) β (Fintype.card d)) ≤
      squaredTolerance d K + (4 * (Fintype.card d : ℝ)^2 / (3 * β)) *
        Real.log ((2 * K + 1 : ℕ) : ℝ) := by
  rw [law_eq_average_weight n G ρ hρ β]
  have hv := volume_pos n
  have hp := pow_pos (massLower_pos d K) (4 * Fintype.card (Vertex n))
  have hb : 0 < 6 * β * (Fintype.card (Vertex n) : ℝ) := by positivity
  have he := GibbsFreeEnergyBound.weighted_cap_expectation_bound
    (referenceMeasure G (Vertex n)) (averageDefect n G ρ)
    (average_continuous n G ρ hρ) (6 * β * (Fintype.card (Vertex n) : ℝ)) hb
    (squaredTolerance d K) ((massLower d K)^(4 * Fintype.card (Vertex n))) hp
    (goodEvent n G (nearIdentity ρ K))
    (goodEvent_measurable n G _ (nearIdentity_measurable ρ hρ K))
    (by
      rw [goodEvent_mass]
      exact pow_le_pow_left₀ (massLower_pos d K).le
        (nearIdentity_mass_lower ρ hρ K hK) _)
    (fun U hU => goodEvent_small n G ρ (nearIdentity ρ K) (squaredTolerance d K)
      (fun a ha b hb c hc e he => four_link_defect_squared_bound ρ K a b c e ha hb hc he)
      U hU)
  convert he using 1
  unfold massLower
  rw [Real.log_pow, one_div, Real.log_inv, Real.log_pow]
  push_cast
  field_simp
  ring

/-- The fundamental SU(2) representation gives a completely explicit density bound. -/
theorem energyDensity_grid_bound (K : ℕ) (hK : 0 < K) (β : ℝ) (hβ : 0 < β) :
    (∫ U, energyDensity n U ∂wilsonLaw n Q character β 2) ≤
      1568 / (K : ℝ)^2 + (16 / (3 * β)) * Real.log ((2 * K + 1 : ℕ) : ℝ) := by
  have h := average_grid_entropy_bound n Q representation representation_continuous K hK β hβ
  simpa only [energyDensity, representation_character, Fintype.card_fin,
    squaredTolerance_formula, Nat.cast_ofNat, show (2 * (2 : ℝ)^4 * (1 + 3 * 2)^2) = 1568 by
      norm_num, show 4 * (2 : ℝ)^2 = 16 by norm_num] using h

/-- No volume, period-dependent threshold, or exterior-distribution hypothesis occurs. -/
theorem energyDensity_bound (β : ℝ) (hβ : 0 < β) :
    (∫ U, energyDensity n U ∂wilsonLaw n Q character β 2) ≤ energyEnvelope β := by
  apply (energyDensity_grid_bound n (grid β) (grid_pos β) β hβ).trans
  unfold energyEnvelope
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hβ.le (beta_le_grid β) 2)
  · exact mul_le_mul_of_nonneg_left (grid_log_le β hβ) (by positivity)

/-- Translation invariance upgrades the mean-density estimate to each actual plaquette. -/
theorem plaquette_mean_bound (β : ℝ) (hβ : 0 < β) (p : PlaquetteIndex n) :
    (∫ U, WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p
      ∂wilsonLaw n Q character β 2) ≤ 6 * energyEnvelope β := by
  have h := mean_plaquette_le_six_average n Q representation representation_continuous β 2 p
  simp only [representation_character, plaquetteDefect_eq_term] at h
  exact h.trans (mul_le_mul_of_nonneg_left (energyDensity_bound n β hβ) (by norm_num))

/-- The explicit bound vanishes at weak coupling, independently of the period. -/
theorem energyEnvelope_tendsto : Filter.Tendsto energyEnvelope Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun β : ℝ => 1568 / β^2) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by decide : 2 ≠ 0))).const_mul
        (1568 : ℝ)
  have ha : Filter.Tendsto (fun β : ℝ => 2 * β + 5) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) Filter.tendsto_id)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop (3 / 2) (-(15 / 2)) 1
    (by norm_num)).comp ha
  have hl' : Filter.Tendsto (fun β : ℝ => (16 / (3 * β)) * Real.log (2 * β + 5))
      Filter.atTop (nhds 0) := by
    convert hl.const_mul 16 using 1
    · ext β
      simp only [Function.comp_apply, pow_one]
      rw [show (3 : ℝ) / 2 * (2 * β + 5) + -(15 / 2) = 3 * β by ring]
      ring
    · norm_num
  simpa only [energyEnvelope, add_zero] using hpow.add hl'

end
end UnifiedTheory.Clay.YangMills.WilsonEnergyDensity
