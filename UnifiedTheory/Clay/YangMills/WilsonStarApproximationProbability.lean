/- The all-direction SU(2) star approximation under the original interacting
Wilson law. Its error tends to zero in probability at any diverging coupling,
uniformly over varying lattice periods and selected links. No uniform
integrability, simultaneous all-link event or multiscale estimate is inferred. -/
import UnifiedTheory.Clay.YangMills.SU2GeneralStarApproximation
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonStarApproximationProbability
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonUniformVariance
open SU2StarEnergy WilsonEnergyDensity WilsonBadStapleProbability SU2GeneralStarApproximation
open scoped Quaternion RealInnerProductSpace Topology

/-- Explicit probability envelope at beta = t^4. -/
def probabilityEnvelope (t : ℝ) : ℝ := 18 * t ^ 3 * energyEnvelope (t ^ 4)

theorem weighted_energy_bound (t : ℝ) (ht : 1 ≤ t) :
    t ^ 3 * energyEnvelope (t ^ 4) ≤
      1568 / t ^ 5 + (16 / 3) * (Real.log 7 + 4 * Real.log t) / t := by
  have ht0 : 0 < t := by linarith
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have hlog : Real.log (2 * t ^ 4 + 5) ≤ Real.log 7 + 4 * Real.log t := by
    have h := Real.log_le_log (by positivity : 0 < 2 * t ^ 4 + 5)
      (show 2 * t ^ 4 + 5 ≤ 7 * t ^ 4 by linarith)
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (pow_ne_zero 4 ht0.ne'), Real.log_pow] at h
    exact h
  have he : t ^ 3 * energyEnvelope (t ^ 4) =
      1568 / t ^ 5 + (16 / 3) * Real.log (2 * t ^ 4 + 5) / t := by
    unfold energyEnvelope
    field_simp
  rw [he]
  gcongr

theorem probabilityEnvelope_tendsto : Tendsto probabilityEnvelope atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ => 1568 / t ^ 5) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 5 ≠ 0))).const_mul
        (1568 : ℝ)
  have hinv : Tendsto (fun t : ℝ => Real.log 7 / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (Real.log 7)
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hupper : Tendsto (fun t : ℝ =>
      1568 / t ^ 5 + (16 / 3) * (Real.log 7 + 4 * Real.log t) / t) atTop (𝓝 0) := by
    convert hpow.add ((hinv.add (hlog.const_mul 4)).const_mul (16 / 3)) using 1
    · ext t
      ring
    · norm_num
  have hweighted : Tendsto (fun t : ℝ => t ^ 3 * energyEnvelope (t ^ 4)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (by positivity) (energyEnvelope_nonneg _ (by positivity))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact weighted_energy_bound t ht
  simpa only [probabilityEnvelope, ← mul_assoc, mul_zero] using hweighted.const_mul 18

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- Actual generated interaction error at the selected link, as a full-law observable. -/
def actualError (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (U : Configuration (Vertex n) Q) : ℝ := error β (stapleField n x μ U)

def errorEvent (x : Vertex n) (μ : Fin 4) (β ε : ℝ) :
    Set (Configuration (Vertex n) Q) := {U | ε ≤ |actualError n x μ β U|}

omit [Fact (1 < n)] in
theorem actualError_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (actualError n x μ β) :=
  (error_continuous β).comp (stapleField_continuous n x μ)

omit [Fact (1 < n)] in
theorem errorEvent_measurable (x : Vertex n) (μ : Fin 4) (β ε : ℝ) :
    MeasurableSet (errorEvent n x μ β ε) :=
  (isClosed_le continuous_const (actualError_continuous n x μ β).abs).measurableSet

omit [NeZero n] in
/-- The quadratic form uses the six actual exterior staple triples. -/
theorem actual_quadratic_disagreement (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    quadratic β (exteriorStaple n x μ r) =
      β * disagreement (SingleLinkWilsonOscillation.affected n x μ)
        (fun p => (staple n Q (exteriorConfig n x μ r) x μ p : Quaternion ℝ)) / 6 := by
  have h := quadratic_eq_disagreement (SingleLinkWilsonOscillation.affected n x μ)
    (fun p => (staple n Q (exteriorConfig n x μ r) x μ p : Quaternion ℝ))
    (affected_card_eq_six n x μ)
    (fun p _ => CStarRing.norm_of_mem_unitary
      (staple n Q (exteriorConfig n x μ r) x μ p).property) β
  simpa only [exteriorStaple, stapleSum, weightedStaple, one_smul] using h

/-- Exact accounting for the full induced action, including its exterior reference term. -/
theorem effectiveAction_expansion (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    GibbsMarginalTower.effectiveAction SU2HaarTilt.haar
        (SU2WilsonConditionalSource.splitAction n x μ β) r =
      β * exteriorSourceConstant n x μ r (fun _ => 1) +
        SU2InducedAction.potential β ((6 : ℝ) • (1 : Quaternion ℝ)) +
        quadratic β (exteriorStaple n x μ r) + error β (exteriorStaple n x μ r) := by
  rw [SU2InducedAction.wilson_effectiveAction]
  unfold error
  ring

omit [NeZero n] in
/-- The small-error event is deduced from the actual six-plaquette geometry. -/
theorem errorEvent_subset_bad (x : Vertex n) (μ : Fin 4) (t : ℝ) (ht : 1 ≤ t) :
    errorEvent n x μ (t ^ 4) (1 / t ^ 2) ⊆ badEvent n x μ (6 - 1 / t ^ 3) := by
  intro U hU
  change 1 / t ^ 2 ≤ |error (t ^ 4) (stapleField n x μ U)| at hU
  change ‖stapleField n x μ U‖ ≤ 6 - 1 / t ^ 3
  by_contra hn
  have h := error_bound_fourth_power t ht (stapleField n x μ U)
    (stapleField_norm_le_six n x μ U) (by linarith [lt_of_not_ge hn])
  have ht0 : 0 < t := by linarith
  have hgap : 2 / (3 * t ^ 2) < 1 / t ^ 2 := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos ht0]
  exact (not_lt_of_ge (hU.trans h)) hgap

/-- The error probability has no lattice-volume factor and no supplied law estimate. -/
theorem error_probability_bound (x : Vertex n) (μ : Fin 4) (t : ℝ) (ht : 1 ≤ t) :
    (wilsonLaw n Q character (t ^ 4) 2).real
      (errorEvent n x μ (t ^ 4) (1 / t ^ 2)) ≤ probabilityEnvelope t := by
  letI := wilsonLaw_probability n Q character character_continuous (t ^ 4) 2
  have ht0 : 0 < t := by linarith
  have h := (measureReal_mono (μ := wilsonLaw n Q character (t ^ 4) 2)
    (errorEvent_subset_bad n x μ t ht)).trans
      (bad_probability_bound n (t ^ 4) (by positivity) x μ (6 - 1 / t ^ 3)
        (by have := one_div_pos.mpr (pow_pos ht0 3); linarith))
  convert h using 1
  unfold probabilityEnvelope
  field_simp
  ring

/-- Simultaneous control retains the exact number-of-links cost. Independence
is unnecessary; this does not remove the extensive continuum-volume factor. -/
theorem simultaneous_probability_bound {I : Type*} (s : Finset I)
    (x : I → Vertex n) (μ : I → Fin 4) (t : ℝ) (ht : 1 ≤ t) :
    (wilsonLaw n Q character (t ^ 4) 2).real
      (⋃ i ∈ s, errorEvent n (x i) (μ i) (t ^ 4) (1 / t ^ 2)) ≤
        s.card * probabilityEnvelope t := by
  calc
    _ ≤ ∑ i ∈ s, (wilsonLaw n Q character (t ^ 4) 2).real
        (errorEvent n (x i) (μ i) (t ^ 4) (1 / t ^ 2)) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, probabilityEnvelope t :=
      Finset.sum_le_sum (fun i _ => error_probability_bound n (x i) (μ i) t ht)
    _ = _ := by simp

omit [NeZero n] [Fact (1 < n)] in
/-- Outside the simultaneous bad event the sum of absolute local errors is bounded. -/
theorem sum_error_bound_off_event {I : Type*} (s : Finset I)
    (x : I → Vertex n) (μ : I → Fin 4) (t : ℝ) (U : Configuration (Vertex n) Q)
    (hU : U ∉ ⋃ i ∈ s, errorEvent n (x i) (μ i) (t ^ 4) (1 / t ^ 2)) :
    (∑ i ∈ s, |actualError n (x i) (μ i) (t ^ 4) U|) ≤ s.card / t ^ 2 := by
  have hi (i : I) (his : i ∈ s) : |actualError n (x i) (μ i) (t ^ 4) U| ≤ 1 / t ^ 2 := by
    have hn : U ∉ errorEvent n (x i) (μ i) (t ^ 4) (1 / t ^ 2) :=
      fun h => hU (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨his, h⟩⟩)
    exact (lt_of_not_ge hn).le
  calc
    _ ≤ ∑ _i ∈ s, (1 / t ^ 2) := Finset.sum_le_sum hi
    _ = _ := by simp [div_eq_mul_inv]

omit n [NeZero n] [Fact (1 < n)] in
/-- Vanishing error probability for arbitrary varying lattices and selected links. -/
theorem error_probability_fourth_power_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (t : ι → ℝ) (ht : Tendsto t l atTop)
    (x : ∀ i, Vertex (N i)) (μ : ι → Fin 4) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun i => (wilsonLaw (N i) Q character (t i ^ 4) 2).real
      (errorEvent (N i) (x i) (μ i) (t i ^ 4) ε)) l (𝓝 0) := by
  have hinv : Tendsto (fun i => 1 / t i ^ 2) l (𝓝 0) := by
    simpa only [one_div] using
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (probabilityEnvelope_tendsto.comp ht)
  · exact Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [ht.eventually_ge_atTop 1, hinv.eventually (gt_mem_nhds hε)] with i hi he
    letI := wilsonLaw_probability (N i) Q character character_continuous (t i ^ 4) 2
    apply (measureReal_mono (μ := wilsonLaw (N i) Q character (t i ^ 4) 2) ?_).trans
      (error_probability_bound (N i) (x i) (μ i) (t i) hi)
    intro U hU
    exact he.le.trans hU

omit n [NeZero n] [Fact (1 < n)] in
/-- Every diverging coupling trajectory is covered, with arbitrary varying volume.
This is convergence in probability for one selected generated interaction. -/
theorem error_probability_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (N i)) (μ : ι → Fin 4) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun i => (wilsonLaw (N i) Q character (β i) 2).real
      (errorEvent (N i) (x i) (μ i) (β i) ε)) l (𝓝 0) := by
  have ht := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hβ)
  have h := error_probability_fourth_power_tendsto N
    (fun i => Real.sqrt (Real.sqrt (β i))) ht x μ ε hε
  apply h.congr'
  filter_upwards [hβ.eventually_ge_atTop 0] with i hi
  have he : Real.sqrt (Real.sqrt (β i)) ^ 4 = β i := by
    calc
      _ = (Real.sqrt (Real.sqrt (β i)) ^ 2) ^ 2 := by ring
      _ = β i := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hi]
  rw [he]

end
end UnifiedTheory.Clay.YangMills.WilsonStarApproximationProbability
