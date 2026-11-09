/- Every fixed natural moment of the actual microscopic Wilson excess has a
volume-uniform Gamma(3/2) limit. These moments describe conditional ultraviolet
noise, not a renormalized spacetime hierarchy. -/
import UnifiedTheory.Clay.YangMills.SU2ExcessAllMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2WilsonAllMoments
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt SU2StarEnergy SU2WilsonConditionalSource
open SU2WilsonLocalEquipartition SU2ExcessAllMoments
open scoped Quaternion RealInnerProductSpace Topology

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def conditionalMoment (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) : ℝ :=
  GibbsMarginalTower.response haar (splitAction n x μ β)
    (fun z => (splitExcess n x μ β z)^m) r

def moment (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  ∫ U, (localExcess n x μ β U)^m ∂wilsonLaw n Q character β 2

omit [Fact (1 < n)] in
theorem conditionalMoment_continuous (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (conditionalMoment n m x μ β) :=
  GibbsMarginalTower.response_continuous haar _ _ (splitAction_continuous n x μ β)
    ((splitExcess_continuous n x μ β).pow m)

theorem conditionalMoment_eq_axis (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    conditionalMoment n m x μ β r = axisMoment m (2*β*‖exteriorStaple n x μ r‖) := by
  rw [conditionalMoment, GibbsMarginalTower.response_eq_expectation haar _ _
    (splitAction_continuous n x μ β) r]
  change (∫ q, (excess β (exteriorStaple n x μ r) q)^m ∂conditionalLaw n x μ β r) = _
  rw [conditionalLaw_eq_tiltLaw, excess_pow_mean]

omit [Fact (1 < n)] in
/-- Exact disintegration under the original interacting law for every power. -/
theorem moment_eq_conditional (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    moment n m x μ β = ∫ U, conditionalMoment n m x μ β (exterior n x μ U)
      ∂wilsonLaw n Q character β 2 := by
  have ht := (SU2WilsonMarginalTransport.wilson_coordinates_preserving n x μ β).integral_comp
    (SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm.measurableEmbedding
    (fun z => (splitExcess n x μ β z)^m)
  have he (U : Configuration (Vertex n) Q) :
      localExcess n x μ β U = splitExcess n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U) := by
    simpa only [MeasurableEquiv.apply_symm_apply] using
      localExcess_assemble n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U)
  unfold moment
  simp_rw [he]
  rw [ht]
  have hr := GibbsMarginalTower.response_expectation (exteriorMeasure n Q x μ) haar
    (splitAction n x μ β) (fun z => (splitExcess n x μ β z)^m)
    (splitAction_continuous n x μ β) ((splitExcess_continuous n x μ β).pow m)
  rw [← hr]
  exact SU2WilsonMarginalTransport.retained_integral_eq_wilson n x μ β
    (conditionalMoment n m x μ β) (conditionalMoment_continuous n m x μ β)

theorem conditionalMoment_bounds (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (hβ : 0 ≤ β) (r : Exterior n Q x μ) :
    0 ≤ conditionalMoment n m x μ β r ∧ conditionalMoment n m x μ β r ≤ momentBound m := by
  rw [conditionalMoment_eq_axis]
  exact axisMoment_bounds _ _ (by positivity)

/-- The bound is uniform in beta, exterior, and finite lattice period, for each order. -/
theorem moment_bounds (m : ℕ) (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ moment n m x μ β ∧ moment n m x μ β ≤ momentBound m := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  refine ⟨integral_nonneg (fun U => pow_nonneg (localExcess_nonneg n x μ β hβ U) m), ?_⟩
  rw [moment_eq_conditional]
  have hc := (conditionalMoment_continuous n m x μ β).comp (exterior_continuous n x μ)
  have h := integral_mono (hc.integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (integrable_const (momentBound m))
    (fun U => (conditionalMoment_bounds n m x μ β hβ (exterior n x μ U)).2)
  simpa using h

theorem conditional_error (m : ℕ) (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (U : Configuration (Vertex n) Q) :
    |conditionalMoment n m x μ β (exterior n x μ U) - gammaMoment m| ≤
      errorConstant m / (2*β * r₀) +
        (badEvent n x μ r₀).indicator (fun _ => momentBound m + gammaMoment m) U := by
  classical
  by_cases hU : U ∈ badEvent n x μ r₀
  · rw [Set.indicator_of_mem hU]
    have h := conditionalMoment_bounds n m x μ β hβ.le (exterior n x μ U)
    have hM := (gammaMoment_pos m).le
    have hE : 0 ≤ errorConstant m / (2*β * r₀) :=
      div_nonneg (errorConstant_pos m).le (by positivity)
    rw [abs_le]
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hU, add_zero, conditionalMoment_eq_axis]
    have hr : r₀ ≤ ‖stapleField n x μ U‖ := le_of_lt (lt_of_not_ge hU)
    have hk : 3/2 ≤ 2*β*‖stapleField n x μ U‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hr hβ.le]
    exact (axisMoment_error m hk).trans
      (div_le_div_of_nonneg_left (errorConstant_pos m).le (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hr hβ.le]))

/-- Actual-law convergence rate, including the proved small-staple probability. -/
theorem moment_error (m : ℕ) (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) (hβr : 3 / 4 ≤ β * r₀) :
    |moment n m x μ β - gammaMoment m| ≤ errorConstant m / (2*β * r₀) +
      (momentBound m + gammaMoment m) *
        (18 * WilsonEnergyDensity.energyEnvelope β / (6-r₀)) := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  let F := fun U => conditionalMoment n m x μ β (exterior n x μ U)
  have hc : Continuous F :=
    (conditionalMoment_continuous n m x μ β).comp (exterior_continuous n x μ)
  have hi : Integrable F ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun U => F U - gammaMoment m) ν := hi.sub (integrable_const _)
  have hs := badEvent_measurable n x μ r₀
  have hind : Integrable ((badEvent n x μ r₀).indicator
      (fun _ => momentBound m + gammaMoment m)) ν := (integrable_const _).indicator hs
  have h := integral_mono hi'.norm
    ((integrable_const (errorConstant m / (2*β * r₀))).add hind)
    (fun U => by simpa only [Real.norm_eq_abs] using conditional_error n m x μ β r₀ hβ hr₀ hβr U)
  simp only [Pi.add_apply, Real.norm_eq_abs] at h
  rw [integral_add (integrable_const _) hind, integral_indicator_const _ hs] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hp := WilsonBadStapleProbability.bad_probability_bound n β hβ x μ r₀ hr₆
  change ν.real (badEvent n x μ r₀) ≤ _ at hp
  have hB : 0 ≤ momentBound m + gammaMoment m :=
    add_nonneg (momentBound_pos m).le (gammaMoment_pos m).le
  have hm := mul_le_mul_of_nonneg_left hp hB
  rw [moment_eq_conditional]
  change |(∫ U, F U ∂ν) - gammaMoment m| ≤ _
  have he : (∫ U, F U - gammaMoment m ∂ν) = (∫ U, F U ∂ν) - gammaMoment m := by
    rw [integral_sub hi (integrable_const _)]
    simp
  rw [← he]
  exact abs_integral_le_integral_abs.trans (by nlinarith)

omit n [NeZero n] [Fact (1 < n)] in
/-- Every fixed natural moment converges, with arbitrary changing lattice volumes. -/
theorem moment_tendsto {ι : Type*} {l : Filter ι} (m : ℕ)
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Tendsto (fun i => moment (period i) m (x i) (μ i) (β i)) l (𝓝 (gammaMoment m)) := by
  have hi : Tendsto (fun i => errorConstant m / (2*β i*3)) l (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hβ).const_mul (errorConstant m / 6)
    convert h using 1
    · funext i; dsimp only [Function.comp_apply]; ring
    · simp
  have he := (((WilsonEnergyDensity.energyEnvelope_tendsto.comp hβ).const_mul 18).div_const
    (6-3)).const_mul (momentBound m + gammaMoment m)
  simp only [mul_zero, zero_div] at he
  have hz := hi.add he
  simp only [add_zero] at hz
  have habs : Tendsto (fun i => |moment (period i) m (x i) (μ i) (β i) - gammaMoment m|)
      l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hz
    filter_upwards [hβ.eventually_ge_atTop 1] with i hi
    exact moment_error (period i) m (x i) (μ i) (β i) 3 (by linarith)
      (by norm_num) (by norm_num) (by nlinarith)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- The third connected moment, in its usual raw-moment formula. -/
def connectedThird (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  moment n 3 x μ β - 3 * moment n 1 x μ β * moment n 2 x μ β +
    2 * (moment n 1 x μ β)^3

/-- The fourth cumulant removes the disconnected variance-square contribution. -/
def connectedFourth (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  moment n 4 x μ β - 4 * moment n 1 x μ β * moment n 3 x μ β -
    3 * (moment n 2 x μ β)^2 + 12 * (moment n 1 x μ β)^2 * moment n 2 x μ β -
      6 * (moment n 1 x μ β)^4

omit [Fact (1 < n)] in
/-- The third connected formula is the actual centered third integral. -/
theorem connectedThird_eq_centered (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    connectedThird n x μ β =
      ∫ U, (localExcess n x μ β U - moment n 1 x μ β)^3
        ∂wilsonLaw n Q character β 2 := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  let F := localExcess n x μ β
  let c := moment n 1 x μ β
  have hi (j : ℕ) : Integrable (fun U => (F U)^j) ν :=
    ((localExcess_continuous n x μ β).pow j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiF : Integrable F ν := by simpa only [pow_one] using hi 1
  have he (U : Configuration (Vertex n) Q) : (F U-c)^3 =
      ((F U)^3 - (3*c)*(F U)^2) + (3*c^2)*F U - c^3 := by ring
  change connectedThird n x μ β = ∫ U, (F U-c)^3 ∂ν
  simp_rw [he]
  have hi32 : Integrable (fun U => (F U)^3 - (3*c)*(F U)^2) ν :=
    (hi 3).sub ((hi 2).const_mul (3*c))
  have hi321 : Integrable (fun U => (F U)^3 - (3*c)*(F U)^2 + (3*c^2)*F U) ν :=
    hi32.add (hiF.const_mul (3*c^2))
  rw [integral_sub hi321 (integrable_const (c^3)),
    integral_add hi32 (hiF.const_mul (3*c^2)),
    integral_sub (hi 3) ((hi 2).const_mul (3*c)), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hm1 : (∫ U, F U ∂ν) = moment n 1 x μ β := by
    simp only [moment, pow_one]
    rfl
  rw [hm1]
  change connectedThird n x μ β = moment n 3 x μ β - (3*c)*moment n 2 x μ β +
    (3*c^2)*moment n 1 x μ β - c^3
  unfold connectedThird
  dsimp only [c]
  ring

omit n [NeZero n] [Fact (1 < n)] in
/-- The genuine microscopic noise has a nonzero third cumulant in the weak-coupling limit. -/
theorem connectedThird_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Tendsto (fun i => connectedThird (period i) (x i) (μ i) (β i)) l (𝓝 3) := by
  have h1 := moment_tendsto 1 period β hβ x μ
  have h2 := moment_tendsto 2 period β hβ x μ
  have h3 := moment_tendsto 3 period β hβ x μ
  have h := (h3.sub ((h1.const_mul 3).mul h2)).add ((h1.pow 3).const_mul 2)
  norm_num at h
  exact h

omit n [NeZero n] [Fact (1 < n)] in
/-- The fourth connected moment also survives; the local limiting noise is not Gaussian. -/
theorem connectedFourth_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Tendsto (fun i => connectedFourth (period i) (x i) (μ i) (β i)) l (𝓝 9) := by
  have h1 := moment_tendsto 1 period β hβ x μ
  have h2 := moment_tendsto 2 period β hβ x μ
  have h3 := moment_tendsto 3 period β hβ x μ
  have h4 := moment_tendsto 4 period β hβ x μ
  have h := (((h4.sub ((h1.const_mul 4).mul h3)).sub ((h2.pow 2).const_mul 3)).add
    (((h1.pow 2).const_mul 12).mul h2)).sub ((h1.pow 4).const_mul 6)
  norm_num at h
  exact h

end
end UnifiedTheory.Clay.YangMills.SU2WilsonAllMoments
