/-
Exact SU(2) conditional response at an aligned six-staple exterior, together
with an original-Wilson-law lower proxy for eighteen tangent responses.
The response is the actual normalized Haar expectation. The annealed lower
envelope tends to three along every diverging coupling and changing volumes.

The quaternion path, metric bounds, and scalar original-law estimates are
proved here. The lattice identification of eighteen distinct neighbor
perturbations and the Wasserstein interpretation are separate geometric
arguments; this module does not define a Dobrushin influence matrix.
These obstructions concern absolute single-link influence estimates, not a
physical transfer gap or a gauge-invariant collective estimate.
-/
import UnifiedTheory.Clay.YangMills.SU2HaarCovariance
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2ConditionalInfluence
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt SU2InducedAction SU2HaarCovariance
open scoped Quaternion RealInnerProductSpace

/-- The radial mean written without a special-function representation. -/
theorem radial_mean (β r : ℝ) (hr : 0 ≤ r) :
    tiltMean β (r • (1 : ℍ)) 1 = axisMean (2 * β * r) := by
  by_cases hz : r = 0
  · subst r
    simp [tiltMean_zero]
  · rw [tiltMean_rotational]
    simp only [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg hr,
      real_inner_smul_left, real_inner_self_eq_norm_sq, one_pow, mul_one]
    exact mul_div_cancel_right₀ _ hz

/-- At a perpendicular probe, only the tangent of the staple path contributes. -/
theorem mean_path_perpendicular (β : ℝ) (A : ℝ → ℍ) (B D : ℍ) (t : ℝ)
    (hA : HasDerivAt A D t) (hne : A t ≠ 0) (hperp : ⟪A t, B⟫ = 0) :
    HasDerivAt (fun s => tiltMean β (A s) B)
      (axisMean (2 * β * ‖A t‖) * ⟪D, B⟫ / ‖A t‖) t := by
  have hn : DifferentiableAt ℝ (fun s => ‖A s‖) t := hA.differentiableAt.norm ℝ hne
  have hm : DifferentiableAt ℝ (fun r : ℝ => tiltMean β (r • (1 : ℍ)) 1) ‖A t‖ := by
    simpa only [zero_add] using
      (mean_direction_hasDerivAt β 0 1 1 ‖A t‖).differentiableAt
  have hk : DifferentiableAt ℝ
      (fun s => tiltMean β (‖A s‖ • (1 : ℍ)) 1 / ‖A s‖) t :=
    by
      simpa only [Function.comp_apply, Pi.div_apply] using
        (hm.comp t hn).div hn (norm_ne_zero_iff.mpr hne)
  have hi := hA.inner ℝ (hasDerivAt_const t B)
  have hp := hk.hasDerivAt.mul hi
  have he : (fun s => tiltMean β (‖A s‖ • (1 : ℍ)) 1 / ‖A s‖ * ⟪A s, B⟫) =
      (fun s => tiltMean β (A s) B) := by
    funext s
    rw [radial_mean β _ (norm_nonneg _), tiltMean_rotational]
    ring
  change HasDerivAt (fun s => tiltMean β (‖A s‖ • (1 : ℍ)) 1 / ‖A s‖ * ⟪A s, B⟫) _ t at hp
  rw [he] at hp
  simpa only [hperp, inner_zero_right, zero_add, mul_zero, radial_mean β _ (norm_nonneg _),
    div_mul_eq_mul_div] using hp

def imaginaryUnit : ℍ := ⟨0, 1, 0, 0⟩

theorem imaginaryUnit_norm : ‖imaginaryUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  norm_num [imaginaryUnit, Quaternion.normSq_def]

/-- A unit quaternion path varying one staple while the other five stay equal to one. -/
def alignedStaplePath (t : ℝ) : ℍ :=
  (5 + Real.cos t) • (1 : ℍ) + Real.sin t • imaginaryUnit

/-- This is the ordinary one-parameter subgroup, before adding the other five staples. -/
theorem rotating_staple_norm (t : ℝ) :
    ‖Real.cos t • (1 : ℍ) + Real.sin t • imaginaryUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [Quaternion.normSq_def, imaginaryUnit, ← pow_two, Real.cos_sq_add_sin_sq]

/-- Exact differential response at the aligned six-staple exterior. -/
theorem aligned_mean_hasDerivAt (β : ℝ) :
    HasDerivAt (fun t => tiltMean β (alignedStaplePath t) imaginaryUnit)
      (axisMean (12 * β) / 6) 0 := by
  have hp : HasDerivAt alignedStaplePath imaginaryUnit 0 := by
    convert (((Real.hasDerivAt_cos 0).const_add 5).smul_const (1 : ℍ)).add
      ((Real.hasDerivAt_sin 0).smul_const (imaginaryUnit : ℍ)) using 1
    simp
  have h0 : alignedStaplePath 0 = (6 : ℝ) • (1 : ℍ) := by norm_num [alignedStaplePath]
  have hne : alignedStaplePath 0 ≠ 0 := by rw [h0]; simp
  have hperp : ⟪alignedStaplePath 0, imaginaryUnit⟫ = 0 := by
    rw [h0]
    simp [Quaternion.inner_def, imaginaryUnit]
  have h := mean_path_perpendicular β alignedStaplePath imaginaryUnit imaginaryUnit 0 hp hne hperp
  rw [h0] at h
  norm_num [norm_smul, imaginaryUnit_norm] at h ⊢
  have he : 2 * β * 6 = 12 * β := by ring
  simpa only [he] using h

/-- A rigorous lower bound on the tangent of the actual conditional response. -/
theorem aligned_response_lower (β : ℝ) (hβ : 0 < β) :
    1 / 6 - 1 / (48 * β) ≤
      deriv (fun t => tiltMean β (alignedStaplePath t) imaginaryUnit) 0 := by
  rw [(aligned_mean_hasDerivAt β).deriv]
  have h := axis_concentration (κ := 12 * β) (by positivity)
  have he : 3 / (2 * (12 * β)) = 1 / (8 * β) := by ring
  rw [he] at h
  have hh := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 6)
  ring_nf at hh ⊢
  linarith

/-- Eighteen such tangent influences already prevent a row-sum contraction. -/
theorem eighteen_response_not_contracting (β : ℝ) (hβ : 3 / 16 < β) :
    1 < 18 * deriv (fun t => tiltMean β (alignedStaplePath t) imaginaryUnit) 0 := by
  have hb : 0 < β := by linarith
  have h := aligned_response_lower β hb
  have hi : 1 / (48 * β) < 1 / 9 := by
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 9)
    linarith
  linarith

/-- The source probe has Lipschitz constant one for the quaternion chord metric. -/
theorem probe_lipschitz (q q' : ℍ) :
    |⟪q, imaginaryUnit⟫ - ⟪q', imaginaryUnit⟫| ≤ ‖q - q'‖ := by
  rw [← inner_sub_left]
  simpa only [imaginaryUnit_norm, mul_one] using abs_real_inner_le_norm (q - q') imaginaryUnit

/-- A subgroup displacement is no larger than its unit-speed angle. -/
theorem rotating_staple_distance (t : ℝ) :
    ‖Real.cos t • (1 : ℍ) + Real.sin t • imaginaryUnit - 1‖ ≤ |t| := by
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp only [Quaternion.normSq_def']
  suffices h : (Real.cos t - 1) ^ 2 + Real.sin t ^ 2 ≤ t ^ 2 by
    simpa [imaginaryUnit] using h
  have hc : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq t
  have hh := Real.sin_sq_add_cos_sq (t / 2)
  have hb := Real.sin_sq_le_sq (x := t / 2)
  nlinarith

/-- Every local mean-response bound along this actual unit-staple path must pay the tangent. -/
theorem local_response_constant_lower (β C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ,
      |tiltMean β (alignedStaplePath t) imaginaryUnit -
        tiltMean β (alignedStaplePath 0) imaginaryUnit| ≤
          C * ‖Real.cos t • (1 : ℍ) + Real.sin t • imaginaryUnit - 1‖) :
    axisMean (12 * β) / 6 ≤ C := by
  have hlocal : ∀ᶠ t in nhds (0 : ℝ),
      ‖tiltMean β (alignedStaplePath t) imaginaryUnit -
        tiltMean β (alignedStaplePath 0) imaginaryUnit‖ ≤ C * ‖t - 0‖ := by
    filter_upwards with t
    simpa only [Real.norm_eq_abs, sub_zero] using (hbound t).trans
      (mul_le_mul_of_nonneg_left (rotating_staple_distance t) hC)
  have h := (aligned_mean_hasDerivAt β).le_of_lip' hC hlocal
  exact (le_abs_self _).trans h

/-- An eighteen-neighbor row bound cannot contract at the stated weak-coupling values. -/
theorem local_row_not_contracting (β C : ℝ) (hβ : 3 / 16 < β) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ,
      |tiltMean β (alignedStaplePath t) imaginaryUnit -
        tiltMean β (alignedStaplePath 0) imaginaryUnit| ≤
          C * ‖Real.cos t • (1 : ℍ) + Real.sin t • imaginaryUnit - 1‖) :
    1 < 18 * C := by
  have h := eighteen_response_not_contracting β hβ
  rw [(aligned_mean_hasDerivAt β).deriv] at h
  have hc := local_response_constant_lower β C hC hbound
  linarith

/-- All-staple response bound, with its coupling dependence retained. -/
theorem directional_response_bounds (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β) :
    0 ≤ deriv (fun t : ℝ => tiltMean β (A + t • B) B) 0 ∧
      deriv (fun t : ℝ => tiltMean β (A + t • B) B) 0 ≤ 2 * β * ‖B‖ ^ 2 := by
  rw [(mean_direction_hasDerivAt β A B B 0).deriv]
  simp only [zero_smul, add_zero]
  exact ⟨mul_nonneg (by positivity) (covariance_self_nonneg β A B),
    mul_le_mul_of_nonneg_left (covariance_self_le β A B) (by positivity)⟩

/-- On nonzero staples the explicit coupling cancels, but the bound need not be small. -/
theorem directional_response_good (β : ℝ) (A B : ℍ) (hβ : 0 < β) (hA : A ≠ 0) :
    deriv (fun t : ℝ => tiltMean β (A + t • B) B) 0 ≤ 3 * ‖B‖ ^ 2 / ‖A‖ := by
  rw [(mean_direction_hasDerivAt β A B B 0).deriv]
  simp only [zero_smul, add_zero]
  have h := mul_le_mul_of_nonneg_left (covariance_le_inverse_tilt β A B hβ hA)
    (show 0 ≤ 2 * β by positivity)
  have he : 2 * β * (3 * ‖B‖ ^ 2 / (2 * β * ‖A‖)) = 3 * ‖B‖ ^ 2 / ‖A‖ := by
    field_simp
  rwa [he] at h

/-- The radial response is continuous even where the staple vanishes. -/
theorem radial_response_continuous (β : ℝ) :
    Continuous (fun r : ℝ => tiltMean β (r • (1 : ℍ)) 1) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  simpa only [zero_add] using (mean_direction_hasDerivAt β 0 1 1 r).continuousAt

/-- Positivity follows from the actual covariance derivative, not an asymptotic formula. -/
theorem radial_response_nonneg (β r : ℝ) (hβ : 0 ≤ β) (hr : 0 ≤ r) :
    0 ≤ tiltMean β (r • (1 : ℍ)) 1 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => tiltMean β (r • (1 : ℍ)) 1)
      (2 * β * covariance β (s • (1 : ℍ)) 1 1) s := by
    simpa only [zero_add] using mean_direction_hasDerivAt β 0 1 1 s
  have hdpos (s : ℝ) : 0 ≤ deriv (fun r : ℝ => tiltMean β (r • (1 : ℍ)) 1) s := by
    rw [(hd s).deriv]
    exact mul_nonneg (by positivity) (covariance_self_nonneg β _ _)
  have hm := monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) hdpos
  have h := hm hr
  simpa only [zero_smul, tiltMean_zero] using h

/-- A continuous lower proxy for the sum of eighteen tangent responses.
The denominator is clipped only to keep the scalar function regular at zero. -/
def clippedTangentRow (β : ℝ) (A : ℍ) : ℝ :=
  18 * tiltMean β (‖A‖ • (1 : ℍ)) 1 / max 3 ‖A‖

theorem clippedTangentRow_continuous (β : ℝ) : Continuous (clippedTangentRow β) := by
  unfold clippedTangentRow
  exact (continuous_const.mul ((radial_response_continuous β).comp continuous_norm)).div
    (continuous_const.max continuous_norm) (fun _ => ne_of_gt (by positivity))

theorem clippedTangentRow_nonneg (β : ℝ) (A : ℍ) (hβ : 0 ≤ β) :
    0 ≤ clippedTangentRow β A := by
  unfold clippedTangentRow
  exact div_nonneg (mul_nonneg (by norm_num)
    (radial_response_nonneg β _ hβ (norm_nonneg _))) (by positivity)

/-- Every unit direction perpendicular to a nonzero staple has this exact response. -/
theorem perpendicular_response_formula (β : ℝ) (A B : ℍ)
    (hA : A ≠ 0) (hperp : ⟪A, B⟫ = 0) (hB : ‖B‖ = 1) :
    deriv (fun t : ℝ => tiltMean β (A + t • B) B) 0 =
      axisMean (2 * β * ‖A‖) / ‖A‖ := by
  have hp : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have h := mean_path_perpendicular β (fun t => A + t • B) B B 0 hp
    (by simpa using hA) (by simpa using hperp)
  simpa only [zero_smul, add_zero, real_inner_self_eq_norm_sq, hB, one_pow, mul_one] using h.deriv

/-- The regular proxy is bounded by eighteen genuine perpendicular response derivatives. -/
theorem clipped_le_eighteen_perpendicular (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β)
    (hA : A ≠ 0) (hperp : ⟪A, B⟫ = 0) (hB : ‖B‖ = 1) :
    clippedTangentRow β A ≤ 18 * deriv (fun t : ℝ => tiltMean β (A + t • B) B) 0 := by
  rw [perpendicular_response_formula β A B hA hperp hB, clippedTangentRow,
    ← radial_mean β _ (norm_nonneg _), ← mul_div_assoc]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num) (radial_response_nonneg β _ hβ (norm_nonneg _)))
    (norm_pos_iff.mpr hA) (le_max_right _ _)

/-- On ordinary large staples, the eighteen tangent responses stay above one at weak coupling. -/
theorem clippedTangentRow_good (β : ℝ) (A : ℍ) (hβ : 0 < β)
    (hlo : 3 ≤ ‖A‖) (hhi : ‖A‖ ≤ 6) :
    3 - 3 / (2 * β) ≤ clippedTangentRow β A := by
  have hr : 0 < ‖A‖ := by linarith
  rw [clippedTangentRow, max_eq_right hlo, radial_mean β _ (norm_nonneg _)]
  have h := axis_concentration (κ := 2 * β * ‖A‖) (by positivity)
  have hl : 1 / 6 - 1 / (12 * β) ≤ axisMean (2 * β * ‖A‖) / ‖A‖ := by
    apply (le_div_iff₀ hr).mpr
    have he : 3 / (2 * (2 * β * ‖A‖)) ≤ ‖A‖ / (12 * β) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (‖A‖ - 3)]
    have heq : ‖A‖ / (12 * β) = (1 / (12 * β)) * ‖A‖ := by ring
    rw [heq] at he
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 18)
  convert hh using 1 <;> ring

open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonSingleLinkStaples SU2StarEnergy

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- The proxy evaluated on the original Wilson configuration, without replacing its law. -/
def actualClippedRow (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (U : Configuration (Vertex n) Q) : ℝ := clippedTangentRow β (stapleField n x μ U)

omit [Fact (1 < n)] in
theorem actualClippedRow_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (actualClippedRow n x μ β) :=
  (clippedTangentRow_continuous β).comp (stapleField_continuous n x μ)

/-- Rare small staples leave an explicit noncontracting annealed scalar lower bound. -/
theorem actual_annealed_row_lower (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 < β) :
    (3 - 3 / (2 * β)) *
      (1 - (wilsonLaw n Q character β 2).real (badEvent n x μ 3)) ≤
        ∫ U, actualClippedRow n x μ β U ∂wilsonLaw n Q character β 2 := by
  classical
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  let C := 3 - 3 / (2 * β)
  have hs := badEvent_measurable n x μ 3
  have hp (U : Configuration (Vertex n) Q) :
      (badEvent n x μ 3)ᶜ.indicator (fun _ => C) U ≤ actualClippedRow n x μ β U := by
    by_cases hU : U ∈ badEvent n x μ 3
    · rw [Set.indicator_of_notMem (by simpa using hU)]
      exact clippedTangentRow_nonneg β _ hβ.le
    · rw [Set.indicator_of_mem (by simpa using hU)]
      have hlo : 3 ≤ ‖stapleField n x μ U‖ := le_of_lt (lt_of_not_ge hU)
      exact clippedTangentRow_good β _ hβ hlo (stapleField_norm_le_six n x μ U)
  have hi := (actualClippedRow_continuous n x μ β).integrable_of_hasCompactSupport
    (μ := ν) (HasCompactSupport.of_compactSpace _)
  have h := integral_mono ((integrable_const C).indicator hs.compl) hi hp
  rw [integral_indicator_const _ hs.compl, measureReal_compl hs, probReal_univ] at h
  simpa only [C, ν, smul_eq_mul, mul_comm] using h

/-- Along every diverging coupling and arbitrary changing finite volumes,
the explicit lower envelope tends to three. No physical running-coupling identification is used. -/
theorem annealed_lower_envelope_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (N i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => (3 - 3 / (2 * β i)) *
      (1 - (wilsonLaw (N i) Q character (β i) 2).real
        (badEvent (N i) (x i) (μ i) 3))) l (nhds 3) := by
  have hp := WilsonBadStapleProbability.bad_probability_tendsto N β hβ x μ 3 (by norm_num)
  have hb0 : Filter.Tendsto (fun i => (3 : ℝ) / (2 * β i)) l (nhds 0) :=
    tendsto_const_nhds.div_atTop (hβ.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hb : Filter.Tendsto (fun i => (3 : ℝ) - 3 / (2 * β i)) l (nhds 3) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hb0
  have h1 : Filter.Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  simpa only [sub_zero, mul_one] using hb.mul (h1.sub hp)

/-- Even the original-law average of this lower proxy eventually exceeds one. -/
theorem actual_annealed_row_eventually_gt_one {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (N i)) (μ : ι → Fin 4) :
    ∀ᶠ i in l, 1 < ∫ U, actualClippedRow (N i) (x i) (μ i) (β i) U
      ∂wilsonLaw (N i) Q character (β i) 2 := by
  have hl := (annealed_lower_envelope_tendsto N β hβ x μ).eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ) < 3))
  filter_upwards [hl, hβ.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with i hi hbi
  exact hi.trans_le (actual_annealed_row_lower (N i) (x i) (μ i) (β i) hbi)

end
end UnifiedTheory.Clay.YangMills.SU2ConditionalInfluence
