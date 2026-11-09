/-
Exact one-link induced Wilson actions and their source derivatives.
The Haar partition is the actual quaternion Haar integral. Its directional
Hessian is a connected covariance, and the zero-staple curvature is computed
from the proved Haar semicircle law. Source-tilted Wilson fibers are identified
without an assumed affine-action representation or covariance estimate.

These are finite-cutoff identities. The zero-staple obstruction concerns the
whole quaternion source-vector domain; no probability of such exteriors or
contraction under repeated elimination is asserted here.
-/
import UnifiedTheory.Clay.YangMills.SU2SemicircleSlice
import UnifiedTheory.Clay.YangMills.SU2WilsonConditionalSource
import UnifiedTheory.Clay.YangMills.CompactGibbsSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2InducedAction

noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt
open scoped Quaternion RealInnerProductSpace

def potential (β : ℝ) (A : ℍ) : ℝ := -Real.log (tiltPartition β A)
def baseAction (β : ℝ) (A : ℍ) (q : UnitQuaternion) : ℝ := -(2 * β*⟪(q : ℍ), A⟫)
def insertion (β : ℝ) (B : ℍ) (q : UnitQuaternion) : ℝ := 2 * β*⟪(q : ℍ), B⟫
def covariance (β : ℝ) (A B C : ℍ) : ℝ :=
  (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ * ⟪(q : ℍ), C⟫ ∂tiltLaw β A) -
    tiltMean β A B * tiltMean β A C

theorem baseAction_continuous (β : ℝ) (A : ℍ) : Continuous (baseAction β A) := by
  unfold baseAction
  fun_prop

theorem insertion_continuous (β : ℝ) (B : ℍ) : Continuous (insertion β B) := by
  unfold insertion
  fun_prop

theorem source_weight (β : ℝ) (A B : ℍ) (t : ℝ) (q : UnitQuaternion) :
    CompactGibbsSource.weight (baseAction β A) (insertion β B) t q =
      tiltWeight β (A + t • B) q := by
  unfold CompactGibbsSource.weight CompactGibbsSource.action baseAction insertion tiltWeight
  rw [inner_add_right, real_inner_smul_right]
  congr 1
  ring

theorem source_partition (β : ℝ) (A B : ℍ) (t : ℝ) :
    CompactGibbsSource.partition haar (baseAction β A) (insertion β B) t =
      tiltPartition β (A + t • B) := by
  unfold CompactGibbsSource.partition tiltPartition
  simp_rw [source_weight]

theorem source_law (β : ℝ) (A B : ℍ) (t : ℝ) :
    CompactGibbsContinuity.law haar
      (CompactGibbsSource.action (baseAction β A) (insertion β B) t) =
      tiltLaw β (A + t • B) := by
  unfold CompactGibbsContinuity.law tiltLaw
  congr 1
  funext q
  exact source_weight β A B t q

theorem source_expectation (β : ℝ) (A B C : ℍ) (t : ℝ) :
    CompactGibbsSource.expectation haar (baseAction β A) (insertion β B)
      (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫) t = tiltMean β (A + t • B) C := by
  unfold CompactGibbsSource.expectation
  rw [source_law, tiltLaw_inner_mean]

theorem source_covariance (β : ℝ) (A B C D : ℍ) (t : ℝ) :
    CompactGibbsSource.covariance haar (baseAction β A) (insertion β B)
      (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫) (fun q : UnitQuaternion => ⟪(q : ℍ), D⟫) t =
      covariance β (A + t • B) C D := by
  unfold CompactGibbsSource.covariance covariance
  rw [source_expectation, source_expectation]
  unfold CompactGibbsSource.expectation
  rw [source_law]

theorem source_insert_expectation (β : ℝ) (A B : ℍ) (t : ℝ) :
    CompactGibbsSource.expectation haar (baseAction β A) (insertion β B)
      (insertion β B) t = 2 * β*tiltMean β (A + t • B) B := by
  unfold CompactGibbsSource.expectation
  rw [source_law]
  unfold insertion
  rw [integral_const_mul, tiltLaw_inner_mean]

theorem source_insert_covariance (β : ℝ) (A B C : ℍ) (t : ℝ) :
    CompactGibbsSource.covariance haar (baseAction β A) (insertion β B)
      (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫) (insertion β B) t =
      2 * β*covariance β (A + t • B) C B := by
  unfold CompactGibbsSource.covariance covariance
  rw [source_expectation, source_insert_expectation]
  unfold CompactGibbsSource.expectation
  rw [source_law]
  have he : (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫ * insertion β B q) =
      (fun q : UnitQuaternion => (2 * β)*(⟪(q : ℍ), C⟫ * ⟪(q : ℍ), B⟫)) := by
    funext q
    unfold insertion
    ring
  rw [he, integral_const_mul]
  ring

theorem mean_direction_hasDerivAt (β : ℝ) (A B C : ℍ) (t : ℝ) :
    HasDerivAt (fun s => tiltMean β (A + s • B) C)
      (2 * β*covariance β (A + t • B) C B) t := by
  have h := CompactGibbsSource.expectation_hasDerivAt haar (baseAction β A) (insertion β B)
    (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫) (baseAction_continuous β A)
    (insertion_continuous β B) (continuous_subtype_val.inner continuous_const) t
  simp only [source_insert_covariance] at h
  have he : CompactGibbsSource.expectation haar (baseAction β A) (insertion β B)
      (fun q : UnitQuaternion => ⟪(q : ℍ), C⟫) =
      (fun s => tiltMean β (A + s • B) C) := funext (source_expectation β A B C)
  rw [he] at h
  exact h

theorem potential_direction_hasDerivAt (β : ℝ) (A B : ℍ) (t : ℝ) :
    HasDerivAt (fun s => potential β (A + s • B))
      (-(2 * β*tiltMean β (A + t • B) B)) t := by
  have h := (CompactGibbsSource.log_partition_hasDerivAt haar (baseAction β A)
    (insertion β B) (baseAction_continuous β A) (insertion_continuous β B) t).neg
  simpa only [source_partition, source_insert_expectation, potential] using h

theorem potential_direction_second (β : ℝ) (A B : ℍ) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun u => potential β (A + u • B)) s)
      (-(4 * β ^ 2*covariance β (A + t • B) B B)) t := by
  have he : (fun s : ℝ => deriv (fun u : ℝ => potential β (A + u • B)) s) =
      (fun s => -(2 * β*tiltMean β (A + s • B) B)) := by
    funext s
    exact (potential_direction_hasDerivAt β A B s).deriv
  rw [he]
  convert ((mean_direction_hasDerivAt β A B B t).const_mul (2 * β)).neg using 1
  ring

theorem covariance_self_nonneg (β : ℝ) (A B : ℍ) : 0 ≤ covariance β A B B := by
  have h := CompactGibbsSource.covariance_self_nonneg haar (baseAction β A) (insertion β B)
    (fun q : UnitQuaternion => ⟪(q : ℍ), B⟫) (baseAction_continuous β A)
    (insertion_continuous β B) (continuous_subtype_val.inner continuous_const) 0
  simpa only [source_covariance, zero_smul, add_zero] using h

theorem covariance_self_le (β : ℝ) (A B : ℍ) : covariance β A B B ≤ ‖B‖ ^ 2 := by
  letI := tiltLaw_probability β A
  have hi : Integrable (fun q : UnitQuaternion => ⟪(q : ℍ), B⟫ * ⟪(q : ℍ), B⟫) (tiltLaw β A) :=
    ((continuous_subtype_val.inner continuous_const).mul
      (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hp (q : UnitQuaternion) : ⟪(q : ℍ), B⟫ * ⟪(q : ℍ), B⟫ ≤ ‖B‖ ^ 2 := by
    have h := abs_real_inner_le_norm (q : ℍ) B
    rw [CStarRing.norm_of_mem_unitary q.property, one_mul] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg B)).2 h
    rw [sq_abs] at hs
    simpa only [pow_two] using hs
  have hb := integral_mono hi (integrable_const (‖B‖ ^ 2)) hp
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] at hb
  unfold covariance
  nlinarith [sq_nonneg (tiltMean β A B)]

theorem potential_curvature_bounds (β : ℝ) (A B : ℍ) (t : ℝ) :
    -(4 * β ^ 2*‖B‖ ^ 2) ≤ deriv (fun s => deriv (fun u => potential β (A + u • B)) s) t ∧
      deriv (fun s => deriv (fun u => potential β (A + u • B)) s) t ≤ 0 := by
  rw [(potential_direction_second β A B t).deriv]
  constructor
  · have h := mul_le_mul_of_nonneg_left (covariance_self_le β (A + t • B) B)
      (show 0 ≤ 4 * β ^ 2 by positivity)
    linarith
  · have h := mul_nonneg (show 0 ≤ 4 * β ^ 2 by positivity)
      (covariance_self_nonneg β (A + t • B) B)
    linarith

theorem haar_real_square : (∫ q : UnitQuaternion, (q : ℍ).re ^ 2 ∂haar) = 1/4 := by
  rw [SU2SemicircleSlice.haar_semicircle (fun t => t ^ 2) (by fun_prop)]
  have he : SU2ScalarTilt.semicircleIntegral 0 (fun t => t ^ 2) = Real.pi/8 := by
    have h := SU2SemicircleSlice.angular_cosine (fun t => t ^ 2) (by fun_prop)
    have hs : (∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ 2*Real.cos θ ^ 2) = Real.pi/8 := by
      rw [integral_sin_sq_mul_cos_sq]
      have hz : Real.sin (4*Real.pi) = 0 := by
        simpa using Real.sin_nat_mul_pi 4
      rw [hz]
      norm_num
    rw [hs] at h
    simpa [SU2ScalarTilt.semicircleIntegral, SU2ScalarTilt.weight] using h.symm
  rw [he]
  field_simp [Real.pi_ne_zero]
  norm_num

theorem haar_inner_square (B : ℍ) :
    (∫ q : UnitQuaternion, ⟪(q : ℍ), B⟫ ^ 2 ∂haar) = ‖B‖ ^ 2/4 := by
  by_cases hB : B = 0
  · subst B
    simp
  · calc
      _ = ∫ q : UnitQuaternion, ⟪((orientation B hB * q : UnitQuaternion):ℍ), B⟫ ^ 2 ∂haar :=
        (integral_mul_left_eq_self (fun q : UnitQuaternion => ⟪(q : ℍ), B⟫ ^ 2)
          (orientation B hB)).symm
      _ = ∫ q : UnitQuaternion, ‖B‖ ^ 2*(q : ℍ).re ^ 2 ∂haar := by
        apply integral_congr_ae
        filter_upwards with q
        rw [oriented_inner]
        ring
      _ = _ := by rw [integral_const_mul, haar_real_square]; ring

theorem tiltLaw_zero (β : ℝ) : tiltLaw β 0 = haar := by
  simp [tiltLaw, tiltWeight, LocalGibbsComparison.weightedLaw]

theorem covariance_zero (β : ℝ) (B : ℍ) : covariance β 0 B B = ‖B‖ ^ 2/4 := by
  unfold covariance
  rw [tiltLaw_zero, tiltMean_zero]
  simp only [← pow_two, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  exact haar_inner_square B

theorem potential_curvature_zero (β : ℝ) (B : ℍ) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => potential β (u • B)) s) 0 = -β ^ 2*‖B‖ ^ 2 := by
  have h := (potential_direction_second β 0 B 0).deriv
  simp only [zero_add, zero_smul, covariance_zero] at h
  rw [h]
  ring


/-- The global curvature cannot be uniformly bounded as the coupling increases. -/
theorem no_uniform_curvature_bound :
    ¬ ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β →
      |deriv (fun s : ℝ => deriv (fun u : ℝ => potential β (u • (1 : ℍ))) s) 0| ≤ C := by
  rintro ⟨C, hC⟩
  have hb : 1 ≤ |C| + 2 := by nlinarith [abs_nonneg C]
  have h := hC (|C| + 2) hb
  rw [potential_curvature_zero] at h
  simp only [norm_one, one_pow, mul_one, abs_neg, abs_pow] at h
  rw [abs_of_nonneg (by positivity : 0 ≤ |C| + 2)] at h
  have hc := le_abs_self C
  have ha := abs_nonneg C
  nlinarith [sq_nonneg C]


theorem mean_neg_probe (β : ℝ) (A B : ℍ) : tiltMean β A (-B) = -tiltMean β A B := by
  simp only [tiltMean_rotational, inner_neg_right]
  ring

theorem covariance_neg_right (β : ℝ) (A B C : ℍ) :
    covariance β A B (-C) = -covariance β A B C := by
  unfold covariance
  simp only [inner_neg_right, mul_neg, integral_neg, mean_neg_probe]
  ring

/-- A source-dependent effective action has an actual normalized first response. -/
theorem affine_source_first (C D : ℝ) (V B : ℍ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => C - s * D + potential 1 (V - s • B))
      (-D + 2 * tiltMean 1 (V - t • B) B) t := by
  have hlin : HasDerivAt (fun s : ℝ => C - s * D) (-D) t := by
    simpa using (hasDerivAt_const t C).sub ((hasDerivAt_id t).mul_const D)
  have hp := potential_direction_hasDerivAt 1 V (-B) t
  convert hlin.add hp using 1 <;>
    simp only [smul_neg, ← sub_eq_add_neg, mean_neg_probe, mul_one, mul_neg, neg_neg]
  rfl

/-- The second response is precisely minus the conditional source variance. -/
theorem affine_source_second (C D : ℝ) (V B : ℍ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => deriv (fun u : ℝ => C - u * D + potential 1 (V - u • B)) s)
      (-4 * covariance 1 (V - t • B) B B) t := by
  have he :
      (fun s : ℝ => deriv (fun u : ℝ => C - u * D + potential 1 (V - u • B)) s) =
      (fun s : ℝ => -D + 2 * tiltMean 1 (V - s • B) B) := by
    funext s
    exact (affine_source_first C D V B s).deriv
  rw [he]
  have hm := (mean_direction_hasDerivAt 1 V (-B) B t).const_mul 2
  convert (hasDerivAt_const t (-D)).add hm using 1 <;>
    simp only [smul_neg, ← sub_eq_add_neg, covariance_neg_right, mul_one, zero_add] <;>
      first | rfl | ring

open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The actual fiber partition, including the full exterior action constant. -/
theorem wilson_fiberMass (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    GibbsMarginalTower.fiberMass haar (SU2WilsonConditionalSource.splitAction n x μ β) r =
      Real.exp (-β * exteriorSourceConstant n x μ r (fun _ => 1)) *
        tiltPartition β (exteriorStaple n x μ r) := by
  unfold GibbsMarginalTower.fiberMass tiltPartition
  have he (q : Q) : Real.exp (-SU2WilsonConditionalSource.splitAction n x μ β (r, q)) =
      Real.exp (-β * exteriorSourceConstant n x μ r (fun _ => 1)) *
        tiltWeight β (exteriorStaple n x μ r) q := by
    rw [SU2WilsonConditionalSource.splitAction, action_assemble]
    unfold tiltWeight
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- Exact one-link induced action for the original Wilson model. -/
theorem wilson_effectiveAction (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    GibbsMarginalTower.effectiveAction haar (SU2WilsonConditionalSource.splitAction n x μ β) r =
      β * exteriorSourceConstant n x μ r (fun _ => 1) +
        potential β (exteriorStaple n x μ r) := by
  rw [GibbsMarginalTower.effectiveAction, wilson_fiberMass,
    Real.log_mul (Real.exp_ne_zero _) (tiltPartition_pos _ _).ne', Real.log_exp]
  unfold potential
  ring

/-- The nonlinear interaction is the actual radial Haar partition, with no supplied density law. -/
theorem wilson_effectiveAction_radial (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    GibbsMarginalTower.effectiveAction haar (SU2WilsonConditionalSource.splitAction n x μ β) r =
      β * exteriorSourceConstant n x μ r (fun _ => 1) -
        Real.log (axisPartition (2 * β * ‖exteriorStaple n x μ r‖)) := by
  rw [wilson_effectiveAction, potential, tiltPartition_radial]
  rfl

/-- A real source tilt produces a shifted actual staple, even when β=0. -/
theorem wilson_sourced_effectiveAction (x : Vertex n) (μ : Fin 4) (β t : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    GibbsMarginalTower.effectiveAction haar
      (fun z => SU2WilsonConditionalSource.splitAction n x μ β z -
        t * SU2WilsonConditionalSource.splitSource n x μ f z) r =
      β * exteriorSourceConstant n x μ r (fun _ => 1) -
        t * exteriorSourceConstant n x μ r f +
        potential 1 (β • exteriorStaple n x μ r -
          t • exteriorWeightedStaple n x μ r f) := by
  let C := β * exteriorSourceConstant n x μ r (fun _ => 1) -
    t * exteriorSourceConstant n x μ r f
  let V := β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f
  have he (q : Q) :
      Real.exp (-(SU2WilsonConditionalSource.splitAction n x μ β (r, q) -
        t * SU2WilsonConditionalSource.splitSource n x μ f (r, q))) =
      Real.exp (-C) * tiltWeight 1 V q := by
    rw [SU2WilsonConditionalSource.splitAction, action_assemble,
      SU2WilsonConditionalSource.splitSource, source_assemble]
    unfold tiltWeight V C
    rw [← Real.exp_add, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    congr 1
    ring
  change -Real.log (∫ q, Real.exp (-(SU2WilsonConditionalSource.splitAction n x μ β (r, q) -
    t * SU2WilsonConditionalSource.splitSource n x μ f (r, q))) ∂haar) = C + potential 1 V
  simp_rw [he]
  rw [integral_const_mul]
  change -Real.log (Real.exp (-C) * tiltPartition 1 V) = C + potential 1 V
  rw [Real.log_mul (Real.exp_ne_zero _) (tiltPartition_pos _ _).ne', Real.log_exp]
  unfold potential
  ring


/-- Source curvature of the full Wilson fiber after an actual one-link integration. -/
theorem wilson_sourced_curvature (x : Vertex n) (μ : Fin 4) (β t : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => GibbsMarginalTower.effectiveAction haar
      (fun z => SU2WilsonConditionalSource.splitAction n x μ β z -
        u * SU2WilsonConditionalSource.splitSource n x μ f z) r) s) t =
      -4 * covariance 1
        (β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f)
        (exteriorWeightedStaple n x μ r f) (exteriorWeightedStaple n x μ r f) := by
  have he : (fun u : ℝ => GibbsMarginalTower.effectiveAction haar
      (fun z => SU2WilsonConditionalSource.splitAction n x μ β z -
        u * SU2WilsonConditionalSource.splitSource n x μ f z) r) =
      (fun u : ℝ => β * exteriorSourceConstant n x μ r (fun _ => 1) -
        u * exteriorSourceConstant n x μ r f +
        potential 1 (β • exteriorStaple n x μ r -
          u • exteriorWeightedStaple n x μ r f)) := by
    funext u
    exact wilson_sourced_effectiveAction n x μ β u f r
  rw [he]
  exact (affine_source_second _ _ _ _ _).deriv

/-- A genuine finite-cutoff source bound; its norm is that of the actual weighted staple. -/
theorem wilson_sourced_curvature_bounds (x : Vertex n) (μ : Fin 4) (β t : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    let H := fun u : ℝ => GibbsMarginalTower.effectiveAction haar
      (fun z => SU2WilsonConditionalSource.splitAction n x μ β z -
        u * SU2WilsonConditionalSource.splitSource n x μ f z) r;
    -4 * ‖exteriorWeightedStaple n x μ r f‖ ^ 2 ≤ deriv (fun s => deriv H s) t ∧
      deriv (fun s => deriv H s) t ≤ 0 := by
  dsimp only []
  rw [wilson_sourced_curvature]
  constructor
  · have h := covariance_self_le 1
      (β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f)
      (exteriorWeightedStaple n x μ r f)
    linarith
  · have h := covariance_self_nonneg 1
      (β • exteriorStaple n x μ r - t • exteriorWeightedStaple n x μ r f)
      (exteriorWeightedStaple n x μ r f)
    linarith

end
end UnifiedTheory.Clay.YangMills.SU2InducedAction
