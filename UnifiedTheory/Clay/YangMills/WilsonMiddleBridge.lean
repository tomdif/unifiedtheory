/- Exact middle-slice conditioning of the variance pair law. The middle
conditional has a known Wilson action and no ground-state factor. The
correlated endpoint marginal retains its actual ground factors. -/
import UnifiedTheory.Clay.YangMills.WilsonVariancePair

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMiddleBridge
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonVariancePair WilsonVarianceProfile WilsonGroundHeatBath
open CompactDensityEntropy WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]

def weight (β : ℝ) (v w u : Slice n) : ℝ :=
  rawKernel character β 2 u v * rawKernel character β 2 u w

theorem weight_pos (β : ℝ) (v w u : Slice n) : 0 < weight n β v w u :=
  mul_pos (rawKernel_pos _ _ _ _ _) (rawKernel_pos _ _ _ _ _)

theorem weight_continuous (β : ℝ) (v w : Slice n) : Continuous (weight n β v w) := by
  have hk := rawKernel_continuous character character_continuous β 2 (n := n)
  exact (hk.comp (f := fun u : Slice n => (u,v)) (continuous_id.prodMk continuous_const)).mul
    (hk.comp (f := fun u : Slice n => (u,w)) (continuous_id.prodMk continuous_const))

def action (β : ℝ) (v w u : Slice n) : ℝ :=
  β*potential character 2 u + β*kineticAction character 2 u v + β*kineticAction character 2 u w

theorem action_continuous (β : ℝ) (v w : Slice n) : Continuous (action n β v w) := by
  have hc := character_continuous
  unfold action potential kineticAction spatialHolonomy
  fun_prop

theorem action_eq_input (β : ℝ) (v w u : Slice n) :
    action n β v w u = WilsonSymmetricLinkChange.inputAction n β u v +
      WilsonSymmetricLinkChange.inputAction n β u w := by
  unfold action WilsonSymmetricLinkChange.inputAction
  ring

/-- The middle action has a collective second-difference budget for every endpoint pair. -/
theorem action_second_bound (β : ℝ) (hβ : 0 ≤ β) (q v w u : Slice n) :
    action n β v w (q*u)+action n β v w (q⁻¹*u)-2*action n β v w u ≤
      36*β*WilsonJointRotation.cost n q := by
  have hv := WilsonJointRotation.inputAction_second_bound n β hβ q u v
  have hw := WilsonJointRotation.inputAction_second_bound n β hβ q u w
  simp only [action_eq_input]
  nlinarith

/-- Every middle-dependent term is explicit; there is no log-ground term. -/
theorem weight_action (β : ℝ) (v w u : Slice n) :
    weight n β v w u = spatialWeight character β 2 v * spatialWeight character β 2 w *
      Real.exp (-action n β v w u) := by
  unfold weight rawKernel spatialWeight kineticWeight action
  simp only [← Real.exp_add]
  congr 1
  ring

def mass (β : ℝ) (v w : Slice n) : ℝ :=
  ∫ u, weight n β v w u ∂WilsonSlabOperator.measure n

theorem mass_pos (β : ℝ) (v w : Slice n) : 0 < mass n β v w :=
  PositiveKernelRatio.profile_integral_pos (WilsonSlabOperator.measure n)
    ⟨weight n β v w, weight_continuous n β v w⟩ (weight_pos n β v w)

def law (β : ℝ) (v w : Slice n) : Measure (Slice n) :=
  LocalGibbsComparison.weightedLaw (WilsonSlabOperator.measure n) (weight n β v w)

theorem law_probability (β : ℝ) (v w : Slice n) : IsProbabilityMeasure (law n β v w) :=
  LocalGibbsComparison.weightedLaw_probability _ _ (weight_continuous n β v w).measurable
    (continuous_integrable _ _ (weight_continuous n β v w))
    (fun u => (weight_pos n β v w u).le) (mass_pos n β v w)

theorem law_integral (β : ℝ) (v w : Slice n) (H : Slice n → ℝ) :
    (∫ u, H u ∂law n β v w) =
      (∫ u, weight n β v w u*H u ∂WilsonSlabOperator.measure n)/mass n β v w :=
  LocalGibbsComparison.weighted_integral _ _ (weight_continuous n β v w).measurable
    (fun u => (weight_pos n β v w u).le) (mass_pos n β v w) H

def endpointWeight (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) : ℝ :=
  ground n β hβ v*ground n β hβ w/‖transfer n β‖^2 * mass n β v w

theorem endpointWeight_pos (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) :
    0 < endpointWeight n β hβ v w :=
  mul_pos (div_pos (mul_pos (ground_pos n β hβ v) (ground_pos n β hβ w))
    (sq_pos_of_pos (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1))
    (mass_pos n β v w)

/-- Exact conditional integral, including the correlated endpoint marginal. -/
theorem fiber_integral (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) (H : Slice n → ℝ) :
    (∫ u, pairWeight n β hβ u v w*H u ∂WilsonSlabOperator.measure n) =
      endpointWeight n β hβ v w*(∫ u, H u ∂law n β v w) := by
  rw [law_integral]
  have he : (∫ u, pairWeight n β hβ u v w*H u ∂WilsonSlabOperator.measure n) =
      (ground n β hβ v*ground n β hβ w/‖transfer n β‖^2)*
        (∫ u, weight n β v w u*H u ∂WilsonSlabOperator.measure n) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    unfold pairWeight weight
    ring
  rw [he]
  unfold endpointWeight
  field_simp [(mass_pos n β v w).ne']

theorem endpointWeight_integral (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) :
    endpointWeight n β hβ v w =
      ∫ u, pairWeight n β hβ u v w ∂WilsonSlabOperator.measure n := by
  letI := law_probability n β v w
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using
    (fiber_integral n β hβ v w (fun _ => 1)).symm

/-- The endpoint weight is the actual normalized marginal, not a product replacement. -/
theorem endpointWeight_mass (β : ℝ) (hβ : 0 ≤ β) :
    (∫ z : Slice n × Slice n, endpointWeight n β hβ z.1 z.2
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) = 1 := by
  have hi := continuous_integrable
    ((WilsonSlabOperator.measure n).prod
      ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))) _
    (pairWeight_continuous n β hβ)
  have hs := integral_integral_swap
    (f := fun u (z : Slice n × Slice n) => pairWeight n β hβ u z.1 z.2) hi
  have hm (u : Slice n) : (∫ z : Slice n × Slice n, pairWeight n β hβ u z.1 z.2
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) =
      (ground n β hβ u)^2 := by
    have hc : Continuous (fun z : Slice n × Slice n => pairWeight n β hβ u z.1 z.2) :=
      (pairWeight_continuous n β hβ).comp
        (f := fun z : Slice n × Slice n => (u,z)) (continuous_const.prodMk continuous_id)
    rw [integral_prod _ (continuous_integrable _ _ hc)]
    exact pairWeight_mass n β hβ u
  simp_rw [endpointWeight_integral]
  rw [← hs]
  simp_rw [hm]
  exact ground_square_integral n β hβ

/-- Source-weighted middle observables disintegrate under the exact bridge law. -/
theorem weighted_profile (β : ℝ) (hβ : 0 ≤ β) (f H : C(Slice n, ℝ)) :
    (∫ u, (profile n β hβ f u)^2*H u ∂groundLaw n β hβ) =
      (∫ z : Slice n × Slice n, endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2*
        (∫ u, H u ∂law n β z.1 z.2)
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))/2 := by
  let G := fun p : Slice n × (Slice n × Slice n) =>
    pairWeight n β hβ p.1 p.2.1 p.2.2*(f p.2.1-f p.2.2)^2*H p.1
  have hG : Continuous G := ((pairWeight_continuous n β hβ).mul
    (((f.continuous.comp (f := fun p : Slice n × (Slice n × Slice n) => p.2.1)
      (by fun_prop)).sub (f.continuous.comp
      (f := fun p : Slice n × (Slice n × Slice n) => p.2.2) (by fun_prop))).pow 2)).mul
    (H.continuous.comp continuous_fst)
  have hi (u : Slice n) : (∫ z : Slice n × Slice n, G (u,z)
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) =
      2*((ground n β hβ u)^2*(profile n β hβ f u)^2*H u) := by
    dsimp only [G]
    rw [integral_mul_const]
    have hp := amplitude_pair n β hβ u f
    have hc : Continuous (fun z : Slice n × Slice n =>
        pairWeight n β hβ u z.1 z.2*(f z.1-f z.2)^2) :=
      (((pairWeight_continuous n β hβ).comp
        (f := fun z : Slice n × Slice n => (u,z))
          (continuous_const.prodMk continuous_id))).mul (by fun_prop)
    rw [integral_prod _ (continuous_integrable _ _ hc)]
    have he : (∫ v, ∫ w, pairWeight n β hβ u v w*(f v-f w)^2
        ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n) =
        2*(ground n β hβ u)^2*(profile n β hβ f u)^2 := by nlinarith [hp]
    rw [he]
    ring
  have hf (z : Slice n × Slice n) : (∫ u, G (u,z) ∂WilsonSlabOperator.measure n) =
      endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2*(∫ u, H u ∂law n β z.1 z.2) := by
    calc
      _ = (∫ u, pairWeight n β hβ u z.1 z.2*H u ∂WilsonSlabOperator.measure n)*
          (f z.1-f z.2)^2 := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with u
        dsimp [G]
        ring
      _ = _ := by rw [fiber_integral]; ring
  have hs := integral_integral_swap (f := fun u z => G (u,z)) (continuous_integrable
    ((WilsonSlabOperator.measure n).prod
      ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))) _ hG)
  change (∫ u, ∫ z, G (u,z) ∂(WilsonSlabOperator.measure n).prod
    (WilsonSlabOperator.measure n) ∂WilsonSlabOperator.measure n) =
      (∫ z, ∫ u, G (u,z) ∂WilsonSlabOperator.measure n
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) at hs
  simp_rw [hi, hf] at hs
  rw [integral_const_mul] at hs
  rw [groundLaw, GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n)
    (ground n β hβ) (ground n β hβ).continuous]
  have he : (∫ u, (ground n β hβ u)^2*((profile n β hβ f u)^2*H u)
      ∂WilsonSlabOperator.measure n) =
      ∫ u, (ground n β hβ u)^2*(profile n β hβ f u)^2*H u
        ∂WilsonSlabOperator.measure n := by
    apply integral_congr_ae
    filter_upwards with u
    ring
  rw [he]
  linarith

/-- The source-weighted endpoint mass is exactly the actual variance loss. -/
theorem loss_pair (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    WilsonPhysicalVariance.loss n β hβ f =
      (∫ z : Slice n × Slice n, endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))/2 := by
  have hm (v w : Slice n) : (∫ _u : Slice n, (1 : ℝ) ∂law n β v w) = 1 := by
    letI := law_probability n β v w
    simp
  have h := weighted_profile n β hβ f (1 : C(Slice n, ℝ))
  simp only [ContinuousMap.one_apply, mul_one, hm] at h
  change WilsonWeightedEntropy.mass n β hβ (profile n β hβ f) = _ at h
  rw [profile_mass] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonMiddleBridge
