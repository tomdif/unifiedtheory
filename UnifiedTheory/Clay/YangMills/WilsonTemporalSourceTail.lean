/- Source-sensitive temporal-defect suppression. The Haar insertion floor
controls a product of absolute endpoint sources. The exact time increment
pays for conversion to a squared source on one endpoint. On physical
observables the increment is bounded by the actual variance loss. -/
import UnifiedTheory.Clay.YangMills.WilsonTemporalDefectMoment
import UnifiedTheory.Clay.YangMills.WilsonPhysicalEnergyLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTemporalSourceTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonGroundLocalComparison WilsonTemporalCutFloor WilsonTemporalDefectMoment
open WilsonHighFieldDecay WilsonHighFieldReduction WilsonPhysicalVariance WilsonGroundHeatBath
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]

theorem law_pairing (β : ℝ) (hβ : 0 ≤ β) (f g : C(Slice n, ℝ)) :
    (∫ z, f z.1 * g z.2 ∂law n β hβ) = pairing n β hβ f (step n β hβ g) := by
  rw [law_integral, pairing_raw]
  have hi : Integrable (fun z : Slice n × Slice n =>
      (rawKernel character β 2 z.1 z.2 * ground n β hβ z.1 * ground n β hβ z.2 /
        ‖transfer n β‖) * (f z.1 * g z.2))
      ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((((rawKernel_continuous character character_continuous β 2).mul
      ((ground n β hβ).continuous.comp continuous_fst)).mul
      ((ground n β hβ).continuous.comp continuous_snd)).div_const _).mul
      ((f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with u
  apply integral_congr_ae
  filter_upwards with v
  unfold rawTransition
  field_simp [(ground_pos n β hβ u).ne']

theorem pairing_le_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    pairing n β hβ f (step n β hβ f) ≤ mass n β hβ f := by
  have hc := pairing_sq n β hβ f (step n β hβ f)
  have hs := mass_step_le n β hβ f
  have hm := mass_nonneg n β hβ f
  have hp := mass_nonneg n β hβ (step n β hβ f)
  nlinarith

theorem raw_dirichlet (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    GroundStateDirichlet.dirichlet (WilsonSlabOperator.measure n)
      (fun z => rawKernel character β 2 z.1 z.2) (ground n β hβ) ‖transfer n β‖ f =
        mass n β hβ f - pairing n β hβ f (step n β hβ f) := by
  rw [← law_pairing, law_integral]
  unfold GroundStateDirichlet.dirichlet GroundStateDirichlet.normSquared
    GroundStateDirichlet.pairing GroundStateDirichlet.edgeDensity
  rw [mass, groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  ring

theorem increment_identity (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ z, (f z.1-f z.2)^2 ∂law n β hβ) =
      2 * (mass n β hβ f-pairing n β hβ f (step n β hβ f)) := by
  have he := GroundStateDirichlet.dirichlet_expectation (WilsonSlabOperator.measure n)
    (fun z => rawKernel character β 2 z.1 z.2)
    (rawKernel_continuous character character_continuous β 2)
    (fun z => (rawKernel_pos _ _ _ z.1 z.2).le)
    (WilsonTemporalInfluence.rawKernel_symm n β) (ground n β hβ)
    (ground n β hβ).continuous (fun u => (ground_pos n β hβ u).le) ‖transfer n β‖
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    (ground_raw_equation n β hβ) f f.continuous
  rw [raw_dirichlet] at he
  change _ = (1/2 : ℝ) * (∫ z, (f z.1-f z.2)^2 ∂law n β hβ) at he
  linarith

theorem physical_increment_le_loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ z, (f z.1-f z.2)^2 ∂law n β hβ) ≤ 2 * loss n β hβ f := by
  rw [increment_identity, ← WilsonPhysicalEnergyLoss.transferEnergy_identity n β hβ f hf]
  exact mul_le_mul_of_nonneg_left
    (WilsonPhysicalEnergyLoss.transferEnergy_le_loss n β hβ f hf) (by norm_num)

/-- Absolute endpoint products admit a genuine polynomial exponential moment,
uniformly over the source. This is stronger than the background tail. -/
theorem source_product_moment (β : ℝ) (hβ : 3 / 4 ≤ β)
    (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) :
    (∫ z, Real.exp (β * defect n e z) * |f z.1| * |f z.2| ∂law n β (by linarith)) ≤
      SU2GaussianMass.cap β * mass n β (by linarith) f := by
  let b : C(Slice n, ℝ) := ⟨fun u => |f u|, f.continuous.abs⟩
  let a : Slice n → ℝ := fun u => ground n β (by linarith) u * b u
  have ha : Continuous a := (ground n β (by linarith)).continuous.mul b.continuous
  have hc := quadratic_removal n β hβ e (fun u => (a u : ℂ))
    (Complex.continuous_ofReal.comp ha)
  rw [real_reflection, real_reflection] at hc
  have hpos := (PositiveKernelGroundState.transfer_top_eigenvector n β (by linarith)).1
  have hc' := div_le_div_of_nonneg_right hc hpos.le
  have hm : mass n β (by linarith) b = mass n β (by linarith) f := by
    unfold mass
    simp only [b, ContinuousMap.coe_mk, sq_abs]
  have he : (∫ z, Real.exp (β * defect n e z) * |f z.1| * |f z.2|
      ∂law n β (by linarith)) =
      (∫ z : Slice n × Slice n, a z.1 * cut n β e z.1 z.2 * a z.2
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) / ‖transfer n β‖ := by
    rw [law_integral, ← integral_div]
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [a, b, ContinuousMap.coe_mk]
    rw [show rawKernel character β 2 z.1 z.2 * ground n β (by linarith) z.1 *
        ground n β (by linarith) z.2 / ‖transfer n β‖ *
          (Real.exp (β * defect n e z) * |f z.1| * |f z.2|) =
      ((ground n β (by linarith) z.1 * |f z.1|) *
        (rawKernel character β 2 z.1 z.2 * Real.exp (β * defect n e z)) *
        (ground n β (by linarith) z.2 * |f z.2|)) / ‖transfer n β‖ by ring,
      cancellation]
  have hp : (∫ z : Slice n × Slice n, a z.1 * rawKernel character β 2 z.1 z.2 * a z.2
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) / ‖transfer n β‖ =
      pairing n β (by linarith) b (step n β (by linarith) b) := by
    rw [← law_pairing, law_integral, ← integral_div]
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [a]
    ring
  rw [he]
  calc
    _ ≤ SU2GaussianMass.cap β *
        pairing n β (by linarith) b (step n β (by linarith) b) := by
      simpa only [mul_div_assoc, hp] using hc'
    _ ≤ SU2GaussianMass.cap β * mass n β (by linarith) b :=
      mul_le_mul_of_nonneg_left (pairing_le_mass n β (by linarith) b)
        (SU2GaussianMass.cap_nonneg β (by linarith))
    _ = _ := by rw [hm]

/-- The squared-source tail is paid by actual physical loss plus an
exponentially small mass term. No source-independent bad-event substitution
or independence of temporal links is used. -/
theorem physical_source_tail (β : ℝ) (hβ : 3 / 4 ≤ β)
    (e : SpatialVertex n × Fin 3) (t : ℝ) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ z, {w | t ≤ defect n e w}.indicator (fun w => (f w.1)^2) z
      ∂law n β (by linarith)) ≤
      2 * loss n β (by linarith) f +
        2 * (Real.exp (-β*t) * SU2GaussianMass.cap β) * mass n β (by linarith) f := by
  letI := law_probability n β (by linarith)
  let ν := law n β (by linarith)
  have hE : MeasurableSet {z | t ≤ defect n e z} :=
    measurableSet_le measurable_const (defect_continuous n e).measurable
  have hdiff : Integrable (fun z : Slice n × Slice n => (f z.1-f z.2)^2) ν :=
    (((f.continuous.comp continuous_fst).sub
      (f.continuous.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hprod : Integrable (fun z : Slice n × Slice n =>
      Real.exp (β * defect n e z) * |f z.1| * |f z.2|) ν :=
    (((Real.continuous_exp.comp (continuous_const.mul (defect_continuous n e))).mul
      (f.continuous.abs.comp continuous_fst)).mul
      (f.continuous.abs.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi := integral_mono
    ((((f.continuous.comp continuous_fst).pow 2).integrable_of_hasCompactSupport
      (μ := ν) (HasCompactSupport.of_compactSpace _)).indicator hE)
    (hdiff.add (hprod.const_mul (2 * Real.exp (-β*t)))) (fun z => ?_)
  · simp only [Pi.add_apply, Function.comp_apply] at hi
    rw [integral_add hdiff (hprod.const_mul _), integral_const_mul] at hi
    have hd := physical_increment_le_loss n β (by linarith) f hf
    have hp := mul_le_mul_of_nonneg_left (source_product_moment n β hβ e f)
      (show 0 ≤ 2 * Real.exp (-β*t) by positivity)
    dsimp only [ν] at hi
    nlinarith
  · change {w | t ≤ defect n e w}.indicator (fun w => (f w.1)^2) z ≤
      (f z.1-f z.2)^2 + 2 * Real.exp (-β*t) *
        (Real.exp (β * defect n e z) * |f z.1| * |f z.2|)
    have hab : f z.1 * f z.2 ≤ |f z.1| * |f z.2| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hp : 0 ≤ |f z.1| * |f z.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hz : t ≤ defect n e z
    · rw [Set.indicator_of_mem (show z ∈ {w | t ≤ defect n e w} from hz)]
      have he : 1 ≤ Real.exp (-β*t) * Real.exp (β * defect n e z) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right he hp
      nlinarith [sq_nonneg (f z.2)]
    · rw [Set.indicator_of_notMem (show z ∉ {w | t ≤ defect n e w} from hz)]
      exact add_nonneg (sq_nonneg _) (by positivity)

end
end UnifiedTheory.Clay.YangMills.WilsonTemporalSourceTail
