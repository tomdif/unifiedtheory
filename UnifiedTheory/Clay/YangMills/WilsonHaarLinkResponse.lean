/- Haar-averaged link responses dominate actual single-link conditional
variances without a coupling penalty. Whole-slab observability still needs
a variance factorization for the actual ground law, not the 4D Gibbs law. -/
import UnifiedTheory.Clay.YangMills.WilsonHaarRefresh

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHaarLinkResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonDissipationIteration WilsonSymmetricLinkChange
open WilsonHaarRefresh CompactDensityEntropy WilsonVarianceResponse
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

omit [NeZero n] in
theorem shift_joint_continuous (e : SpatialVertex n × Fin 3) :
    Continuous (fun z : Q × Slice n => shift n e z.1 z.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = e
  · subst j
    simp only [shift_at]
    exact continuous_fst.mul ((continuous_apply e).comp continuous_snd)
  · simp only [shift_away n e _ _ j hj]
    exact (continuous_apply j).comp continuous_snd

omit [NeZero n] in
theorem rotate_singleton (e : SpatialVertex n × Fin 3) (q : Inside n {e}) (U : Slice n) :
    rotateBlock n {e} q U = shift n e (q ⟨e, by simp⟩) U := by
  funext j
  by_cases hj : j = e
  · subst j
    simp only [rotateBlock, updateMap, WilsonBlockMarginal.assemble_inside
      {e} _ e (by simp), shift_at]
  · simp only [rotateBlock, updateMap, WilsonBlockMarginal.assemble_outside
      {e} _ j (by simpa using hj), outsideProjection, shift_away n e _ U j hj]

omit [NeZero n] in
theorem refreshAt_singleton (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) (U : Slice n) :
    refreshAt n {e} f U = ∫ q, (f (shift n e q U)-f U)^2 ∂RegulatedGauge.compactHaar Q := by
  rw [refreshAt_rotations]
  simp_rw [rotate_singleton, sub_sq_comm (f U)]
  have hp := measurePreserving_eval (fun _ : {j // j ∈ ({e} : Finset (SpatialVertex n × Fin 3))} =>
    RegulatedGauge.compactHaar Q) (⟨e, by simp⟩ : {j // j ∈ ({e} : Finset _)})
  have hc : Continuous (fun q => (f (shift n e q U)-f U)^2) :=
    ((f.continuous.comp ((shift_joint_continuous n e).comp
      (continuous_id.prodMk continuous_const))).sub continuous_const).pow 2
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable]

theorem responseEnergy_continuous (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) :
    Continuous (fun q => responseEnergy n β hβ e q f) := by
  letI := groundLaw_probability n β hβ
  exact GibbsMarginalTower.fiber_integral_continuous (groundLaw n β hβ) _
    (((f.continuous.comp (shift_joint_continuous n e)).sub
      (f.continuous.comp continuous_snd)).pow 2)

/-- This is exactly the response used by the physical-transfer estimates, averaged in q. -/
theorem energy_singleton (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) :
    WilsonHaarRefresh.energy n β hβ {e} f =
      ∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q := by
  letI := groundLaw_probability n β hβ
  unfold WilsonHaarRefresh.energy
  simp_rw [refreshAt_singleton]
  have hc : Continuous (fun z : Slice n × Q => (f (shift n e z.2 z.1)-f z.1)^2) :=
    (((f.continuous.comp (shift_joint_continuous n e)).comp continuous_swap).sub
      (f.continuous.comp continuous_fst)).pow 2
  exact integral_integral_swap (f := fun U q => (f (shift n e q U)-f U)^2)
    (continuous_integrable ((groundLaw n β hβ).prod (RegulatedGauge.compactHaar Q)) _ hc)

/-- No small-coupling, density-ratio, or global mixing premise. -/
theorem local_lower (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) :
    heatBathEnergy n β hβ {e} f ≤
      ∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q := by
  rw [← energy_singleton]
  exact heatBathEnergy_le_energy n β hβ {e} f

def totalEnergy (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∑ e, ∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q

def totalConditionalVariance (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∑ e, heatBathEnergy n β hβ {e} f

theorem total_lower (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    totalConditionalVariance n β hβ f ≤ totalEnergy n β hβ f :=
  Finset.sum_le_sum (fun e _ => local_lower n β hβ e f)

omit [NeZero n] in
theorem coefficient_cap (β : ℝ) (hβ : 0 ≤ β) (q : Q) :
    coefficient β q ≤ (Real.exp (8*β)-1)^2 := by
  have hq : ‖(q : ℍ)-1‖ ≤ 2 := by
    simpa only [QuaternionSymmetricChange.unit_norm, norm_one, one_add_one_eq_two] using
      norm_sub_le (q : ℍ) (1 : ℍ)
  unfold coefficient
  apply (sq_le_sq₀ (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))).mpr
  apply sub_le_sub_right
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem total_upper (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    totalEnergy n β hβ (step n β hβ f) ≤
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ) * (Real.exp (8*β)-1)^2 *
        loss n β hβ f := by
  have he (e : SpatialVertex n × Fin 3) :
      (∫ q, responseEnergy n β hβ e q (step n β hβ f) ∂RegulatedGauge.compactHaar Q) ≤
        (Real.exp (8*β)-1)^2 * loss n β hβ f := by
    have h := integral_mono (continuous_integrable (RegulatedGauge.compactHaar Q) _
      (responseEnergy_continuous n β hβ e (step n β hβ f))) (integrable_const _)
      (fun q => (response_le_loss n β hβ e q f).trans
        (mul_le_mul_of_nonneg_right (coefficient_cap β hβ q) (loss_nonneg n β hβ f)))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  calc
    _ ≤ ∑ _e : SpatialVertex n × Fin 3, (Real.exp (8*β)-1)^2 * loss n β hβ f :=
      Finset.sum_le_sum (fun e _ => he e)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem variance_flow_antitone (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Antitone (fun k => variance n β hβ (flow n β hβ f k)) := by
  apply antitone_nat_of_succ_le
  intro k
  exact variance_step_le n β hβ (flow n β hβ f k)

/-- The only new premise is factorization for the actual ground law on physical sources. -/
theorem slab_lower (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalConditionalVariance n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U) (k : ℕ) :
    (k : ℝ) * variance n β hβ (flow n β hβ f k) ≤
      A * ∑ j ∈ Finset.range k, totalEnergy n β hβ (flow n β hβ f (j+1)) := by
  have hj (j : ℕ) (hj : j ∈ Finset.range k) :
      variance n β hβ (flow n β hβ f k) ≤
        A * totalEnergy n β hβ (flow n β hβ f (j+1)) :=
    ((variance_flow_antitone n β hβ f) (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans
      ((hfactor _ (flow_gauge n β hβ f hinv (j+1))).trans
        (mul_le_mul_of_nonneg_left (total_lower n β hβ _) hA))
  have h := Finset.sum_le_sum hj
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] using h

/-- The slab length is retained. Uniform control must address A*kappa/k. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hfactor : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalConditionalVariance n β hβ F)
    (hupper : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      totalEnergy n β hβ (step n β hβ F) ≤ κ * loss n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (flow n β hβ f k) ≤
      (A*κ/((k : ℝ)+A*κ))*variance n β hβ f := by
  have hu : (∑ j ∈ Finset.range k, totalEnergy n β hβ (flow n β hβ f (j+1))) ≤
      κ * (variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, κ * loss n β hβ (flow n β hβ f j) :=
        Finset.sum_le_sum (fun j _ => hupper _ (flow_gauge n β hβ f hinv j))
      _ = _ := by rw [← Finset.mul_sum, loss_telescope]
  have h := (slab_lower n β hβ A hA hfactor f hinv k).trans
    (mul_le_mul_of_nonneg_left hu hA)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ)+A*κ)).mpr
  nlinarith

/-- The crude upper coefficient is proved; only ground-law factorization is assumed here.
Its volume and coupling dependence is retained, so this is no uniform physical gap. -/
theorem explicit_slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalConditionalVariance n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (flow n β hβ f k) ≤
      (A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*(Real.exp (8*β)-1)^2) /
        ((k : ℝ)+A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*(Real.exp (8*β)-1)^2))) *
          variance n β hβ f :=
  slab_contraction n β hβ A _ hA (by positivity) hfactor
    (fun F _ => total_upper n β hβ F) f hinv k hk

end
end UnifiedTheory.Clay.YangMills.WilsonHaarLinkResponse
