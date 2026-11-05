/- Polynomial, volume-independent domination of the actual one-link ground
conditional density by Haar. This controls peaks, not spatial mixing. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSemiconvex
import UnifiedTheory.Clay.YangMills.SU2GaussianMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundPeak
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonSymmetricLinkChange WilsonGroundSemiconvex WilsonHaarLinkResponse
open WilsonGroundHeatBath CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

omit [NeZero n] in
theorem shift_compose (e : SpatialVertex n × Fin 3) (q r : Q) (u : Slice n) :
    shift n e q (shift n e r u) = shift n e (q*r) u := by
  funext j
  by_cases hj : j = e
  · subst j
    simp only [shift_at, mul_assoc]
  · simp only [shift_away n e _ _ j hj]

def linkMass (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (u : Slice n) : ℝ :=
  ∫ q, (ground n β hβ (shift n e q u))^2 ∂RegulatedGauge.compactHaar Q

theorem profile_continuous (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n) :
    Continuous (fun q : Q => ground n β hβ (shift n e q u)) :=
  (ground n β hβ).continuous.comp ((shift_joint_continuous n e).comp
    (continuous_id.prodMk continuous_const))

theorem linkMass_pos (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (u : Slice n) :
    0 < linkMass n β hβ e u :=
  PositiveKernelRatio.profile_integral_pos (RegulatedGauge.compactHaar Q)
    ⟨_, (profile_continuous n β hβ e u).pow 2⟩
    (fun _q => sq_pos_of_pos (ground_pos n β hβ _))

theorem linkMass_shift (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (r : Q) (u : Slice n) :
    linkMass n β hβ e (shift n e r u) = linkMass n β hβ e u := by
  unfold linkMass
  simp_rw [shift_compose]
  exact integral_mul_right_eq_self (μ := RegulatedGauge.compactHaar Q)
    (fun q => (ground n β hβ (shift n e q u))^2) r

/-- Compactness supplies a maximum in the same true one-link fiber. -/
theorem exists_link_maximum (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n) :
    ∃ a : Q, (∀ q : Q, ground n β hβ (shift n e q u) ≤ ground n β hβ (shift n e a u)) ∧
      ∀ r : Q, ground n β hβ (shift n e r (shift n e a u)) ≤
        ground n β hβ (shift n e a u) := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (profile_continuous n β hβ e u).continuousOn
  refine ⟨a, fun q => ha (Set.mem_univ q), ?_⟩
  intro r
  rw [shift_compose]
  exact ha (Set.mem_univ (r*a))

theorem mass_at_maximum (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n)
    (hmax : ∀ r : Q, ground n β hβ (shift n e r u) ≤ ground n β hβ u) :
    SU2GaussianMass.mass (132*β)*(ground n β hβ u)^2 ≤ linkMass n β hβ e u := by
  have h := integral_mono
    ((continuous_integrable (RegulatedGauge.compactHaar Q) _
      (SU2GaussianMass.weight_continuous (132*β))).mul_const ((ground n β hβ u)^2))
    (continuous_integrable (RegulatedGauge.compactHaar Q) _
      ((profile_continuous n β hβ e u).pow 2))
    (fun q => by simpa only [SU2GaussianMass.weight, neg_mul] using
      density_at_link_maximum n β hβ e u hmax q)
  simpa only [integral_mul_const, SU2GaussianMass.mass, linkMass] using h

omit n [NeZero n] in
/-- Explicit O((beta+1)^(3/2)) coefficient, independent of volume and exterior. -/
def peakCap (β : ℝ) : ℝ := SU2GaussianMass.cap (132*(β+1))

omit n [NeZero n] in
def peakConstant : ℝ := SU2GaussianMass.cap 132

omit n [NeZero n] in
theorem peakConstant_pos : 0 < peakConstant := by
  have h := SU2GaussianMass.mass_cap_lower 132 (by norm_num)
  have hm := SU2GaussianMass.mass_pos 132
  change 0 < SU2GaussianMass.cap 132
  nlinarith

omit n [NeZero n] in
theorem peakCap_formula (β : ℝ) :
    peakCap β = peakConstant*(β+1)*Real.sqrt (β+1) := by
  unfold peakCap peakConstant SU2GaussianMass.cap
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 132)]
  ring

omit n [NeZero n] in
theorem peakCap_nonneg (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ peakCap β :=
  SU2GaussianMass.cap_nonneg _ (by positivity)

/-- Unnormalized local density domination, using the actual ground amplitude. -/
theorem ground_square_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n) (q : Q) :
    (ground n β hβ (shift n e q u))^2 ≤ peakCap β*linkMass n β hβ e u := by
  obtain ⟨a, ha, hamax⟩ := exists_link_maximum n β hβ e u
  have hm := mass_at_maximum n β hβ e (shift n e a u) hamax
  rw [linkMass_shift] at hm
  have hmono := mul_le_mul_of_nonneg_right
    (SU2GaussianMass.mass_antitone (show 132*β ≤ 132*(β+1) by linarith))
    (sq_nonneg (ground n β hβ (shift n e a u)))
  have hcap := SU2GaussianMass.mass_cap_lower (132*(β+1)) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left (hmono.trans hm) (peakCap_nonneg β hβ)
  have h2 := mul_le_mul_of_nonneg_right hcap
    (sq_nonneg (ground n β hβ (shift n e a u)))
  have hq := (sq_le_sq₀ (ground_pos n β hβ _).le (ground_pos n β hβ _).le).mpr (ha q)
  unfold peakCap at h1 ⊢
  nlinarith

theorem normalized_density_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n) (q : Q) :
    (ground n β hβ (shift n e q u))^2 / linkMass n β hβ e u ≤ peakCap β :=
  (div_le_iff₀ (linkMass_pos n β hβ e u)).mpr (ground_square_le n β hβ e u q)

omit [NeZero n] in
/-- Haar rotation is exactly Haar replacement in the singleton block coordinates. -/
theorem rotation_integral_fiber (e : SpatialVertex n × Fin 3) (u : Slice n)
    (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ q, F (shift n e q u) ∂RegulatedGauge.compactHaar Q) =
      ∫ a, F (updateMap n {e} u a) ∂insideHaar n {e} := by
  have hp := measurePreserving_eval (fun _ : {j // j ∈ ({e} : Finset (SpatialVertex n × Fin 3))} =>
    RegulatedGauge.compactHaar Q) (⟨e, by simp⟩ : {j // j ∈ ({e} : Finset _)})
  have hc : Continuous (fun q : Q => F (shift n e q u)) :=
    hF.comp ((shift_joint_continuous n e).comp (continuous_id.prodMk continuous_const))
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable]
  simp_rw [← rotate_singleton n e _ u]
  haveI : (insideHaar n {e}).IsMulRightInvariant := by
    unfold insideHaar WilsonBlockMarginal.insideMeasure
    infer_instance
  exact integral_mul_right_eq_self (fun a => F (updateMap n {e} u a))
    (fun j : {j // j ∈ ({e} : Finset (SpatialVertex n × Fin 3))} => u j.1)

theorem linkMass_eq_fiberMass (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n) :
    linkMass n β hβ e u = fiberMass n β hβ {e} (outsideProjection n {e} u) :=
  rotation_integral_fiber n e u (fun v => (ground n β hβ v)^2) ((ground n β hβ).continuous.pow 2)

/-- The bound holds for every actual exterior, not just an averaged reference law. -/
theorem conditionalDensity_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (r : Outside n {e}) (a : Inside n {e}) :
    conditionalDensity n β hβ {e} r a ≤ peakCap β := by
  let u := WilsonBlockMarginal.assemble {e} (r,a)
  have h := normalized_density_le n β hβ e u 1
  have he : shift n e (1 : Q) u = u := by
    funext j
    by_cases hj : j = e
    · subst j
      simp only [shift_at, one_mul]
    · exact shift_away n e 1 u j hj
  rw [he, linkMass_eq_fiberMass] at h
  have ho : outsideProjection n {e} u = r :=
    outsideProjection_assemble n {e} (r,a)
  rw [ho] at h
  exact h

/-- Polynomial domination applies to every continuous nonnegative source weight. -/
theorem conditional_integral_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (r : Outside n {e})
    (F : Inside n {e} → ℝ) (hF : Continuous F) (hF0 : ∀ a, 0 ≤ F a) :
    (∫ a, F a ∂conditionalLaw n β hβ {e} r) ≤
      peakCap β*(∫ a, F a ∂insideHaar n {e}) := by
  rw [conditionalLaw_integral, ← integral_const_mul]
  have hc : Continuous (conditionalDensity n β hβ {e} r) :=
    (((weight_continuous n β hβ {e}).comp
      (continuous_const.prodMk continuous_id)).div_const _)
  exact integral_mono (continuous_integrable _ _ (hc.mul hF))
    (continuous_integrable _ _ (continuous_const.mul hF))
    (fun a => mul_le_mul_of_nonneg_right (conditionalDensity_le n β hβ e r a) (hF0 a))

end
end UnifiedTheory.Clay.YangMills.WilsonGroundPeak
