/- Both ordered field-energy densities admit one integrable Gaussian
majorant over each entire boosted charge orbit. Their limits retain the
square and fourth power of the real displaced centre field. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates (energy)

theorem fieldPower_gaussian_bound (j : Fin 2) (h : ℝ) (h1 : |h| ≤ 1)
    (Q ξ : Transverse) (l : Transverse →L[ℝ] ℝ) :
    (fieldPower j l (rescaledPosition h Q ξ))^2*gaussianEnvelope (1/4) ξ ≤
      256*(fieldBound l Q)^2*gaussianEnvelope (1/8) ξ := by
  calc
    _ ≤ ((fieldBound l Q)^2*(1+energy ξ)^2)*gaussianEnvelope (1/4) ξ :=
      mul_le_mul_of_nonneg_right (fieldPower_square_bound j h h1 Q ξ l) (Real.exp_pos _).le
    _ = (fieldBound l Q)^2*((1+energy ξ)^2*gaussianEnvelope (1/4) ξ) := by ring
    _ ≤ (fieldBound l Q)^2*(256*gaussianEnvelope (1/8) ξ) :=
      mul_le_mul_of_nonneg_left (polynomial_absorption ξ) (sq_nonneg _)
    _ = _ := by ring

def fieldDensity (ε a : ℝ) (hε : 0 < ε) (h : ℝ) (p : Configuration) (θ : ℝ)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (z : ℝ × Transverse) : ℝ :=
  (fieldPower j l (rescaledPosition h (orbitCentre p θ) z.2))^2*outputDensity ε a hε h p θ z

def fieldLimitDensity (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (θ : ℝ)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (z : ℝ × Transverse) : ℝ :=
  (fieldPower j l (orbitCentre p θ))^2*limitDensity ε a hε p θ z

theorem fieldDensity_continuous (ε a h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Continuous (fieldDensity ε a hε h p θ l j) := by
  have hx : Continuous (fun z : ℝ × Transverse => rescaledPosition h (orbitCentre p θ) z.2) := by
    apply continuous_pi
    intro i
    unfold rescaledPosition
    fun_prop
  exact (((l.continuous.comp hx).pow (j.val+1)).pow 2).mul (outputDensity_continuous ε a h hε hb p θ)

theorem fieldDensity_uniform_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    ∃ B : ℝ, ∀ (θ h : ℝ), h ≠ 0 → |h| ≤ 2*Real.pi*ε/3 → |h| ≤ ε/2 → |h| ≤ 1 →
      ∀ (j : Fin 2) (z : ℝ × Transverse), ‖fieldDensity ε a hε h p θ l j z‖ ≤
        B*clockWeight ε a hε z.1*gaussianEnvelope (1/8) z.2 := by
  obtain ⟨B,hB⟩ := outputDensity_uniform_bound ε a hε ha p
  obtain ⟨D,hD⟩ := fieldBound_orbit l p
  refine ⟨256*|B| *|D|,?_⟩
  intro θ h hh hb hs h1 j z
  have hw : 0 ≤ clockWeight ε a hε z.1 := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have ho : ‖outputDensity ε a hε h p θ z‖ ≤
      |B| *clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2 := by
    apply (hB θ h hh hb hs h1 z).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hw) (Real.exp_pos _).le
  have hd : (fieldBound l (orbitCentre p θ))^2 ≤ |D| := (hD θ).trans (le_abs_self D)
  rw [fieldDensity,norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ (fieldPower j l (rescaledPosition h (orbitCentre p θ) z.2))^2*
        (|B| *clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2) :=
      mul_le_mul_of_nonneg_left ho (sq_nonneg _)
    _ = (|B| *clockWeight ε a hε z.1)*
        ((fieldPower j l (rescaledPosition h (orbitCentre p θ) z.2))^2*gaussianEnvelope (1/4) z.2) := by ring
    _ ≤ (|B| *clockWeight ε a hε z.1)*
        (256*(fieldBound l (orbitCentre p θ))^2*gaussianEnvelope (1/8) z.2) :=
      mul_le_mul_of_nonneg_left (fieldPower_gaussian_bound j h h1 _ _ l) (mul_nonneg (abs_nonneg B) hw)
    _ ≤ (|B| *clockWeight ε a hε z.1)*(256*|D| *gaussianEnvelope (1/8) z.2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (Real.exp_pos _).le)
        (mul_nonneg (abs_nonneg B) hw)
    _ = _ := by ring

theorem fieldEnvelope_integrable (ε a B : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun z : ℝ × Transverse => B*clockWeight ε a hε z.1*gaussianEnvelope (1/8) z.2) := by
  rw [Measure.volume_eq_prod ℝ Transverse]
  exact ((clockWeight_integrable ε a hε ha).const_mul B).mul_prod
    (gaussianEnvelope_integrable (1/8) (by norm_num))

theorem fieldDensity_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Integrable (fieldDensity ε a hε h p θ l j) := by
  obtain ⟨B,hB⟩ := fieldDensity_uniform_bound ε a hε ha.le p l
  exact (fieldEnvelope_integrable ε a B hε ha).mono'
    (fieldDensity_continuous ε a h hε hb p θ l j).aestronglyMeasurable
    (Eventually.of_forall (hB θ h hh hb hs h1 j))

theorem fieldDensity_tendsto (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (θ : ℝ)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hz : Tendsto h atTop (𝓝 0)) (z : ℝ × Transverse) :
    Tendsto (fun n => fieldDensity ε a hε (h n) p θ l j z) atTop
      (𝓝 (fieldLimitDensity ε a hε p θ l j z)) :=
  ((fieldPower_tendsto j l (orbitCentre p θ) z.2 h hz).pow 2).mul
    (outputDensity_tendsto ε a hε p θ h hh hz z)

theorem fieldDensity_integral_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, fieldDensity ε a hε (h n) p θ l j z) atTop
      (𝓝 (∫ z, fieldLimitDensity ε a hε p θ l j z)) := by
  obtain ⟨B,hB⟩ := fieldDensity_uniform_bound ε a hε ha.le p l
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ × Transverse => B*clockWeight ε a hε z.1*gaussianEnvelope (1/8) z.2)
  · exact Eventually.of_forall (fun n => (fieldDensity_continuous ε a (h n) hε (hb n) p θ l j).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    exact Eventually.of_forall (hB θ (h n) (hh n) (hb n) hn.1 hn.2 j)
  · exact fieldEnvelope_integrable ε a B hε ha
  · exact Eventually.of_forall (fieldDensity_tendsto ε a hε p θ l j h hh hz)

#print axioms fieldPower_gaussian_bound
#print axioms fieldDensity_continuous
#print axioms fieldDensity_uniform_bound
#print axioms fieldEnvelope_integrable
#print axioms fieldDensity_integrable
#print axioms fieldDensity_tendsto
#print axioms fieldDensity_integral_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity
