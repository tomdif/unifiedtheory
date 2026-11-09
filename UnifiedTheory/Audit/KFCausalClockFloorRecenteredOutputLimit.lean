/- Dominated convergence for the full, Jacobian-weighted output density
on every fixed boosted charge orbit. The dominating function is proved
integrable and is uniform in the charge angle and small nonzero hbar. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates (energy)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedOrbitDensityBound (boostedLine_uniform_bound)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

theorem recenter_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (Q : Transverse) :
    Continuous (fun z : ℝ × Transverse => recenter ε hε z.1 h Q z.2) := by
  have hi : Continuous (fun z : ℝ × Transverse => (chartIso ε hε).symm z.1) :=
    (chartIso ε hε).symm.toHomeomorph.continuous.comp continuous_fst
  unfold recenter KFCausalClockFloorDisplacedShiftPhase.grouped
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    fin_cases i <;> simp [KFCausalTransverseDilationFlow.flow,KFCausalTransverseDilationFlow.scale,
      KFCausalClockFloorDisplacedPhaseLimit.rescaledPosition] <;> fun_prop
  · simp [KFCausalTransverseDilationFlow.flow,KFCausalTransverseDilationFlow.scale,
      KFCausalClockFloorDisplacedPhaseLimit.rescaledPosition]
    fun_prop

theorem boostedLine_continuous (ε a h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) :
    Continuous (fun z : ℝ × Transverse => boostedLine ε a hε z.1 h p θ z.2) := by
  unfold boostedLine
  dsimp only
  apply continuous_const.mul
  exact (KFCausalClockFloorCoherentStrip.line_continuous ε a _ _ _ _ _ hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)).comp
      (f := fun z : ℝ × Transverse => (z.1,recenter ε hε z.1 h _ z.2))
      (continuous_fst.prodMk (recenter_continuous ε hε h _))

theorem clockJacobian_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (clockJacobian ε hε) :=
  Real.continuous_exp.comp (continuous_const.mul (chartIso ε hε).symm.toHomeomorph.continuous)

def outputDensity (ε a : ℝ) (hε : 0 < ε) (h : ℝ) (p : Configuration) (θ : ℝ)
    (z : ℝ × Transverse) : ℝ := clockJacobian ε hε z.1*‖boostedLine ε a hε z.1 h p θ z.2‖^2

def limitDensity (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (θ : ℝ) (z : ℝ × Transverse) : ℝ :=
  clockWeight ε a hε z.1*gaussianEnvelope 2 z.2*
    Real.exp ((p.1+KFCausalClassicalChargePhase.shear
      (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/
        realClock ε hε z.1)

theorem outputDensity_continuous (ε a h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) :
    Continuous (outputDensity ε a hε h p θ) :=
  ((clockJacobian_continuous ε hε).comp continuous_fst).mul
    ((boostedLine_continuous ε a h hε hb p θ).norm.pow 2)

theorem outputDensity_uniform_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) (p : Configuration) :
    ∃ B : ℝ, ∀ (θ h : ℝ), h ≠ 0 → |h| ≤ 2*Real.pi*ε/3 → |h| ≤ ε/2 → |h| ≤ 1 →
      ∀ z : ℝ × Transverse, ‖outputDensity ε a hε h p θ z‖ ≤
        B*clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2 := by
  obtain ⟨B,hB⟩ := boostedLine_uniform_bound ε a hε ha p
  refine ⟨B,?_⟩
  intro θ h hh hb hs h1 z
  have he := mul_le_mul_of_nonneg_left (hB θ z.1 h hh hb hs h1 z.2)
    (show 0 ≤ clockJacobian ε hε z.1 from (Real.exp_pos _).le)
  rw [outputDensity,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (show 0 ≤ clockJacobian ε hε z.1 from (Real.exp_pos _).le) (sq_nonneg _))]
  convert he using 1
  unfold clockWeight gaussianEnvelope
  rw [show -(1/4:ℝ)*energy z.2 = -energy z.2/4 by ring]
  ring

theorem outputDensity_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1) (p : Configuration) (θ : ℝ) :
    Integrable (outputDensity ε a hε h p θ) := by
  obtain ⟨B,hB⟩ := outputDensity_uniform_bound ε a hε ha.le p
  exact (productEnvelope_integrable ε a B hε ha).mono'
    (outputDensity_continuous ε a h hε hb p θ).aestronglyMeasurable
    (Eventually.of_forall (hB θ h hh hb hs h1))

theorem outputDensity_tendsto (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (θ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) (z : ℝ × Transverse) :
    Tendsto (fun n => outputDensity ε a hε (h n) p θ z) atTop (𝓝 (limitDensity ε a hε p θ z)) := by
  have ht := (boostedLine_density_tendsto ε a z.1 hε p θ z.2 h hh hz).const_mul (clockJacobian ε hε z.1)
  convert ht using 1
  unfold limitDensity clockWeight gaussianEnvelope energy
  ring

theorem eventually_small (ε : ℝ) (hε : 0 < ε) (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |h n| ≤ ε/2 ∧ |h n| ≤ 1 := by
  have ht : Tendsto (fun n => |h n|) atTop (𝓝 0) := by simpa using hz.abs
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)),
    ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n hs h1
  exact ⟨hs.le,h1.le⟩

theorem outputDensity_integral_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, outputDensity ε a hε (h n) p θ z) atTop
      (𝓝 (∫ z, limitDensity ε a hε p θ z)) := by
  obtain ⟨B,hB⟩ := outputDensity_uniform_bound ε a hε ha.le p
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ × Transverse => B*clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2)
  · exact Eventually.of_forall (fun n =>
      (outputDensity_continuous ε a (h n) hε (hb n) p θ).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    exact Eventually.of_forall (hB θ (h n) (hh n) (hb n) hn.1 hn.2)
  · exact productEnvelope_integrable ε a B hε ha
  · exact Eventually.of_forall (outputDensity_tendsto ε a hε p θ h hh hz)

theorem boostedOutput_integral (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1) (p : Configuration) (θ : ℝ) :
    ‖boostedOutput ε a h hε ha hh hb p θ‖^2 =
      (∫ z, outputDensity ε a hε h p θ z) /
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  have hi := outputDensity_integrable ε a h hε ha hh hb hs h1 p θ
  rw [boostedOutput_mass,Measure.volume_eq_prod ℝ Transverse] at ⊢
  rw [Measure.volume_eq_prod ℝ Transverse] at hi
  rw [integral_prod _ hi]
  simp only [outputDensity,integral_const_mul]

#print axioms recenter_continuous
#print axioms boostedLine_continuous
#print axioms clockJacobian_continuous
#print axioms outputDensity_continuous
#print axioms outputDensity_uniform_bound
#print axioms outputDensity_integrable
#print axioms outputDensity_tendsto
#print axioms eventually_small
#print axioms outputDensity_integral_tendsto
#print axioms boostedOutput_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
