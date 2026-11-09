/- Pointwise limits and a varying Gaussian majorant for the exactly
rescaled boosted energy density. Only the real part of the transverse
source vanishes; the complex oscillatory state need not converge. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaledLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (imaginarySource)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
open UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (uniformEnvelope ground_envelope_bound)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse_real)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (line)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)

theorem inverseShift_im_bound (ε q h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    |(inverseShift ε q h).im| ≤ |h|/(2*ε) := by
  have hi := Complex.abs_im_le_norm (inverseShift ε q h-inverseShift ε q 0)
  rw [Complex.sub_im,inverseShift_zero,complexInverse_real ε hε,Complex.ofReal_im,sub_zero] at hi
  have hd := inverseShift_difference_bound ε q h hε hb
  rw [inverseShift_zero,complexInverse_real ε hε] at hd
  exact hi.trans hd

theorem rescaled_source_square_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Transverse) (x : Grouped) :
    (source (scale h • imaginarySource (h⁻¹ • p)) (inverseShift ε q h) x).re^2 ≤
      |h| *(momentumSize p/(16*ε^2)*(Real.exp (inverseShift ε q h).re*squared x.1)) := by
  rw [← source_smul]
  have hb' := imaginarySource_square_bound ε h hε hh p (inverseShift ε q h)
    (inverseShift_im_bound ε q h hε hb) (scale h • x)
  apply hb'.trans_eq
  have hs : squared (scale h • x.1) = |h| *squared x.1 := by
    simp only [squared,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum,
      scale,Real.sq_sqrt (abs_nonneg h)]
  rw [Prod.smul_fst,hs]
  ring

theorem rescaled_source_tendsto (ε q : ℝ) (hε : 0 < ε) (p : Transverse) (x : Grouped)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (source (scale (h n) • imaginarySource ((h n)⁻¹ • p))
      (inverseShift ε q (h n)) x).re) atTop (𝓝 0) := by
  have hi := (inverseShift_derivative ε q hε).continuousAt.tendsto.comp hz
  have he := Real.continuous_exp.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp hi)
  have ht : Tendsto (fun n => |h n| *(momentumSize p/(16*ε^2)*
      (Real.exp (inverseShift ε q (h n)).re*squared x.1))) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul ((he.mul_const (squared x.1)).const_mul (momentumSize p/(16*ε^2)))
  have hs := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => sq_nonneg ((source (scale (h n) • imaginarySource ((h n)⁻¹ • p))
      (inverseShift ε q (h n)) x).re))
    (fun n => rescaled_source_square_bound ε q (h n) hε (hh n) (hb n) p x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero,Real.norm_eq_abs] using hs.sqrt

theorem line_shift_tendsto (ε a α β : ℝ) (hε : 0 < ε) (z : ℝ × Grouped) :
    Tendsto (fun h : ℝ => line ε a α β (-h/2) z) (𝓝 0) (𝓝 (line ε a α β 0 z)) := by
  have hq : (z.1:ℂ) ∈ KFCausalComplexClockChart.targetStrip ε := by
    change |(z.1:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hc := (KFCausalClockFloorFullGaussian.trial_analytic ε a α β hε z.2 (z.1:ℂ) hq).continuousAt
  have ht : ContinuousAt (fun h : ℝ => (z.1:ℂ)+((-h/2:ℝ):ℂ)*Complex.I) 0 := by fun_prop
  have ht' : Tendsto (fun h : ℝ => (z.1:ℂ)+((-h/2:ℝ):ℂ)*Complex.I) (𝓝 0) (𝓝 (z.1:ℂ)) := by
    simpa only [Complex.ofReal_zero,neg_zero,zero_div,zero_mul,add_zero] using ht.tendsto
  simpa only [line,Complex.ofReal_zero,zero_mul,add_zero] using hc.tendsto.comp ht'

theorem rescaledLine_square (ε a h : ℝ) (hε : 0 < ε) (p : Configuration) (z : ℝ × Grouped) :
    ‖rescaledLine ε a h p z‖^2 = ‖phaseRatio ε p.1 z.1 h‖^2*
      (Real.exp (source (scale h • imaginarySource (h⁻¹ • p.2)) (inverseShift ε z.1 h) z.2).re)^2*
      ‖line ε a (groundWidth 1) (neutralWidth 1) (-h/2) z‖^2 := by
  have hp : ‖clockPhase (p.1/h) (inverseShift ε z.1 h)‖ = ‖phaseRatio ε p.1 z.1 h‖ := by
    rw [clockPhase_factor,norm_mul,inverseShift_zero,complexInverse_real ε hε]
    have hr (r s : ℝ) : ‖clockPhase r (s:ℂ)‖ = 1 := by simp [clockPhase,Complex.norm_exp]
    rw [hr,one_mul]
  simp only [rescaledLine,KFCausalClockFloorCoherentStrip.line,KFCausalClockFloorCoherentStrip.trial,
    coherentPacket,line,KFCausalClockFloorFullGaussian.trial,norm_mul,mul_pow]
  rw [show ‖clockPhase (p.1/h) (KFCausalComplexClockInverse.complexInverse ε
      ((z.1:ℂ)+((-h/2:ℝ):ℂ)*Complex.I))‖ = ‖phaseRatio ε p.1 z.1 h‖ from hp,Complex.norm_exp]
  unfold inverseShift
  ring

def limitDensity (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (z : ℝ × Grouped) : ℝ :=
  Real.exp (p.1/realClock ε hε z.1)*‖line ε a (groundWidth 1) (neutralWidth 1) 0 z‖^2

theorem rescaled_density_tendsto (ε a : ℝ) (hε : 0 < ε) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (z : ℝ × Grouped) :
    Tendsto (fun n => ‖rescaledLine ε a (h n) p z‖^2) atTop (𝓝 (limitDensity ε a hε p z)) := by
  have hn : Tendsto h atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => hh n)⟩
  have hp := (phaseRatio_energy_tendsto ε p.1 z.1 hε).comp hn
  have hs := Real.continuous_exp.continuousAt.tendsto.comp (rescaled_source_tendsto ε z.1 hε p.2 z.2 h hh hb hz)
  have hl := ((line_shift_tendsto ε a (groundWidth 1) (neutralWidth 1) hε z).comp hz).norm.pow 2
  simp_rw [rescaledLine_square ε a _ hε p z]
  simpa only [Real.exp_zero,one_pow,mul_one,limitDensity] using (hp.mul (hs.pow 2)).mul hl

theorem rescaled_density_bound (ε a h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (z : ℝ × Grouped) :
    ‖rescaledLine ε a h p z‖^2 ≤ (uniformEnvelope ε p)^2*
      ‖line ε a (groundWidth 1/2) (neutralWidth 1/2) (-h/2) z‖^2 := by
  have hi := boostedLine_bound ε a h _ _ hε hh (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hb p (z.1,scale h • z.2)
  have hu := hi.trans (mul_le_mul_of_nonneg_right (ground_envelope_bound ε h hε hh h1 p) (norm_nonneg _))
  rw [← rescaledLine_eq ε a h hh p z,KFCausalClockFloorGaussianRescaling.line_smul] at hu
  rw [← mul_div_assoc,scale_groundWidth h hh,← mul_div_assoc,scale_neutralWidth h hh] at hu
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hu 2

#print axioms inverseShift_im_bound
#print axioms rescaled_source_square_bound
#print axioms rescaled_source_tendsto
#print axioms line_shift_tendsto
#print axioms rescaledLine_square
#print axioms rescaled_density_tendsto
#print axioms rescaled_density_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaledLimit
