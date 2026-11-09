/- Exact transverse rescaling of the actual boosted longitudinal energy.
The oscillatory source is rescaled along with the Gaussian, retaining the
neutral shear. This is an identity, not yet an interchange of limits. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyRemainder
import UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (line line_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (gaussianState_mass)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling (quadratic_smul gaussianMass_smul)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass trial_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem source_smul (b : Fin 5 → ℂ) (z : ℂ) (c : ℝ) (x : Grouped) :
    source b z (c • x) = source (c • b) z x := by
  simp [source,position,neutral,mix,Fin.sum_univ_succ,Complex.real_smul]
  ring

theorem line_smul (ε a α β r y c : ℝ) (b : Fin 5 → ℂ) (q : ℝ) (x : Grouped) :
    line ε a α β r b y (q,c • x) = line ε a (c^2*α) (c^2*β) r (c • b) y (q,x) := by
  simp only [line,KFCausalClockFloorCoherentStrip.trial,coherentPacket,source_smul,
    packet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,quadratic_smul]

theorem line_mass_smul (ε a α β r y c : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hc : 0 < c) :
    (∫ z : ℝ × Grouped, ‖line ε a (c^2*α) (c^2*β) r (c • b) y z‖^2) =
      (c^5)⁻¹*(∫ z : ℝ × Grouped, ‖line ε a α β r b y z‖^2) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure Grouped) := Measure.prod.instIsAddHaarMeasure _ _
  have hd : Module.finrank ℝ Grouped = 5 := by simp [Grouped,Charged,Module.finrank_prod]
  have h0 := line_memLp ε a α β r b y hε ha hα hβ hw hy
  have h1 := line_memLp ε a (c^2*α) (c^2*β) r (c • b) y hε ha
    (by positivity) (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hw (sq_nonneg c)]) hy
  have hi0 := (memLp_two_iff_integrable_sq_norm h0.1).mp h0
  have hi1 := (memLp_two_iff_integrable_sq_norm h1.1).mp h1
  rw [Measure.volume_eq_prod ℝ Grouped] at hi0 hi1 ⊢
  rw [integral_prod _ hi1,integral_prod _ hi0,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  simp_rw [← line_smul]
  simpa only [hd,smul_eq_mul] using
    (Measure.integral_comp_smul_of_nonneg (volume : Measure Grouped)
      (fun x => ‖line ε a α β r b y (q,x)‖^2) c (hR := hc.le))

theorem line_mass_ratio (ε a α β r y c : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hc : 0 < c) :
    (∫ z : ℝ × Grouped, ‖line ε a (c^2*α) (c^2*β) r (c • b) y z‖^2)/gaussianMass (c^2*α) (c^2*β) =
      (∫ z : ℝ × Grouped, ‖line ε a α β r b y z‖^2)/gaussianMass α β := by
  rw [line_mass_smul ε a α β r y c b hε ha hα hβ hw hy hc,gaussianMass_smul α β c hα hβ hc]
  exact mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 5 hc.ne'))

def scale (h : ℝ) : ℝ := Real.sqrt |h|

theorem scale_positive (h : ℝ) (hh : h ≠ 0) : 0 < scale h := Real.sqrt_pos.mpr (abs_pos.mpr hh)

theorem scale_groundWidth (h : ℝ) (hh : h ≠ 0) : (scale h)^2*groundWidth h = groundWidth 1 := by
  rw [scale,Real.sq_sqrt (abs_nonneg h)]
  unfold groundWidth
  norm_num
  field_simp [abs_ne_zero.mpr hh]

theorem scale_neutralWidth (h : ℝ) (hh : h ≠ 0) : (scale h)^2*neutralWidth h = neutralWidth 1 := by
  rw [neutralWidth,neutralWidth,← mul_div_assoc,scale_groundWidth h hh]

def rescaledLine (ε a h : ℝ) (p : Configuration) : ℝ × Grouped → ℂ :=
  line ε a (groundWidth 1) (neutralWidth 1) (p.1/h)
    (scale h • imaginarySource (h⁻¹ • p.2)) (-h/2)

theorem rescaledLine_eq (ε a h : ℝ) (hh : h ≠ 0) (p : Configuration) (z : ℝ × Grouped) :
    rescaledLine ε a h p z =
      line ε a (groundWidth h) (neutralWidth h) (p.1/h)
        (imaginarySource (h⁻¹ • p.2)) (-h/2) (z.1,scale h • z.2) := by
  rw [line_smul,scale_groundWidth h hh,scale_neutralWidth h hh]
  rfl

theorem rescaledLine_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : MemLp (rescaledLine ε a h p) 2 volume :=
  line_memLp ε a _ _ _ _ _ hε ha (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1) (shift_bound ε h hb)

theorem rescaled_energy_identity (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    ‖boostedExponentialOutput ε a h hε ha hh hb p‖^2 =
      (∫ z : ℝ × Grouped, ‖rescaledLine ε a h p z‖^2)/
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  have ht := line_mass_ratio ε a (groundWidth h) (neutralWidth h) (p.1/h) (-h/2)
    (scale h) (imaginarySource (h⁻¹ • p.2)) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb) (scale_positive h hh)
  rw [scale_groundWidth h hh,scale_neutralWidth h hh] at ht
  have he : (h⁻¹ • p).1 = p.1/h := by change h⁻¹*p.1 = _; ring
  rw [boostedExponentialOutput,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul,trial_norm_square,
    spectralOutput,gaussianState_mass,he]
  rw [mul_comm (clockMass ε a),← div_div,mul_comm (clockMass ε a),← div_div]
  exact congrArg (fun x : ℝ => x/clockMass ε a) ht.symm

#print axioms source_smul
#print axioms line_smul
#print axioms line_mass_smul
#print axioms line_mass_ratio
#print axioms scale_positive
#print axioms scale_groundWidth
#print axioms scale_neutralWidth
#print axioms rescaledLine_eq
#print axioms rescaledLine_memLp
#print axioms rescaled_energy_identity

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling
