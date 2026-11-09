/- The modified initial clock amplitude is a bounded smooth multiplier
of the unshifted amplitude. Its frequency dependence is retained. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge
import UnifiedTheory.Audit.KFCausalBoundedClockCharge
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (displacement displacement_smooth)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (displacement_strip_bound)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso chartIso_apply)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)

def modifier (ε a p h s : ℝ) : ℂ := Complex.exp
  ((-1+(p:ℂ)*Complex.I)*displacement ε h s+(a*h^2/4:ℝ)+Complex.I*(a*h*chart ε s:ℝ))
def bound (a p h : ℝ) : ℝ := Real.exp ((1+|p|)*Real.pi/3+a*h^2/4)
def symbol (ε a p h s : ℝ) : ℂ := modifier ε a p h s*(Real.sqrt (Real.exp s+ε):ℂ)⁻¹
def symbolBound (ε a p h : ℝ) : ℝ := bound a p h*(Real.sqrt ε)⁻¹

theorem inverse_zero (ε s : ℝ) (hε : 0 < ε) : inverse ε 0 s = (s:ℂ) := by
  simp only [inverse,argument,Complex.ofReal_zero,zero_mul,add_zero]
  rw [KFCausalComplexClockInverse.complexInverse_real ε hε,← chartIso_apply ε hε]
  simp only [OrderIso.symm_apply_apply]

theorem scale_zero (ε s : ℝ) (hε : 0 < ε) : scale ε 0 s = 1 := by
  simp [scale,relative,inverse_zero ε s hε,KFCausalClockFloorShearBounds.complexScale]

theorem modifier_smooth (ε a p h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ContDiff ℝ 1 (modifier ε a p h) := by
  have hc : ContDiff ℝ 1 (fun s : ℝ => (a*h*chart ε s:ℝ)) := by unfold chart; fun_prop
  exact (((contDiff_const.mul (displacement_smooth ε h hε hb)).add contDiff_const).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hc))).cexp

theorem modifier_bound (ε a p h s : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ‖modifier ε a p h s‖ ≤ bound a p h := by
  have hd := displacement_strip_bound ε h hε hb s
  have hr : -(displacement ε h s).re ≤ Real.pi/3 :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hd)
  have hi : |(displacement ε h s).im| ≤ Real.pi/3 := (Complex.abs_im_le_norm _).trans hd
  have hp : -(p*(displacement ε h s).im) ≤ |p| *(Real.pi/3) :=
    (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg p))
  rw [modifier,Complex.norm_exp,bound,Real.exp_le_exp]
  simp only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.one_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.neg_im,Complex.one_im,
    Complex.mul_im,mul_zero,zero_mul,mul_one,sub_zero,add_zero]
  nlinarith

theorem symbol_smooth (ε a p h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ContDiff ℝ 1 (symbol ε a p h) := by
  have hs : ContDiff ℝ 1 (fun s : ℝ => Real.sqrt (Real.exp s+ε)) :=
    (contDiff_id.exp.add contDiff_const).sqrt (fun s => ne_of_gt (by positivity))
  exact (modifier_smooth ε a p h hε hb).mul ((Complex.ofRealCLM.contDiff.comp hs).inv
    (fun s => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'))

theorem symbolBound_nonnegative (ε a p h : ℝ) : 0 ≤ symbolBound ε a p h := by
  unfold symbolBound bound
  positivity

theorem symbol_bound (ε a p h s : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ‖symbol ε a p h s‖ ≤ symbolBound ε a p h := by
  have hir : (Real.sqrt (Real.exp s+ε))⁻¹ ≤ (Real.sqrt ε)⁻¹ :=
    KFCausalClockFloorClockHalf.inverseWeight_bound ε hε (s,0)
  have hi : ‖(Real.sqrt (Real.exp s+ε):ℂ)⁻¹‖ ≤ (Real.sqrt ε)⁻¹ := by
    simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hir
  rw [symbol,norm_mul,symbolBound]
  exact mul_le_mul (modifier_bound ε a p h s hε hb) hi (norm_nonneg _) (Real.exp_pos _).le

theorem clock_amplitude_identity (ε a p h s : ℝ) (hε : 0 < ε) :
    Complex.exp (-displacement ε h s)*clockAmplitude ε a p (-h/2) s =
      modifier ε a p h s*clockAmplitude ε a p 0 s := by
  simp only [clockAmplitude,clockPhase,clockFactor,modifier,inverse_zero ε s hε]
  calc
    _ = (KFCausalClockFloorChargeTrialBridge.amplitude ε s:ℂ)*Complex.exp
      (-displacement ε h s+(p:ℂ)*Complex.I*inverse ε (-h/2) s-(a:ℂ)*(argument ε (-h/2) s)^2) := by
        simp only [sub_eq_add_neg,neg_mul,Complex.exp_add]
        ring
    _ = (KFCausalClockFloorChargeTrialBridge.amplitude ε s:ℂ)*Complex.exp
      (((-1+(p:ℂ)*Complex.I)*displacement ε h s+(a*h^2/4:ℝ)+Complex.I*(a*h*chart ε s:ℝ))+
        (p:ℂ)*Complex.I*(s:ℂ)-(a:ℂ)*(argument ε 0 s)^2) := by
        congr 2
        unfold displacement relative argument
        push_cast
        linear_combination (-(a:ℂ)*(h:ℂ)^2/4)*Complex.I_sq
    _ = _ := by
      simp only [sub_eq_add_neg,neg_mul,Complex.exp_add]
      ring

#print axioms inverse_zero
#print axioms scale_zero
#print axioms modifier_smooth
#print axioms modifier_bound
#print axioms symbol_smooth
#print axioms symbolBound_nonnegative
#print axioms symbol_bound
#print axioms clock_amplitude_identity
end
end UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier
