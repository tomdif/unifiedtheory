/- Uniform bounds for oscillatory sources on the actual imaginary shift.
The imaginary transverse source only couples to the imaginary flow, so
the apparent 1/h divergence cancels. The neutral shear is explicit. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase line trial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (imaginarySource)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse_real)
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (packet_half_norm)

def shearedMomentum (p : Transverse) : Charged := ![p 0,p 1,p 2+2*p 4,p 3+2*p 4]
def momentumSize (p : Transverse) : ℝ := ∑ i : Fin 4, (shearedMomentum p i)^2
def momentumPairing (p : Transverse) (x : Charged) : ℝ := ∑ i : Fin 4, shearedMomentum p i*x i

theorem momentumPairing_square (p : Transverse) (x : Charged) :
    (momentumPairing p x)^2 ≤ momentumSize p*squared x :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (shearedMomentum p) x

theorem imaginarySource_real (p : Transverse) (h : ℝ) (z : ℂ) (x : Grouped) :
    (source (imaginarySource (h⁻¹ • p)) z x).re =
      -((complexScale z).im/h)*momentumPairing p x.1 := by
  simp [source,imaginarySource,position,neutral,momentumPairing,shearedMomentum,
    mix,Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem complexScale_im_square_small (z : ℂ) :
    (complexScale z).im^2 ≤ Real.exp z.re*z.im^2/4 := by
  have he : (Real.exp (z.re/2))^2 = Real.exp z.re := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [complexScale,Complex.exp_im,mul_pow,Complex.div_ofNat_re,Complex.div_ofNat_im,he]
  convert mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := z.im/2)) (Real.exp_pos z.re).le using 1
  ring

theorem imaginarySource_square_bound (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (p : Transverse) (z : ℂ) (hz : |z.im| ≤ |h|/(2*ε)) (x : Grouped) :
    (source (imaginarySource (h⁻¹ • p)) z x).re^2 ≤
      momentumSize p/(16*ε^2)*(Real.exp z.re*squared x.1) := by
  have hm : 0 ≤ momentumSize p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz2 := pow_le_pow_left₀ (abs_nonneg z.im) hz 2
  rw [sq_abs,div_pow,sq_abs] at hz2
  have hc := (complexScale_im_square_small z).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 (Real.exp_pos z.re).le) (by norm_num : (0:ℝ) ≤ 4))
  have hd := div_le_div_of_nonneg_right hc (sq_nonneg h)
  have hs : ((complexScale z).im/h)^2 ≤ Real.exp z.re/(16*ε^2) := by
    rw [div_pow]
    apply hd.trans_eq
    field_simp
    ring
  rw [imaginarySource_real,neg_mul,neg_sq,mul_pow]
  exact (mul_le_mul hs (momentumPairing_square p x.1) (sq_nonneg _)
    (div_nonneg (Real.exp_pos z.re).le (by positivity))).trans_eq (by ring)

theorem imaginarySource_bound (ε h α β : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (p : Transverse) (z : ℂ)
    (hz : |z.im| ≤ Real.pi/3) (hhz : |z.im| ≤ |h|/(2*ε)) (x : Grouped) :
    (source (imaginarySource (h⁻¹ • p)) z x).re ≤
      (quadratic α β z x.1 x.2).re/2+momentumSize p/(8*α*ε^2) := by
  let Q := (quadratic α β z x.1 x.2).re
  let K := momentumSize p/(4*α*ε^2)
  have hm : 0 ≤ momentumSize p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := quadratic_re_nonnegative α β hα.le hβ.le hw z hz x.1 x.2
  have hl := quadratic_re_lower α β hα.le hβ.le hw z hz x.1 x.2
  have hd : (α/4)*(Real.exp z.re*squared x.1) ≤ Q := by
    have hn : 0 ≤ β*(x.2+shift z x.1)^2 := by positivity
    dsimp [Q]
    nlinarith only [hl,hn]
  have hk := mul_le_mul_of_nonneg_left hd hK
  have he : K*((α/4)*(Real.exp z.re*squared x.1)) =
      momentumSize p/(16*ε^2)*(Real.exp z.re*squared x.1) := by
    dsimp [K]
    field_simp
    ring
  rw [he] at hk
  have hs := (imaginarySource_square_bound ε h hε hh p z hhz x).trans hk
  have hr : (source (imaginarySource (h⁻¹ • p)) z x).re ≤ (Q+K)/2 := by
    nlinarith [sq_nonneg (Q-K)]
  exact hr.trans_eq (by dsimp [Q,K]; ring)

theorem boostedPacket_bound (ε h α β : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (p : Transverse) (z : ℂ)
    (hz : |z.im| ≤ Real.pi/3) (hhz : |z.im| ≤ |h|/(2*ε)) (x : Grouped) :
    ‖coherentPacket α β (imaginarySource (h⁻¹ • p)) z x‖ ≤
      Real.exp (momentumSize p/(8*α*ε^2))*‖packet (α/2) (β/2) z x‖ := by
  rw [coherentPacket,norm_mul,Complex.norm_exp,packet_half_norm,← Real.exp_add,
    packet,Complex.norm_exp,Complex.neg_re,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := imaginarySource_bound ε h α β hε hh hα hβ hw p z hz hhz x
  linarith

theorem clockPhase_shift_bound (ε p q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    ‖clockPhase (p/h) (inverseShift ε q h)‖ ≤ Real.exp (|p|/(2*ε)) := by
  rw [clockPhase_factor,norm_mul,inverseShift_zero,complexInverse_real ε hε]
  have he (s : ℝ) : ‖clockPhase (p/h) (s:ℂ)‖ = 1 := by
    simp [clockPhase,Complex.norm_exp]
  rw [he,one_mul]
  exact phaseRatio_norm_bound ε p q h hε hh hb

def envelope (ε α : ℝ) (p : Configuration) : ℝ :=
  Real.exp (|p.1|/(2*ε)+momentumSize p.2/(8*α*ε^2))

theorem boostedLine_bound (ε a h α β : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (p : Configuration) (w : ℝ × Grouped) :
    ‖line ε a α β (p.1/h) (imaginarySource (h⁻¹ • p.2)) (-h/2) w‖ ≤
      envelope ε α p*‖KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) (-h/2) w‖ := by
  have hs := KFCausalClockFloorShiftedOutput.shift_bound ε h hb
  have ht : |(((w.1:ℂ)+((-h/2:ℝ):ℂ)*Complex.I):ℂ).im| ≤ Real.pi*ε/3 := by simpa using hs
  have hz := inverse_im_third_strip ε hε _ ht
  have hi := inverse_im_bound ε hε _ (shiftArgument_mem ε w.1 h hb)
  have hzi : |(inverseShift ε w.1 h).im| ≤ |h|/(2*ε) := by
    simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,
      abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),div_div] using hi
  have hc := clockPhase_shift_bound ε p.1 w.1 h hε hh hb
  have hp := boostedPacket_bound ε h α β hε hh hα hβ hw p.2 _ hz hzi w.2
  have hm := mul_le_mul hc hp (norm_nonneg _) (Real.exp_pos _).le
  have hf := mul_le_mul_of_nonneg_left hm
    (norm_nonneg (KFCausalClockFloorFullGaussian.clockFactor a ((w.1:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)))
  simpa only [line,trial,KFCausalClockFloorFullGaussian.line,KFCausalClockFloorFullGaussian.trial,
    envelope,Real.exp_add,norm_mul,mul_assoc,mul_left_comm,inverseShift] using hf

#print axioms momentumPairing_square
#print axioms imaginarySource_real
#print axioms complexScale_im_square_small
#print axioms imaginarySource_square_bound
#print axioms imaginarySource_bound
#print axioms boostedPacket_bound
#print axioms clockPhase_shift_bound
#print axioms boostedLine_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
