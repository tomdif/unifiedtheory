/- Uniform small-hbar bounds for the full recentered density. The shear
phase is absorbed into the remaining Gaussian decay, with explicit
dependence on physical centres and momenta and no clock-coordinate loss. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedGaussianBound
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDensityBound
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedUniformShift
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedGaussianBound
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (shear transverseRatio)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition transverseRatio_eq)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase (phaseRatio phaseRatio_norm_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)

theorem transverseRatio_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) (X P : Transverse) :
    ‖transverseRatio ε q h X P‖ ≤ Real.exp (2*scaleBound ε*|shear X P|) := by
  rw [transverseRatio_eq,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (relativeScale_slope_bound ε q h hε hh hb hsmall)
      (by norm_num : (0:ℝ) ≤ 2)) (abs_nonneg (shear X P))
  simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs] using ht

theorem rescaledRatio_square_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) (h1 : |h| ≤ 1) (Q P ξ : Transverse) :
    ‖transverseRatio ε q h (rescaledPosition h Q ξ) P‖^2 ≤
      Real.exp (4*scaleBound ε*|shear Q P|+16*(scaleBound ε)^2*momentumBound P)*
        Real.exp (energy ξ/4) := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (transverseRatio_bound ε q h hε hh hb hsmall
    (rescaledPosition h Q ξ) P) 2
  rw [← Real.exp_nat_mul] at ht
  apply ht.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  have hD := (scaleBound_positive ε hε).le
  have ha : |shear (rescaledPosition h Q ξ) P| ≤
      |shear Q P|+Real.sqrt |h| * |shear ξ P| := by
    change |shear (fun i => Q i+Real.sqrt |h| * ξ i) P| ≤ _
    rw [shear_add_scale]
    simpa only [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] using
      abs_add_le (shear Q P) (Real.sqrt |h| * shear ξ P)
  have hy := phase_young (scaleBound ε) (Real.sqrt |h|) ξ P
  rw [Real.sq_sqrt (abs_nonneg h)] at hy
  have hb' := mul_le_mul_of_nonneg_left h1
    (show 0 ≤ 16*(scaleBound ε)^2*momentumBound P from by positivity [momentumBound_nonnegative P])
  have ht' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*scaleBound ε by positivity)
  nlinarith

theorem clockRatio_square_bound (ε q h r : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ‖phaseRatio ε r q h‖^2 ≤ Real.exp (|r|/ε) := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (phaseRatio_norm_bound ε r q h hε hh hb) 2
  rw [← Real.exp_nat_mul] at ht
  convert ht using 1
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

def amplitudeBound (ε : ℝ) (Q P : Transverse) : ℝ :=
  Real.exp (8*(scaleBound ε)^2*energy Q+4*scaleBound ε*|shear Q P|+
    16*(scaleBound ε)^2*momentumBound P)

theorem density_bound (ε q h r : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ ε/2) (h1 : |h| ≤ 1) (Q P ξ : Transverse) :
    density ε q h r Q P ξ ≤
      Real.exp (|r|/ε)*amplitudeBound ε Q P*Real.exp (-energy ξ/4) := by
  rw [density_factor,norm_mul,mul_pow]
  have hg := gaussianFactor_square_bound ε q h hε hh hb hsmall h1 Q ξ
  have hp := mul_le_mul (clockRatio_square_bound ε q h r hε hh hb)
    (rescaledRatio_square_bound ε q h hε hh hb (by linarith) h1 Q P ξ)
    (sq_nonneg _) (Real.exp_pos _).le
  have ht := mul_le_mul hg hp (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
  apply ht.trans_eq
  unfold amplitudeBound
  simp only [← Real.exp_add]
  congr 1
  ring

theorem clockFactor_square_bound (a u h : ℝ) (ha : 0 ≤ a) (h1 : |h| ≤ 1) :
    ‖clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)‖^2 ≤
      Real.exp (a/2)*‖clockFactor a (u:ℂ)‖^2 := by
  simp only [clockFactor,Complex.norm_exp,← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp [pow_two,Complex.mul_re,Complex.mul_im]
  have hs : h^2 ≤ 1 := by nlinarith [sq_abs h,abs_nonneg h]
  nlinarith [mul_le_mul_of_nonneg_left hs ha]

theorem centeredLine_bound (ε a u h r : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ ε/2) (h1 : |h| ≤ 1) (Q P ξ : Transverse) :
    ‖centeredLine ε a u h r Q P ξ‖^2 ≤
      Real.exp (|r|/ε+a/2)*amplitudeBound ε Q P*
        ‖clockFactor a (u:ℂ)‖^2*Real.exp (-energy ξ/4) := by
  rw [centeredLine_square ε a u h r hε]
  have ht := mul_le_mul (clockFactor_square_bound a u h ha h1)
    (density_bound ε u h r hε hh hb hsmall h1 Q P ξ)
    (show 0 ≤ density ε u h r Q P ξ from sq_nonneg _) (by positivity)
  apply ht.trans_eq
  rw [Real.exp_add]
  ring

#print axioms transverseRatio_bound
#print axioms rescaledRatio_square_bound
#print axioms clockRatio_square_bound
#print axioms density_bound
#print axioms clockFactor_square_bound
#print axioms centeredLine_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDensityBound
