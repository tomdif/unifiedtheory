/- A concrete nonzero physical charge-zero trial for the optional clock
floor, with the clock prefactor needed before inverse dressing. The
Hamiltonian energy-domain conclusion still requires ordered-domain work. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
import UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests (quadratic_exp_integrable)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
open UnifiedTheory.Audit.KFCausalStandingChargeOperator

theorem chart_square_lower (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    (ε^2/2)*s^2-1 ≤ (chart ε s)^2 := by
  by_cases hs : 0 ≤ s
  · have hb : 0 ≤ ε*s := mul_nonneg hε.le hs
    have he : ε*s ≤ chart ε s := by unfold chart; linarith [Real.exp_pos s]
    have hsq := (sq_le_sq₀ hb (hb.trans he)).mpr he
    nlinarith [sq_nonneg (ε*s)]
  · have he : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr (le_of_not_ge hs)
    have he2 : (Real.exp s)^2 ≤ 1 := by nlinarith [Real.exp_pos s]
    unfold chart
    nlinarith [sq_nonneg (2*Real.exp s+ε*s)]

def realClock (ε a s : ℝ) : ℝ := (1+ε*Real.exp (-s))*Real.exp (-a*(chart ε s)^2)
def clockFunction (ε a : ℝ) (s : ℝ) : ℂ := (realClock ε a s:ℂ)

theorem clockFunction_continuous (ε a : ℝ) : Continuous (clockFunction ε a) := by
  unfold clockFunction realClock chart
  fun_prop

theorem realClock_positive (ε a s : ℝ) (hε : 0 ≤ ε) : 0 < realClock ε a s := by
  unfold realClock
  positivity

theorem clockFunction_ne_zero (ε a : ℝ) (hε : 0 ≤ ε) (s : ℝ) : clockFunction ε a s ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (realClock_positive ε a s hε).ne'

theorem realClock_square_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) (s : ℝ) :
    (realClock ε a s)^2 ≤ 2*Real.exp (2*a)*
      (Real.exp (-(a*ε^2)*s^2)+ε^2*Real.exp (-(a*ε^2)*s^2-2*s)) := by
  have hchart := chart_square_lower ε hε s
  have hq : -2*a*(chart ε s)^2 ≤ 2*a-(a*ε^2)*s^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hchart ha]
  have hexp := Real.exp_le_exp.mpr hq
  have hs : (Real.exp (-s))^2 = Real.exp (-2*s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hp : (1+ε*Real.exp (-s))^2 ≤ 2+2*ε^2*Real.exp (-2*s) := by
    rw [← hs]
    nlinarith [sq_nonneg (1-ε*Real.exp (-s))]
  have hb := mul_le_mul hp hexp (Real.exp_pos _).le (by positivity)
  have he : Real.exp (2*a-(a*ε^2)*s^2) =
      Real.exp (2*a)*Real.exp (-(a*ε^2)*s^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ht : Real.exp (-(a*ε^2)*s^2-2*s) =
      Real.exp (-(a*ε^2)*s^2)*Real.exp (-2*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreal : (realClock ε a s)^2 =
      (1+ε*Real.exp (-s))^2*Real.exp (-2*a*(chart ε s)^2) := by
    rw [realClock,mul_pow,← Real.exp_nat_mul]
    congr 1
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hreal]
  apply hb.trans_eq
  rw [he,ht]
  ring

theorem clockFunction_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (clockFunction ε a) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (clockFunction_continuous ε a).aestronglyMeasurable).mpr
  have h0 := integrable_exp_neg_mul_sq (by positivity : 0 < a*ε^2)
  have h1 := quadratic_exp_integrable (a*ε^2) (-2) 0 (by positivity)
  have hi := (h0.add (h1.const_mul (ε^2))).const_mul (2*Real.exp (2*a))
  apply hi.mono' ((clockFunction_continuous ε a).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with s
  simp only [Real.norm_eq_abs,abs_sq,clockFunction,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Pi.add_apply,add_zero]
  convert realClock_square_bound ε a hε ha.le s using 1
  ring

def neutralWidth (hbar : ℝ) : ℝ := groundWidth hbar/32

theorem neutralWidth_positive (hbar : ℝ) (hh : hbar ≠ 0) : 0 < neutralWidth hbar :=
  div_pos (groundWidth_positive hbar hh) (by norm_num)

theorem neutralWidth_bound (hbar : ℝ) : 32*neutralWidth hbar ≤ groundWidth hbar := by
  unfold neutralWidth
  linarith

def trialState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) : Hilbert :=
  groundState hbar hh (neutralWidth hbar) (neutralWidth_positive hbar hh)
    (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)

theorem trialState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    trialState ε a hbar hε ha hh =ᵐ[volume]
      configurationProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a) :=
  groundState_coe hbar hh _ (neutralWidth_positive hbar hh) _ _ _

theorem trialState_ne_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    trialState ε a hbar hε ha hh ≠ 0 :=
  groundState_ne_zero hbar hh _ (neutralWidth_positive hbar hh) _ _ _
    (clockFunction_ne_zero ε a hε.le 0)

theorem trialState_mem_zeroSector (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    trialState ε a hbar hε ha hh ∈ zeroSector hbar hh :=
  groundState_mem_zeroSector hbar hh _ (neutralWidth_positive hbar hh) _ _ _

theorem trialState_charge_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (trialState ε a hbar hε ha hh,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr (trialState_mem_zeroSector ε a hbar hε ha hh)

#print axioms chart_square_lower
#print axioms clockFunction_continuous
#print axioms realClock_positive
#print axioms clockFunction_ne_zero
#print axioms realClock_square_bound
#print axioms clockFunction_memLp
#print axioms neutralWidth_positive
#print axioms neutralWidth_bound
#print axioms trialState_coe
#print axioms trialState_ne_zero
#print axioms trialState_mem_zeroSector
#print axioms trialState_charge_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
