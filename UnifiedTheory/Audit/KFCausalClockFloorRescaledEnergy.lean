/- An exact decreasing energy and a finite static-output dissipation
budget for the actual full evolution. This is not clock recovery. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
import Mathlib.Topology.Order.MonotoneConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance (energy power energy_derivative)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "E" => energy ε hε h hne hb m g k

def staticEnergy (s t : ℝ) (w : V) : ℝ := ‖A (F s t w)‖^2
def scaledEnergy (s t : ℝ) (w : V) : ℝ := Real.exp (-2*t)*E s t w
def staticLoss (s t : ℝ) (w : V) : ℝ := Real.exp (-2*t)*staticEnergy ε hε h hne hb m g k s t w

theorem energy_split (s t : ℝ) (w : V) :
    E s t w = staticEnergy ε hε h hne hb m g k s t w+Real.exp (2*t)*‖B (F s t w)‖^2 := rfl

theorem scaled_split (s t : ℝ) (w : V) :
    scaledEnergy ε hε h hne hb m g k s t w =
      staticLoss ε hε h hne hb m g k s t w+‖B (F s t w)‖^2 := by
  have he : Real.exp (-2*t)*Real.exp (2*t) = 1 := by
    rw [← Real.exp_add,show -2*t+2*t = 0 by ring,Real.exp_zero]
  have algebra (x y : ℝ) : Real.exp (-2*t)*(x+Real.exp (2*t)*y) = Real.exp (-2*t)*x+y := by
    rw [mul_add,← mul_assoc,he,one_mul]
  exact (congrArg (fun x : ℝ => Real.exp (-2*t)*x) (energy_split ε hε h hne hb m g k s t w)).trans
    (algebra (staticEnergy ε hε h hne hb m g k s t w) (‖B (F s t w)‖^2))

theorem staticEnergy_continuous (s : ℝ) (w : V) :
    Continuous (fun t => staticEnergy ε hε h hne hb m g k s t w) :=
  ((A).continuous.comp (formFlow_continuous ε hε h hne hb m g k s w)).norm.pow 2

theorem staticLoss_continuous (s : ℝ) (w : V) :
    Continuous (fun t => staticLoss ε hε h hne hb m g k s t w) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (staticEnergy_continuous ε hε h hne hb m g k s w)

theorem scaled_nonnegative (s t : ℝ) (w : V) :
    0 ≤ scaledEnergy ε hε h hne hb m g k s t w :=
  mul_nonneg (Real.exp_pos _).le (timeEnergy_nonneg ε hε h hne hb m g k t (F s t w))

theorem scaled_derivative (s t : ℝ) (w : V) :
    HasDerivAt (fun r => scaledEnergy ε hε h hne hb m g k s r w)
      (-2*staticLoss ε hε h hne hb m g k s t w) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2)).exp).mul
    (energy_derivative ε hε h hne hb m g k s t w)
  convert hd using 1
  rw [energy_split]
  simp only [id_eq,power,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,
    ← Real.exp_nat_mul,Nat.cast_ofNat,staticLoss]
  ring

theorem scaled_antitone (s : ℝ) (w : V) :
    Antitone (fun t => scaledEnergy ε hε h hne hb m g k s t w) :=
  antitone_of_hasDerivAt_nonpos (fun t => scaled_derivative ε hε h hne hb m g k s t w)
    (fun _ => mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

theorem scaled_limit (s : ℝ) (w : V) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ ≤ scaledEnergy ε hε h hne hb m g k s t w) ∧
      Tendsto (fun t => scaledEnergy ε hε h hne hb m g k s t w) atTop (𝓝 ℓ) := by
  have h0 := fun t => scaled_nonnegative ε hε h hne hb m g k s t w
  have hd : BddBelow (Set.range (fun t => scaledEnergy ε hε h hne hb m g k s t w)) :=
    ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  exact ⟨⨅ t, scaledEnergy ε hε h hne hb m g k s t w,le_ciInf h0,
    fun t => ciInf_le hd t,tendsto_atTop_ciInf (scaled_antitone ε hε h hne hb m g k s w) hd⟩

theorem static_integral (s a b : ℝ) (w : V) :
    2*(∫ t in a..b, staticLoss ε hε h hne hb m g k s t w) =
      scaledEnergy ε hε h hne hb m g k s a w-scaledEnergy ε hε h hne hb m g k s b w := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => scaled_derivative ε hε h hne hb m g k s t w)
    ((continuous_const.mul (staticLoss_continuous ε hε h hne hb m g k s w)).intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul] at hi
  linarith only [hi]

theorem static_forward_budget (s a b : ℝ) (w : V) :
    (∫ t in a..b, staticLoss ε hε h hne hb m g k s t w) ≤
      scaledEnergy ε hε h hne hb m g k s a w/2 := by
  have hi := static_integral ε hε h hne hb m g k s a b w
  have hn := scaled_nonnegative ε hε h hne hb m g k s b w
  linarith

#print axioms energy_split
#print axioms scaled_split
#print axioms staticEnergy_continuous
#print axioms staticLoss_continuous
#print axioms scaled_nonnegative
#print axioms scaled_derivative
#print axioms scaled_antitone
#print axioms scaled_limit
#print axioms static_integral
#print axioms static_forward_budget
end
end UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy
