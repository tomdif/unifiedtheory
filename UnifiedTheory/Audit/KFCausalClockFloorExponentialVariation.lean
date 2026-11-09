/- Forward physical test-vector variation on the actual quantum flow.
Its bound grows as exp(2t), with a time-independent constant derived
from the initial energy of the state and of the form-domain test. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "U" => evolution ε hε h hne hb m g k
local notation "E" => timeEnergy ε hε h hne hb m g k
local notation "Q" => referenceFormOperator ε hε h hne hb m g k

def slope (s t : ℝ) (w z : V) : ℂ :=
  (Complex.I*((1/h:ℝ):ℂ))*inner ℂ (F s t w) (Q t z)

def variationConstant (s : ℝ) (w z : V) : ℝ :=
  |1/h| * Real.exp (-2*s)*(E s w+E s z+1)

theorem variationConstant_nonnegative (s : ℝ) (w z : V) :
    0 ≤ variationConstant ε hε h hne hb m g k s w z := by
  have hw := timeEnergy_nonneg ε hε h hne hb m g k s w
  have hz := timeEnergy_nonneg ε hε h hne hb m g k s z
  unfold variationConstant
  positivity

theorem pairing_derivative (s t : ℝ) (w z : V) :
    HasDerivAt (fun r => inner ℂ (U s r (J w)) (J z))
      (slope ε hε h hne hb m g k s t w z) t := by
  let W := weakTrajectory ε hε h hne hb m g k s w
  have hd := mass_pairing_derivative ε hε h hne hb m g k s w W t z
  have he : (fun r => inner ℂ (massState ε hε h hne hb m g k s w W r) z) =
      (fun r => inner ℂ (U s r (J w)) (J z)) := by
    funext r
    rw [evolution_embedding]
    exact mass_left_pairing ε hε h hne hb m g k (F s r w) z
  have hs : inner ℂ (massSlope ε hε h hne hb m g k s w W t) z =
      slope ε hε h hne hb m g k s t w z :=
    massSlope_pairing ε hε h hne hb m g k s w W t z
  exact (congrArg₂ (fun (f : ℝ → ℂ) d => HasDerivAt f d t) he hs).mp hd

theorem slope_bound (s t : ℝ) (hst : s ≤ t) (w z : V) :
    ‖slope ε hε h hne hb m g k s t w z‖ ≤
      variationConstant ε hε h hne hb m g k s w z*Real.exp (2*t) := by
  let A := fun u : V => energyOutput ε hε h hne hb m g k t
    (formTransfer ε hε h hne hb m g k 0 t u)
  have hw : ‖A (F s t w)‖^2 ≤ Real.exp (2*(t-s))*E s w := by
    have he := formFlow_energy_bound ε hε h hne hb m g k s t w
    rw [abs_of_nonneg (sub_nonneg.mpr hst)] at he
    exact (timeEnergy_actual ε hε h hne hb m g k t (F s t w)).le.trans he
  have hz : ‖A z‖^2 ≤ Real.exp (2*(t-s))*E s z :=
    (timeEnergy_actual ε hε h hne hb m g k t z).le.trans
      (timeEnergy_comparison ε hε h hne hb m g k s t hst z).2
  have hp : ‖A (F s t w)‖*‖A z‖ ≤ Real.exp (2*(t-s))*(E s w+E s z+1) := by
    nlinarith [sq_nonneg (‖A (F s t w)‖-‖A z‖),
      timeEnergy_nonneg ε hε h hne hb m g k s w,
      timeEnergy_nonneg ε hε h hne hb m g k s z,Real.exp_pos (2*(t-s))]
  have hi : ‖inner ℂ (F s t w) (Q t z)‖ ≤ Real.exp (2*(t-s))*(E s w+E s z+1) := by
    rw [referenceForm_represents_closed_form]
    exact (norm_inner_le_norm (𝕜 := ℂ) (A (F s t w)) (A z)).trans hp
  have he : Real.exp (2*(t-s)) = Real.exp (-2*s)*Real.exp (2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : ‖Complex.I*((1/h:ℝ):ℂ)‖ = |1/h| := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [slope,norm_mul,hc]
  calc
    _ ≤ |1/h| * (Real.exp (2*(t-s))*(E s w+E s z+1)) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = _ := by rw [he]; unfold variationConstant; ring

theorem pairing_variation (s a b : ℝ) (hsa : s ≤ a) (hab : a ≤ b) (w z : V) :
    ‖inner ℂ (U s b (J w)) (J z)-inner ℂ (U s a (J w)) (J z)‖ ≤
      variationConstant ε hε h hne hb m g k s w z*Real.exp (2*b)*(b-a) := by
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ Set.Icc a b) => (pairing_derivative ε hε h hne hb m g k s r w z).hasDerivWithinAt)
    (fun r hr => (slope_bound ε hε h hne hb m g k s r (hsa.trans hr.1) w z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show 2*r ≤ 2*b by linarith [hr.2]))
        (variationConstant_nonnegative ε hε h hne hb m g k s w z)))
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hd

#print axioms variationConstant_nonnegative
#print axioms pairing_derivative
#print axioms slope_bound
#print axioms pairing_variation
end
end UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation
