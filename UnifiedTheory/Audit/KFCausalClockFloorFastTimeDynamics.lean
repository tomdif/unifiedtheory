/- The actual full weak evolution in exponential time. The static
remainder is retained, tends to zero for each fixed form test, and has a
finite square-integral budget. No autonomous propagator limit is claimed. -/
import UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
import UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFastTimeDynamics
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
open UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation (pairing_derivative slope)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "U" => evolution ε hε h hne hb m g k
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "Q" => referenceFormOperator ε hε h hne hb m g k

def leading (s u : ℝ) (w z : V) : ℂ :=
  (Complex.I*((1/(2*h):ℝ):ℂ))*inner ℂ (B (F s (physicalTime u) w)) (B z)
def remainder (s u : ℝ) (w z : V) : ℂ :=
  (Complex.I*((1/(2*h*u):ℝ):ℂ))*inner ℂ (A (F s (physicalTime u) w)) (A z)
def testCost (z : V) : ℝ := ‖A z‖^2/(4*h^2)

theorem weak_derivative (s u : ℝ) (hu : 0 < u) (w z : V) :
    HasDerivAt (fun r => inner ℂ (U s (physicalTime r) (J w)) (J z))
      (leading ε hε h hne hb m g k s u w z+remainder ε hε h hne hb m g k s u w z) u := by
  have hd := (pairing_derivative ε hε h hne hb m g k s (physicalTime u) w z).scomp u
    (physicalTime_derivative u hu)
  have hp : inner ℂ (F s (physicalTime u) w) (Q (physicalTime u) z) =
      inner ℂ (A (F s (physicalTime u) w)) (A z)+(u:ℂ)*inner ℂ (B (F s (physicalTime u) w)) (B z) := by
    simpa only [exp_physicalTime u hu] using
      KFCausalBoundedFormCurve.formOperator_pairing A B (physicalTime u) (F s (physicalTime u) w) z
  convert hd using 1
  dsimp only [KFCausalClockFloorExponentialVariation.slope]
  rw [hp]
  change leading ε hε h hne hb m g k s u w z+remainder ε hε h hne hb m g k s u w z =
    ((1/(2*u):ℝ):ℂ)*((Complex.I*((1/h:ℝ):ℂ))*_)
  unfold leading remainder
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hu.ne',Complex.ofReal_ne_zero.mpr hne]
  ring

theorem remainder_continuous (s : ℝ) (w z : V) :
    ContinuousOn (fun u => remainder ε hε h hne hb m g k s u w z) (Set.Ioi 0) := by
  have hf := (A).continuous.comp_continuousOn
    ((formFlow_continuous ε hε h hne hb m g k s w).comp_continuousOn physicalTime_continuous)
  have hr : ContinuousOn (fun u : ℝ => 1/(2*h*u)) (Set.Ioi 0) :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun _ hu => mul_ne_zero (mul_ne_zero (by norm_num) hne) (ne_of_gt hu))
  exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hr)).mul
    (hf.inner continuousOn_const)

theorem remainder_square_bound (s u : ℝ) (hu : 0 < u) (w z : V) :
    ‖remainder ε hε h hne hb m g k s u w z‖^2 ≤
      testCost ε hε h hne hb m g k z*fastLoss ε hε h hne hb m g k s u w := by
  simp only [remainder,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  have hi := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) (A (F s (physicalTime u) w)) (A z)) 2
  calc
    _ ≤ (1/(2*h*u))^2*(‖A (F s (physicalTime u) w)‖*‖A z‖)^2 :=
      mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = _ := by unfold testCost fastLoss staticEnergy; field_simp [hu.ne',hne]; ring

theorem remainder_integral_bound (s a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (w z : V) :
    (∫ u in a..b, ‖remainder ε hε h hne hb m g k s u w z‖^2) ≤
      testCost ε hε h hne hb m g k z*
        (fastEnergy ε hε h hne hb m g k s a w-fastEnergy ε hε h hne hb m g k s b w) := by
  have hc := ((remainder_continuous ε hε h hne hb m g k s w z).norm.pow 2).mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hu => ha.trans_le hu.1)
  have hl := (fastLoss_continuous ε hε h hne hb m g k s w).mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hu => ha.trans_le hu.1)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable_of_Icc hab)
    ((continuousOn_const.mul hl).intervalIntegrable_of_Icc hab)
    (fun u hu => remainder_square_bound ε hε h hne hb m g k s u (ha.trans_le hu.1) w z)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul,fastLoss_integral ε hε h hne hb m g k s a b ha hab w] at hi
  exact hi

theorem remainder_tail_budget (s : ℝ) (w z : V) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ a b, R ≤ a → a ≤ b →
      (∫ u in a..b, ‖remainder ε hε h hne hb m g k s u w z‖^2) < η := by
  obtain ⟨ℓ,_,hl,ht⟩ := fastEnergy_limit ε hε h hne hb m g k s w
  have hz : Tendsto (fun u => testCost ε hε h hne hb m g k z*
      (fastEnergy ε hε h hne hb m g k s u w-ℓ)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using (ht.sub_const ℓ).const_mul (testCost ε hε h hne hb m g k z)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds hη))
  refine ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a b ha hab
  have ha' : 0 < a := (lt_of_lt_of_le zero_lt_one (le_max_right R 1)).trans_le ha
  have hi := remainder_integral_bound ε hε h hne hb m g k s a b ha' hab w z
  have hc : 0 ≤ testCost ε hε h hne hb m g k z := by unfold testCost; positivity
  exact (hi.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left (hl b) _) hc)).trans_lt
    (hR a ((le_max_left _ _).trans ha))

theorem remainder_tendsto_zero (s : ℝ) (w z : V) :
    Tendsto (fun u => remainder ε hε h hne hb m g k s u w z) atTop (𝓝 0) := by
  have he : ∀ᶠ u : ℝ in atTop, ‖remainder ε hε h hne hb m g k s u w z‖^2 ≤
      testCost ε hε h hne hb m g k z*fastLoss ε hε h hne hb m g k s u w :=
    (eventually_gt_atTop (0:ℝ)).mono (fun u hu => remainder_square_bound ε hε h hne hb m g k s u hu w z)
  have hsq := squeeze_zero' (Eventually.of_forall (fun u => sq_nonneg
      ‖remainder ε hε h hne hb m g k s u w z‖)) he
    (show Tendsto (fun u => testCost ε hε h hne hb m g k z*fastLoss ε hε h hne hb m g k s u w) atTop (𝓝 0) by
      simpa only [mul_zero] using (fastLoss_tendsto_zero ε hε h hne hb m g k s w).const_mul (testCost ε hε h hne hb m g k z))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

theorem remainder_square_integrable (s a : ℝ) (ha : 0 < a) (w z : V) :
    IntegrableOn (fun u => ‖remainder ε hε h hne hb m g k s u w z‖^2) (Set.Ioi a) := by
  have hc := ((remainder_continuous ε hε h hne hb m g k s w z).norm.pow 2).mono
    (show Set.Ioi a ⊆ Set.Ioi 0 from fun _ hu => ha.trans hu)
  apply ((fastLoss_integrable ε hε h hne hb m g k s a ha w).const_mul
    (testCost ε hε h hne hb m g k z)).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact remainder_square_bound ε hε h hne hb m g k s u (ha.trans hu) w z

#print axioms weak_derivative
#print axioms remainder_continuous
#print axioms remainder_square_bound
#print axioms remainder_integral_bound
#print axioms remainder_tail_budget
#print axioms remainder_tendsto_zero
#print axioms remainder_square_integrable
end
end UnifiedTheory.Audit.KFCausalClockFloorFastTimeDynamics
