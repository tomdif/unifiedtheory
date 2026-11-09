/- The retained fast-time remainder is represented by an actual vector
in the reference form Hilbert space. Its norm controls all form tests
uniformly, is square-integrable, and tends to zero. This is a form-dual
estimate, not a physical Hilbert-norm scattering bound. -/
import UnifiedTheory.Audit.KFCausalClockFloorFastTimeDynamics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorFastTimeDualError
noncomputable section
open Filter MeasureTheory
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFastTimeDynamics (remainder)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "A" => staticMap ε hε h hne hb m g k

def errorVector (s u : ℝ) (w : V) : V :=
  conj (Complex.I*((1/(2*h*u):ℝ):ℂ)) • (A).adjoint (A (F s (physicalTime u) w))

theorem error_pairing (s u : ℝ) (w z : V) :
    remainder ε hε h hne hb m g k s u w z =
      inner ℂ (errorVector ε hε h hne hb m g k s u w) z := by
  let c : ℂ := Complex.I*((1/(2*h*u):ℝ):ℂ)
  let x : V := F s (physicalTime u) w
  change c*inner ℂ (A x) (A z) = inner ℂ (conj c • (A).adjoint (A x)) z
  symm
  calc
    _ = conj (conj c)*inner ℂ ((A).adjoint (A x)) z :=
      inner_smul_left (𝕜 := ℂ) ((A).adjoint (A x)) z (conj c)
    _ = c*inner ℂ ((A).adjoint (A x)) z :=
      congrArg (fun q : ℂ => q*inner ℂ ((A).adjoint (A x)) z) (starRingEnd_self_apply c)
    _ = _ := congrArg (fun q : ℂ => c*q) ((A).adjoint_inner_left z (A x))

theorem uniform_weak_bound (s u : ℝ) (w z : V) :
    ‖remainder ε hε h hne hb m g k s u w z‖ ≤
      ‖errorVector ε hε h hne hb m g k s u w‖*‖z‖ := by
  rw [error_pairing]
  exact norm_inner_le_norm _ _

theorem error_continuous (s : ℝ) (w : V) :
    ContinuousOn (fun u => errorVector ε hε h hne hb m g k s u w) (Set.Ioi 0) := by
  have hf := (A).adjoint.continuous.comp_continuousOn ((A).continuous.comp_continuousOn
    ((formFlow_continuous ε hε h hne hb m g k s w).comp_continuousOn physicalTime_continuous))
  have hr : ContinuousOn (fun u : ℝ => 1/(2*h*u)) (Set.Ioi 0) :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun _ hu => mul_ne_zero (mul_ne_zero (by norm_num) hne) (ne_of_gt hu))
  exact (Complex.continuous_conj.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hr))).smul hf

theorem error_square_bound (s u : ℝ) (hu : 0 < u) (w : V) :
    ‖errorVector ε hε h hne hb m g k s u w‖^2 ≤
      (1/(4*h^2))*fastLoss ε hε h hne hb m g k s u w := by
  have ha : ‖(A).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint,LinearIsometryEquiv.norm_map] using
      staticMap_norm_le_one ε hε h hne hb m g k
  have hn : ‖(A).adjoint (A (F s (physicalTime u) w))‖ ≤ ‖A (F s (physicalTime u) w)‖ :=
    ((A).adjoint.le_opNorm _).trans ((mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_eq (one_mul _))
  simp only [errorVector,norm_smul,Complex.norm_conj,norm_mul,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  calc
    _ ≤ (1/(2*h*u))^2*‖A (F s (physicalTime u) w)‖^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _)
    _ = _ := by
      unfold fastLoss KFCausalClockFloorRescaledEnergy.staticEnergy
      field_simp [hu.ne',hne]
      ring

theorem error_integral_bound (s a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (w : V) :
    (∫ u in a..b, ‖errorVector ε hε h hne hb m g k s u w‖^2) ≤
      (1/(4*h^2))*(fastEnergy ε hε h hne hb m g k s a w-fastEnergy ε hε h hne hb m g k s b w) := by
  have hc := ((error_continuous ε hε h hne hb m g k s w).norm.pow 2).mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hu => ha.trans_le hu.1)
  have hl := (fastLoss_continuous ε hε h hne hb m g k s w).mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hu => ha.trans_le hu.1)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable_of_Icc hab)
    ((continuousOn_const.mul hl).intervalIntegrable_of_Icc hab)
    (fun u hu => error_square_bound ε hε h hne hb m g k s u (ha.trans_le hu.1) w)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul,fastLoss_integral ε hε h hne hb m g k s a b ha hab w] at hi
  exact hi

theorem error_square_integrable (s a : ℝ) (ha : 0 < a) (w : V) :
    IntegrableOn (fun u => ‖errorVector ε hε h hne hb m g k s u w‖^2) (Set.Ioi a) := by
  have hc := ((error_continuous ε hε h hne hb m g k s w).norm.pow 2).mono
    (show Set.Ioi a ⊆ Set.Ioi 0 from fun _ hu => ha.trans hu)
  apply ((fastLoss_integrable ε hε h hne hb m g k s a ha w).const_mul (1/(4*h^2))).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact error_square_bound ε hε h hne hb m g k s u (ha.trans hu) w

theorem error_tendsto_zero (s : ℝ) (w : V) :
    Tendsto (fun u => errorVector ε hε h hne hb m g k s u w) atTop (𝓝 0) := by
  have he := (eventually_gt_atTop (0:ℝ)).mono (fun u hu => error_square_bound ε hε h hne hb m g k s u hu w)
  have hsq := squeeze_zero' (Eventually.of_forall (fun u => sq_nonneg
      ‖errorVector ε hε h hne hb m g k s u w‖)) he
    (show Tendsto (fun u => (1/(4*h^2))*fastLoss ε hε h hne hb m g k s u w) atTop (𝓝 0) by
      simpa only [mul_zero] using (fastLoss_tendsto_zero ε hε h hne hb m g k s w).const_mul (1/(4*h^2)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

#print axioms error_pairing
#print axioms uniform_weak_bound
#print axioms error_continuous
#print axioms error_square_bound
#print axioms error_integral_bound
#print axioms error_square_integrable
#print axioms error_tendsto_zero
end
end UnifiedTheory.Audit.KFCausalClockFloorFastTimeDualError
