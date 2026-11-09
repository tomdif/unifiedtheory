/- Higher clock-power rates on the actual eight-component, charge-averaged
energy output. The classical comparison is nonpositive; the quantum
upward rate is bounded by an explicit constant times abs(hbar). -/
import UnifiedTheory.Audit.KFCausalClockFloorPowerForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing
open UnifiedTheory.Audit.KFCausalClockFloorPowerForm (compLp_power_coe)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "R" => outputAction ε hε h hb

def powerFactor (n : ℕ) (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val < 5 then 0 else powerDriftOperator ε hε n

def powerOutput (n : ℕ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => powerFactor ε hε n i (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (powerFactor ε hε n i).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem powerOutput_apply (n : ℕ) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    powerOutput ε hε n g i = powerFactor ε hε n i (g i) := rfl

theorem outputAction_power_apply (n : ℕ) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    ((R^n) g) i = ((factorAction ε hε h hb i)^n) (g i) := by
  induction n with
  | zero => simp only [pow_zero,ContinuousLinearMap.one_apply]
  | succ n ih => simp only [pow_succ',ContinuousLinearMap.mul_apply,outputAction_apply,ih]

theorem powerOutput_nonpositive (n : ℕ) (g : Output (Fin 8) Hilbert) :
    (inner ℂ g (powerOutput ε hε n g)).re ≤ 0 := by
  rw [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_nonpos
  intro i _
  simp only [powerOutput_apply,powerFactor]
  split
  · simp only [ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re,le_refl]
  · exact powerDrift_pairing_nonpositive ε hε n (g i)

theorem powerOutputLp_nonpositive (n : ℕ) (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    (inner ℂ g ((powerOutput ε hε n).compLp g)).re ≤ 0 := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) g ((powerOutput ε hε n).compLp g))
  change (∫ θ, (inner ℂ (g θ) ((powerOutput ε hε n).compLp g θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (g θ) ((powerOutput ε hε n).compLp g θ) ∂angleMeasure).re at he
  rw [L2.inner_def,← he]
  apply integral_nonpos_of_ae
  filter_upwards [(powerOutput ε hε n).coeFn_compLp g] with θ hθ
  rw [hθ]
  exact powerOutput_nonpositive ε hε n (g θ)

include hne in
theorem factor_power_velocity_error (n : ℕ) (i : Fin 8) (f : Hilbert) :
    |(-2/h)*(inner ℂ f (((factorAction ε hε h hb i)^(n+1)) f)).im-
      (inner ℂ f (powerFactor ε hε n i f)).re| ≤ (errorConstant ε n*|h|)*‖f‖^2 := by
  unfold factorAction powerFactor
  split
  · simp only [ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re,
      defect_power_im_zero ε hε,mul_zero,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (errorConstant_nonnegative ε n) (abs_nonneg h)) (sq_nonneg _)
  · exact power_velocity_pairing_error ε hε h hne hb n f

include hne in
theorem output_power_velocity_error (n : ℕ) (g : Output (Fin 8) Hilbert) :
    |(-2/h)*(inner ℂ g ((R^(n+1)) g)).im-(inner ℂ g (powerOutput ε hε n g)).re| ≤
      (errorConstant ε n*|h|)*‖g‖^2 := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Complex.im_sum,Complex.re_sum,Finset.mul_sum,
    ← Finset.sum_sub_distrib,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [outputAction_power_apply,powerOutput_apply] using factor_power_velocity_error ε hε h hne hb n i (g i)

include hne in
theorem outputLp_power_velocity_error (n : ℕ) (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    |(-2/h)*(inner ℂ g (((ContinuousLinearMap.compLpL 2 angleMeasure R)^(n+1)) g)).im-
      (inner ℂ g ((powerOutput ε hε n).compLp g)).re| ≤ (errorConstant ε n*|h|)*‖g‖^2 := by
  apply KFCausalMultiplierVelocityPairing.integrated_velocity_bound
  filter_upwards [compLp_power_coe angleMeasure R (n+1) g,(powerOutput ε hε n).coeFn_compLp g] with θ hr hc
  rw [hr,hc]
  exact output_power_velocity_error ε hε h hne hb n (g θ)

include hne in
theorem outputLp_power_rate_upper (n : ℕ) (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    (-2/h)*(inner ℂ g (((ContinuousLinearMap.compLpL 2 angleMeasure R)^(n+1)) g)).im ≤ (errorConstant ε n*|h|)*‖g‖^2 := by
  have he := (abs_le.mp (outputLp_power_velocity_error ε hε h hne hb n g)).2
  have hn := powerOutputLp_nonpositive ε hε n g
  linarith

#print axioms powerOutput_apply
#print axioms outputAction_power_apply
#print axioms powerOutput_nonpositive
#print axioms powerOutputLp_nonpositive
#print axioms factor_power_velocity_error
#print axioms output_power_velocity_error
#print axioms outputLp_power_velocity_error
#print axioms outputLp_power_rate_upper

end
end UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityOutput
