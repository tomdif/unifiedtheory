/- The quantum-to-classical velocity error is controlled on the full
eight-component energy output and survives charge integration. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing
import UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3)
local notation "R" => outputAction ε hε hbar hh

def classicalFactor (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val < 5 then 0 else driftOperator ε hε

def classicalOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => classicalFactor ε hε i (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (classicalFactor ε hε i).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem classicalOutput_apply (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    classicalOutput ε hε g i = classicalFactor ε hε i (g i) := rfl

theorem driftOperator_norm (f : Hilbert) : ‖driftOperator ε hε f‖ ≤ (1/ε)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [driftOperator_coe ε hε f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply KFCausalClockFloorDefectTransportScalar.drift_bound ε _ hε
  constructor
  · exact (KFCausalClockFloorCanonicalDefect.defect_positive ε x.1 hε).le
  · rw [← realDefect_chart ε hε x.1]
    exact KFCausalClockFloorQuantumVelocityScalar.realDefect_le_one ε hε _

theorem classicalOutput_norm (g : Output (Fin 8) Hilbert) :
    ‖classicalOutput ε hε g‖ ≤ (1/ε)*‖g‖ := by
  have hb (i : Fin 8) : ‖classicalFactor ε hε i (g i)‖ ≤ (1/ε)*‖g i‖ := by
    unfold classicalFactor
    split
    · simp only [ContinuousLinearMap.zero_apply,norm_zero]
      positivity
    · exact driftOperator_norm ε hε (g i)
  have hs : ‖classicalOutput ε hε g‖^2 ≤ ((1/ε)*‖g‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [classicalOutput_apply,mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
  have hn : 0 ≤ (1/ε)*‖g‖ := by positivity
  nlinarith [norm_nonneg (classicalOutput ε hε g)]

theorem classicalOutputLp_pairing_bound (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    |(inner ℂ g ((classicalOutput ε hε).compLp g)).re| ≤ (1/ε)*‖g‖^2 := by
  have hn : ‖(classicalOutput ε hε).compLp g‖ ≤ (1/ε)*‖g‖ := by
    apply ((classicalOutput ε hε).norm_compLp_le g).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (classicalOutput_norm ε hε)
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  have hh' := mul_le_mul_of_nonneg_left hn (norm_nonneg g)
  nlinarith

include hne in
theorem factor_velocity_error (i : Fin 8) (f : Hilbert) :
    |(-2/hbar)*(inner ℂ f (factorAction ε hε hbar hh i f)).im-
      (inner ℂ f (classicalFactor ε hε i f)).re| ≤ (20*|hbar|/ε^2)*‖f‖^2 := by
  unfold factorAction classicalFactor
  split
  · simp only [ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re,
      defect_inner_im_zero ε hε,mul_zero,sub_self,abs_zero]
    positivity
  · exact velocity_pairing_norm_error ε hε hbar hne hh f

include hne in
theorem output_velocity_error (g : Output (Fin 8) Hilbert) :
    |(-2/hbar)*(inner ℂ g (R g)).im-(inner ℂ g (classicalOutput ε hε g)).re| ≤
      (20*|hbar|/ε^2)*‖g‖^2 := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Complex.im_sum,Complex.re_sum,Finset.mul_sum,
    ← Finset.sum_sub_distrib,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact factor_velocity_error ε hε hbar hne hh i (g i)

include hne in
theorem outputLp_velocity_error (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    |(-2/hbar)*(inner ℂ g ((R).compLp g)).im-
      (inner ℂ g ((classicalOutput ε hε).compLp g)).re| ≤
      (20*|hbar|/ε^2)*‖g‖^2 := by
  apply KFCausalMultiplierVelocityPairing.integrated_velocity_bound
  filter_upwards [(R).coeFn_compLp g,(classicalOutput ε hε).coeFn_compLp g] with θ hr hc
  rw [hr,hc]
  exact output_velocity_error ε hε hbar hne hh (g θ)

#print axioms classicalOutput_apply
#print axioms driftOperator_norm
#print axioms classicalOutput_norm
#print axioms classicalOutputLp_pairing_bound
#print axioms factor_velocity_error
#print axioms output_velocity_error
#print axioms outputLp_velocity_error

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
