/- Classical clock dissipation selects only the three ordered outputs.
Its exact time rescaling cancels the exponential-time denominator. -/
import UnifiedTheory.Audit.KFCausalAveragedOutputRescaling
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorDissipationRescaling
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorQuantumVelocityOutput (classicalOutput classicalOutput_apply classicalFactor)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε)
local notation "C" => classicalOutput ε hε

theorem finite_pairing (s t : ℝ) (g : Output (Fin 8) Hilbert) :
    inner ℂ (timeOutput s t g) (C (timeOutput s t g))=
      (Real.exp (2*(t-s)):ℂ)*inner ℂ g (C g) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<5
  · simp only [classicalOutput_apply,classicalFactor,hi,if_true,
      ContinuousLinearMap.zero_apply,inner_zero_right,mul_zero]
  · have hi3 : ¬ i.val<3 := by omega
    simp only [classicalOutput_apply,classicalFactor,hi,if_false,timeOutput_apply,hi3,
      map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
    have he : (Real.exp (t-s):ℂ)*(Real.exp (t-s):ℂ)=(Real.exp (2*(t-s)):ℂ) := by
      rw [← Complex.ofReal_mul,← Real.exp_add]
      congr 2
      ring
    rw [← mul_assoc,he]

theorem averaged_pairing (s t : ℝ) (g : EnergyOutputSpace) :
    inner ℂ (timeOutputLp s t g) ((C).compLp (timeOutputLp s t g))=
      (Real.exp (2*(t-s)):ℂ)*inner ℂ g ((C).compLp g) := by
  have he : (fun θ => inner ℂ (timeOutputLp s t g θ) ((C).compLp (timeOutputLp s t g) θ)) =ᵐ[angleMeasure]
      fun θ => (Real.exp (2*(t-s)):ℂ)*inner ℂ (g θ) ((C).compLp g θ) := by
    filter_upwards [(timeOutput s t).coeFn_compLp g,(C).coeFn_compLp (timeOutputLp s t g),
      (C).coeFn_compLp g] with θ ht hc hg
    change timeOutputLp s t g θ=timeOutput s t (g θ) at ht
    rw [hc,ht,hg,finite_pairing]
  rw [L2.inner_def,integral_congr_ae he,integral_const_mul,← L2.inner_def]

theorem averaged_real_pairing (s t : ℝ) (g : EnergyOutputSpace) :
    (inner ℂ (timeOutputLp s t g) ((C).compLp (timeOutputLp s t g))).re=
      Real.exp (2*(t-s))*(inner ℂ g ((C).compLp g)).re := by
  rw [averaged_pairing]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

#print axioms finite_pairing
#print axioms averaged_pairing
#print axioms averaged_real_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorDissipationRescaling
