/- Quantitative control of all eight energy outputs for the actual radial
observable. The only additive correction is the second momentum row;
its bound is independent of time and all matter couplings. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action action_norm)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (output_norm)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap correctionMap outputMap_norm)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)

def extra : Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun f := WithLp.toLp 2 (Pi.single 2 ((Real.sqrt (1/2):ℂ) • correction ε hε h δ v hδ 1 f))
  map_add' f g := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add,smul_add]
  map_smul' c f := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smul]
    module
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => by
    fin_cases i <;> simp <;> fun_prop))


def amplification (ε h δ v : ℝ) : ℝ := Real.exp (v^2*h^2/(8*δ*ε^2))

include hδ in
theorem amplification_one_le : 1 ≤ amplification ε h δ v := by
  apply Real.one_le_exp_iff.mpr
  positivity

theorem extra_norm (f : Hilbert) :
    ‖extra ε hε h δ v hδ f‖ = Real.sqrt (1/2)*‖correction ε hε h δ v hδ 1 f‖ := by
  change ‖(WithLp.toLp 2 (Pi.single 2 ((Real.sqrt (1/2):ℂ) • correction ε hε h δ v hδ 1 f)) : Output (Fin 8) Hilbert)‖ = _
  rw [PiLp.norm_toLp_single,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem extra_bound (f : Hilbert) :
    ‖extra ε hε h δ v hδ f‖ ≤ |h| *responseConstant ε δ v*‖f‖ := by
  rw [extra_norm]
  exact (mul_le_mul_of_nonneg_left (correction_second_bound ε hε h δ v hδ f)
    (Real.sqrt_nonneg _)).trans_eq (by unfold responseConstant; ring)

theorem physical_correction (m g k t : ℝ) (f : Hilbert) :
    correctionMap (factorCorrection ε δ v hε hδ h) (energyWeight m g k t) f =
      extra ε hε h δ v hδ f := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [correctionMap,factorCorrection,energyWeight,extra,
      correction_other ε hε h δ v hδ 0 (by decide),
      correction_other ε hε h δ v hδ 2 (by decide),
      correction_other ε hε h δ v hδ 3 (by decide)]

variable (hh : |h| ≤ 2*Real.pi*ε/3)

def outputAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε δ v hε hδ h hh)

theorem outputAction_norm (y : Output (Fin 8) Hilbert) :
    ‖outputAction ε hε h δ v hδ hh y‖ ≤ amplification ε h δ v*‖y‖ := by
  have hB : 1 ≤ amplification ε h δ v := amplification_one_le ε h δ v hδ
  apply outputMap_norm _ _ (by linarith)
  intro i f
  have hp := (action_norm h δ v hδ f).trans
    (le_mul_of_one_le_left (norm_nonneg f) hB)
  have hq := output_norm ε h δ v hε hδ hh f
  fin_cases i <;> first | exact hp | exact hq

theorem transformedOutput_eq (m g k t : ℝ) (f : Hilbert) (y : Output (Fin 8) Hilbert) :
    transformedOutput ε δ v hε hδ h hh (energyWeight m g k t) f y =
      outputAction ε hε h δ v hδ hh y+extra ε hε h δ v hδ f := by
  rw [transformedOutput,physical_correction]
  rfl

theorem output_bound (f : Hilbert) (y : Output (Fin 8) Hilbert) :
    ‖outputAction ε hε h δ v hδ hh y+extra ε hε h δ v hδ f‖ ≤
      amplification ε h δ v*‖y‖+|h| *responseConstant ε δ v*‖f‖ :=
  (norm_add_le _ _).trans (add_le_add
    (outputAction_norm ε hε h δ v hδ hh y) (extra_bound ε hε h δ v hδ f))

#print axioms amplification_one_le
#print axioms extra_norm
#print axioms extra_bound
#print axioms physical_correction
#print axioms outputAction_norm
#print axioms transformedOutput_eq
#print axioms output_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound
