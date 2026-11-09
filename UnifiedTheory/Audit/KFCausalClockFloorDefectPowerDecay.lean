/- Strong decay of the real and shifted response powers, and of their
actual simultaneous energy-output action. The estimates are uniform in
the iteration number, without asserting a uniform rate of convergence. -/
import UnifiedTheory.Audit.KFCausalMultiplierPowerDecay
import UnifiedTheory.Audit.KFCausalInvariantRangeCore
import UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction
import UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
import UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)

theorem real_response_decay (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    Tendsto (fun n : ℕ => (residual (defectOperator ε hε) : Hilbert → Hilbert)^[n] f) atTop (𝓝 0) := by
  apply KFCausalMultiplierPowerDecay.iterate_tendsto_zero (responseOperator ε hε)
    (fun x : Configuration => (response ε x.1:ℂ)) (responseOperator_coe ε hε)
  · unfold response clock
    fun_prop
  · intro x
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (response_bounds ε x.1 hε).1]
    exact (response_bounds ε x.1 hε).2

theorem shifted_response_decay (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    Tendsto (fun n : ℕ => (residual (shiftedDefect ε hε h hh) : Hilbert → Hilbert)^[n] f) atTop (𝓝 0) :=
  KFCausalMultiplierPowerDecay.iterate_tendsto_zero (shiftedResponse ε hε h hh)
    (fun x => 1-physicalSymbol ε h x) (shiftedResponse_coe ε hε h hh)
    (continuous_const.sub (physicalSymbol_continuous ε hε h hh)).measurable
    (physical_response_strict ε hε h hh) f

theorem factor_residual_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (i : Fin 8) (g : Hilbert) :
    ‖residual (factorAction ε hε h hh i) g‖ ≤ ‖g‖ := by
  by_cases hi : i.val < 5
  · simpa only [factorAction,hi,if_true] using responseOperator_norm ε hε g
  · simpa only [factorAction,hi,if_false] using shiftedResponse_norm ε hε h hh g

theorem factor_response_decay (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (i : Fin 8) (g : Hilbert) :
    Tendsto (fun n : ℕ => (residual (factorAction ε hε h hh i) : Hilbert → Hilbert)^[n] g) atTop (𝓝 0) := by
  by_cases hi : i.val < 5
  · simpa only [factorAction,hi,if_true] using real_response_decay ε hε g
  · simpa only [factorAction,hi,if_false] using shifted_response_decay ε hε h hh g

theorem output_residual_iterate (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (g : Output (Fin 8) Hilbert) (n : ℕ) (i : Fin 8) :
    ((residual (outputAction ε hε h hh) : Output (Fin 8) Hilbert → Output (Fin 8) Hilbert)^[n] g) i =
      (residual (factorAction ε hε h hh i) : Hilbert → Hilbert)^[n] (g i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      simp only [KFCausalInvariantRangeCore.residual,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply,PiLp.sub_apply,outputAction_apply] at ih ⊢
      rw [ih]

theorem output_response_decay (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (g : Output (Fin 8) Hilbert) :
    Tendsto (fun n : ℕ =>
      (residual (outputAction ε hε h hh) : Output (Fin 8) Hilbert → Output (Fin 8) Hilbert)^[n] g)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => fun i : Fin 8 =>
      ((residual (outputAction ε hε h hh) : Output (Fin 8) Hilbert → Output (Fin 8) Hilbert)^[n] g) i)
      atTop (𝓝 (fun _ => (0:Hilbert))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [output_residual_iterate] using factor_response_decay ε hε h hh i (g i)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 8 => Hilbert)).continuousAt.tendsto.comp ht

theorem output_residual_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (g : Output (Fin 8) Hilbert) :
    ‖residual (outputAction ε hε h hh) g‖ ≤ ‖g‖ := by
  have hs : ‖residual (outputAction ε hε h hh) g‖^2 ≤ ‖g‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    simpa only [KFCausalInvariantRangeCore.residual,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      PiLp.sub_apply,outputAction_apply] using
      pow_le_pow_left₀ (norm_nonneg _) (factor_residual_norm ε hε h hh i (g i)) 2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem output_iterate_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (g : Output (Fin 8) Hilbert) (n : ℕ) :
    ‖(residual (outputAction ε hε h hh) : Output (Fin 8) Hilbert → Output (Fin 8) Hilbert)^[n] g‖ ≤ ‖g‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (output_residual_norm ε hε h hh _).trans ih

#print axioms real_response_decay
#print axioms shifted_response_decay
#print axioms factor_residual_norm
#print axioms factor_response_decay
#print axioms output_residual_iterate
#print axioms output_response_decay
#print axioms output_residual_norm
#print axioms output_iterate_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
