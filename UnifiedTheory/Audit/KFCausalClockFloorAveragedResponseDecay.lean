/- Strong response-power decay on the actual charge-averaged form space.
The orbit-output estimate uses derived contractivity and vector-valued
L2 convergence, not an assumed uniform rate or charge-zero condition. -/
import UnifiedTheory.Audit.KFCausalLpStrongPowerDecay
import UnifiedTheory.Audit.KFCausalEmbeddedResponseDecay
import UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse (responseOperator_norm)
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => KFCausalClockFloorClosedEnergyDefect.energy_bound ε hε h hh
local notation "𝒱" => AveragedSpace ε hε h hb hne mass2 quartic vacuum t
local notation "J" => embedding ε hε h hb hne mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hb hne mass2 quartic vacuum t
local notation "F" => formAction ε hε h hne hh mass2 quartic vacuum t
local notation "R" => outputAction ε hε h hh
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure R

theorem outputLp_residual_decay (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    Tendsto (fun n : ℕ => (residual L : Lp (Output (Fin 8) Hilbert) 2 angleMeasure →
      Lp (Output (Fin 8) Hilbert) 2 angleMeasure)^[n] g) atTop (𝓝 0) := by
  exact KFCausalLpStrongPowerDecay.residual_tendsto_zero R
    (output_residual_norm ε hε h hh) (output_response_decay ε hε h hh) g

theorem outputLp_residual_norm (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    ‖residual L g‖ ≤ ‖g‖ := by
  exact KFCausalLpStrongPowerDecay.residual_norm R (output_residual_norm ε hε h hh) g

theorem form_residual_embedding (u : 𝒱) : J (residual F u) = residual (defectOperator ε hε) (J u) :=
  KFCausalEmbeddedResponseDecay.intertwine J F (defectOperator ε hε)
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t) u

theorem form_residual_output (u : 𝒱) : A (residual F u) = residual L (A u) :=
  KFCausalEmbeddedResponseDecay.intertwine A F L
    (formAction_output ε hε h hne hh mass2 quartic vacuum t) u

theorem form_residual_embedding_iterate (u : 𝒱) (n : ℕ) :
    J ((residual F : 𝒱 → 𝒱)^[n] u) = (residual (defectOperator ε hε) : Hilbert → Hilbert)^[n] (J u) :=
  KFCausalEmbeddedResponseDecay.intertwine_iterate J F (defectOperator ε hε)
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t) u n

theorem form_residual_output_iterate (u : 𝒱) (n : ℕ) :
    A ((residual F : 𝒱 → 𝒱)^[n] u) =
      (residual L : Lp (Output (Fin 8) Hilbert) 2 angleMeasure → Lp (Output (Fin 8) Hilbert) 2 angleMeasure)^[n] (A u) :=
  KFCausalEmbeddedResponseDecay.intertwine_iterate A F L
    (formAction_output ε hε h hne hh mass2 quartic vacuum t) u n

theorem form_residual_decay (u : 𝒱) :
    Tendsto (fun n : ℕ => (residual F : 𝒱 → 𝒱)^[n] u) atTop (𝓝 0) :=
  KFCausalEmbeddedResponseDecay.residual_decay J A F (defectOperator ε hε) L 2
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t)
    (formAction_output ε hε h hne hh mass2 quartic vacuum t)
    (graph_norm_identity ε hε h hb hne mass2 quartic vacuum t)
    (real_response_decay ε hε) (outputLp_residual_decay ε hε h hh) u

theorem form_residual_norm (u : 𝒱) : ‖residual F u‖ ≤ ‖u‖ :=
  KFCausalEmbeddedResponseDecay.residual_norm J A F (defectOperator ε hε) L 2 (by norm_num)
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t)
    (formAction_output ε hε h hne hh mass2 quartic vacuum t)
    (graph_norm_identity ε hε h hb hne mass2 quartic vacuum t)
    (responseOperator_norm ε hε) (outputLp_residual_norm ε hε h hh) u

#print axioms outputLp_residual_decay
#print axioms outputLp_residual_norm
#print axioms form_residual_embedding
#print axioms form_residual_output
#print axioms form_residual_embedding_iterate
#print axioms form_residual_output_iterate
#print axioms form_residual_decay
#print axioms form_residual_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay
