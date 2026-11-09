/- The norm secant applies to the actual transported field paths and
therefore to their original physical endpoints. The resulting initial
cost is a state-defined norm, with no initial shear derivative. -/
import UnifiedTheory.Audit.KFCausalShearNormSecant
import UnifiedTheory.Audit.KFCausalTransportedChargeInitial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalTransportedNormSecant
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root rootValue root_coe)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator operator_norm_sq)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)
open UnifiedTheory.Audit.KFCausalTransportedMatterInterpolation (input output)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter (initialInput initial_representations)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "M" => operator ε h hε hb hh
local notation "W" => root ε hε h hb hh

theorem finite_secant {n : ℕ} (s : Fin n → Seed) (z : Fin n → ℂ) :
    (‖M (KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z 1)‖^2-
      ‖M (input ε h hε hb hh l i s z 0)‖^2)/2 ≤
      expectation W (KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z)
        (KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i s z) 1 := by
  have he := KFCausalShearNormSecant.endpoint_secant ε h hε hb hh
    (input ε h hε hb hh l i s z) (output ε h hε hb hh l i s z)
    (KFCausalTransportedMatterInterpolation.curves_continuous ε h hε hb hh l i s z).1
    (fun t ht => by
      rw [← KFCausalActualTransportedField.profile_operator ε h hε hb hh]
      exact KFCausalTransportedMatterInterpolation.input_derivative ε h hε hb hh l i s z t ht)
    (KFCausalTransportedMatterInterpolation.input_graph ε h hε hb hh l i s z)
    (KFCausalTransportedMatterInterpolation.expectation_monotone ε h hε hb hh l i s z W
      (fun r => (rootValue ε h r:ℂ)) (root_coe ε hε h hb hh))
  obtain ⟨hu,hj⟩ := KFCausalTransportedMatterInterpolation.endpoints ε h hε hb hh l i s z
  simpa only [expectation,hu,hj] using he

variable (a : ℝ) (ha : 0 < a)
local notation "S" => coherentSpan ε a h hε ha hh

theorem actual_endpoint_secant (f : S) (g u j : Hilbert)
    (hg : ((f:Hilbert),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    (‖M u‖^2-‖M (initialInput ε a h hε ha hh hb l i f)‖^2)/2 ≤
      (inner ℂ (W u) (W j)).re := by
  obtain ⟨n,k,z,hf⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f f.property
  have hg' : (∑ r, z r • state ε a h hε ha hh (k r),g) ∈ (orderedExponential ε hε h).graph := hf ▸ hg
  obtain ⟨eu,ej⟩ := KFCausalCoherentMatterInterpolation.endpoints_actual ε a h hε ha hh hb l i k z g u j hg' hu hj
  have he := finite_secant ε h hε hb hh l i
    (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r))
  rw [(initial_representations ε a h hε ha hh hb l i f k z hf).1]
  change (‖M (KFCausalCoherentMatterInterpolation.field ε a h hε ha hh hb l i k z 1)‖^2-_)/2 ≤
    (inner ℂ (W (KFCausalCoherentMatterInterpolation.field ε a h hε ha hh hb l i k z 1))
      (W (KFCausalCoherentMatterInterpolation.shear ε a h hε ha hh hb l i k z 1))).re at he
  simpa only [eu,ej] using he

theorem actual_endpoint_norm_lower (f : S) (g u j : Hilbert)
    (hg : ((f:Hilbert),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    -(ε/8)*‖initialInput ε a h hε ha hh hb l i f‖^2 ≤ (inner ℂ (W u) (W j)).re := by
  have he := actual_endpoint_secant ε h hε hb hh l i a ha f g u j hg hu hj
  have hn := operator_norm_sq ε h hε hb hh (initialInput ε a h hε ha hh hb l i f)
  nlinarith [sq_nonneg ‖M u‖]

#print axioms finite_secant
#print axioms actual_endpoint_secant
#print axioms actual_endpoint_norm_lower
end
end UnifiedTheory.Audit.KFCausalTransportedNormSecant
