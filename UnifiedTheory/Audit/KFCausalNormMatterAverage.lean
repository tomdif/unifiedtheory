/- Charge integration of the actual transported norm secant. Both
initial costs depend on the state, with all interference retained.
The norm cost is not assumed to be controlled by Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalTransportedNormSecant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalNormMatterAverage
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator (rotate)
open UnifiedTheory.Audit.KFCausalTransportedChargeInitial (input curves_continuous)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root rootValue root_coe)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "S" => coherentSpan ε a h hε ha hh
local notation "M" => operator ε h hε hb hh
local notation "W" => root ε hε h hb hh

def cost (f : S) : ℝ := ∫ θ, ‖input ε a h hε ha hh hb l i f θ‖^2 ∂angleMeasure
def weightedCost (f : S) : ℝ := ∫ θ, ‖M (input ε a h hε ha hh hb l i f θ)‖^2 ∂angleMeasure

theorem initialNorm_integrable (f : S) :
    Integrable (fun θ => ‖input ε a h hε ha hh hb l i f θ‖^2) angleMeasure :=
  (continuous_angle_memLp _ ((curves_continuous ε a h hε ha hh hb l i f).1.norm.pow 2)).integrable (by norm_num)

theorem initialWeightedNorm_integrable (f : S) :
    Integrable (fun θ => ‖M (input ε a h hε ha hh hb l i f θ)‖^2) angleMeasure :=
  (continuous_angle_memLp _ (((M).continuous.comp
    (curves_continuous ε a h hε ha hh hb l i f).1).norm.pow 2)).integrable (by norm_num)

theorem actual_average_secant (f : S) (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (f:Hilbert),g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    Integrable (fun θ => ‖M (u θ)‖^2) angleMeasure ∧
      ((∫ θ, ‖M (u θ)‖^2 ∂angleMeasure)-weightedCost ε a h hε ha hh hb l i f)/2 ≤
        ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
  have he := KFCausalTransportedChargeInitial.actual_average_lower ε a h hε ha hh hb l i
    W (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hb hh) f g u j hg hu hj
  have hN := (continuous_angle_memLp _ (((M).continuous.comp he.1).norm.pow 2)).integrable (by norm_num)
  have h0 := initialWeightedNorm_integrable ε a h hε ha hh hb l i f
  refine ⟨hN,?_⟩
  have hp (θ : ℝ) : (‖M (u θ)‖^2-‖M (input ε a h hε ha hh hb l i f θ)‖^2)/2 ≤
      (inner ℂ (W (u θ)) (W (j θ))).re :=
    KFCausalTransportedNormSecant.actual_endpoint_secant ε h hε hb hh l i a ha
      (rotate ε a h hε ha hh (2*Real.pi*θ) f) (g θ) (u θ) (j θ) (hg θ) (hu θ) (hj θ)
  have hi := integral_mono ((hN.sub h0).div_const 2) he.2.2.1 hp
  simp only [Pi.sub_apply] at hi
  rw [integral_div,integral_sub hN h0] at hi
  exact hi

theorem actual_average_norm_lower (f : S) (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (f:Hilbert),g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    -(ε/8)*cost ε a h hε ha hh hb l i f ≤
      ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
  have he := KFCausalTransportedChargeInitial.actual_average_lower ε a h hε ha hh hb l i
    W (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hb hh) f g u j hg hu hj
  have hp (θ : ℝ) : -(ε/8)*‖input ε a h hε ha hh hb l i f θ‖^2 ≤
      (inner ℂ (W (u θ)) (W (j θ))).re :=
    KFCausalTransportedNormSecant.actual_endpoint_norm_lower ε h hε hb hh l i a ha
      (rotate ε a h hε ha hh (2*Real.pi*θ) f) (g θ) (u θ) (j θ) (hg θ) (hu θ) (hj θ)
  have hi := integral_mono ((initialNorm_integrable ε a h hε ha hh hb l i f).const_mul (-(ε/8))) he.2.2.1 hp
  rw [integral_const_mul] at hi
  exact hi

#print axioms initialNorm_integrable
#print axioms initialWeightedNorm_integrable
#print axioms actual_average_secant
#print axioms actual_average_norm_lower
end
end UnifiedTheory.Audit.KFCausalNormMatterAverage
