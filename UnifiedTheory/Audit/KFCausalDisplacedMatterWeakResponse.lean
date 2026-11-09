/- The normalized displaced family has the actual sourced-Gaussian
matter response. Clock displacement must vanish; the existing charge
action preserves that condition. No energy lower bound is assumed. -/
import UnifiedTheory.Audit.KFCausalSourcedMatterWeakResponse
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalDisplacedMatterWeakResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state state_normalization)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (rawState_eq_sourced)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound trialState)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response)
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)

theorem sourced_amplitude_smul (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (C z : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw (z*C) p b =
      z • KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b := by
  apply Lp.ext
  filter_upwards [KFCausalClockFloorSourcedClockMomentum.state_coe ε a α β hε ha hα hβ hw (z*C) p b,
    KFCausalClockFloorSourcedClockMomentum.state_coe ε a α β hε ha hα hβ hw C p b,
    Lp.coeFn_smul z (KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b)]
    with x hz hC hs
  rw [hz,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hC,physicalProfile,clockMultiplier]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (hq : q (.inr 0) = 0)
local notation "N" => (‖trialState ε a h hε ha hh‖⁻¹ : ℝ)
local notation "C" => (N:ℂ)*amplitude h q k
local notation "S" => state ε a h hε ha hh q k
local notation "G" => KFCausalClockFloorSourcedSpectral.shiftedOutput ε a (groundWidth h) (neutralWidth h)
  hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
  C (clockFrequency h k) (source h q k) h hb
local notation "JG" => KFCausalSourcedMomentumOutput.shearOutput ε a (groundWidth h) (neutralWidth h)
  hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
  C (clockFrequency h k) (source h q k) h hb

include hq in
theorem normalized_eq_sourced :
    S = KFCausalClockFloorSourcedClockMomentum.state ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      C (clockFrequency h k) (source h q k) := by
  rw [state_normalization,rawState_eq_sourced ε a h hε ha hh q k hq,sourced_amplitude_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

include hq in
theorem state_regular_graph : (S,G) ∈ regularGraph ε hε h := by
  rw [normalized_eq_sourced ε a h hε ha hh q k hq]
  exact KFCausalSourcedPureClockCommutator.state_regular_graph ε a (groundWidth h) (neutralWidth h)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    C (clockFrequency h k) (source h q k) h hh hb

include hq in
theorem actual_matter_response (l : Transverse →L[ℝ] ℝ) (i : Fin 2) :
    ∃ bf u v j : Hilbert,
      (S,G) ∈ (orderedExponential ε hε h).graph ∧ (G,JG) ∈ (shearMomentum h).graph ∧
      (S,bf) ∈ (pureMomentum ε hε h).graph ∧ (S,u) ∈ (matterFactor ε hε h (fieldPower l i)).graph ∧
      (bf,v) ∈ (matterFactor ε hε h (fieldPower l i)).graph ∧ (JG,j) ∈ (fieldPower l i).graph ∧
      (-2/h)*(inner ℂ u v).im = response ε hε h hb u j := by
  rw [normalized_eq_sourced ε a h hε ha hh q k hq]
  obtain ⟨bf,u,v,j,hbf,hu,hv,hj,he⟩ := KFCausalSourcedMatterWeakResponse.actual_matter_response
    ε a (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) C (clockFrequency h k) (source h q k) h hh hb l i
  exact ⟨bf,u,v,j,KFCausalClockFloorSourcedSpectral.state_ordered_graph
    ε a (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) C (clockFrequency h k) (source h q k) h hb,
    KFCausalSourcedMomentumOutput.shear_graph ε a (groundWidth h) (neutralWidth h) hε ha
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      C (clockFrequency h k) (source h q k) h hh hb,hbf,hu,hv,hj,he⟩

#print axioms sourced_amplitude_smul
#print axioms normalized_eq_sourced
#print axioms state_regular_graph
#print axioms actual_matter_response
end
end UnifiedTheory.Audit.KFCausalDisplacedMatterWeakResponse
