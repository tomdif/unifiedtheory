/- Both reciprocal Gaussian and actual clock momentum have the natural
second vacuum action for w>=1 and abs(h)<=pi*epsilon/3. -/
import UnifiedTheory.Audit.KFCausalGaussianMomentumVacuumSquare
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianVacuumSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport transport_reverse)
open KFCausalReciprocalSqueezeExponential (exponential_graph_squeeze)
open KFCausalReciprocalSqueezeClockCommutation (inverse_half_commutes)
open KFCausalClockFloorVacuumSquare
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalGaussianMomentum (momentum state_eq_transport)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalGaussianVacuumSquare (original_strip)

theorem square_graph_transport (ε : ℝ) (hε : 0 < ε) (h t : ℝ)
    (f z : Hilbert) (hfz : (f,z) ∈ (square ε hε h).graph) :
    (transport t f,transport t z) ∈ (square ε hε h).graph := by
  obtain ⟨u,hu,hz⟩ := (square_graph ε hε h f z).mp hfz
  apply (square_graph ε hε h _ _).mpr
  refine ⟨transport t u,?_,?_⟩
  · rw [← inverse_half_commutes]
    exact exponential_graph_squeeze ε hε h 1 t _ _ hu
  · rw [hz,inverse_half_commutes]

theorem square_domain_transport (ε : ℝ) (hε : 0 < ε) (h t : ℝ) (f : Hilbert) :
    transport t f ∈ (square ε hε h).domain ↔ f ∈ (square ε hε h).domain := by
  constructor
  · intro hf
    obtain ⟨z,hz⟩ := LinearPMap.mem_domain_iff.mp hf
    have hg := square_graph_transport ε hε h (-t) _ _ hz
    rw [transport_reverse] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      (square_graph_transport ε hε h t _ _ ((square ε hε h).mem_graph ⟨f,hf⟩))

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "ψ" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "c" => (Real.exp (-t/2):ℂ)

def stateOutput : Hilbert := c • transport (-t)
  (KFCausalGaussianVacuumSquare.squareOutput ε a α β hε ha hα hβ hbw 1 0 0 h hb)

def momentumOutput : Hilbert := c • transport (-t)
  (KFCausalGaussianMomentumVacuumSquare.squareOutput ε a α β hε ha hα hβ hbw 1 0 0 h hb)

theorem state_graph : (ψ,stateOutput ε a h w hε ha hh hw hb) ∈ (square ε hε h).graph := by
  rw [state_eq_transport ε a h w hε ha hh hw]
  exact (square ε hε h).graph.smul_mem c
    (square_graph_transport ε hε h (-t) _ _
      (KFCausalGaussianVacuumSquare.squareOutput_graph ε a α β hε ha hα hβ hbw 1 0 0 h hb))

theorem momentum_graph :
    (momentum ε a h w hε ha hh hw,momentumOutput ε a h w hε ha hh hw hb) ∈
      (square ε hε h).graph :=
  (square ε hε h).graph.smul_mem c
    (square_graph_transport ε hε h (-t) _ _
      (KFCausalGaussianMomentumVacuumSquare.squareOutput_graph
        ε a α β hε ha hα hβ hbw 1 0 0 h hh hb))

include hb in
theorem state_domain : ψ ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_graph ε a h w hε ha hh hw hb)

include hb in
theorem momentum_domain : momentum ε a h w hε ha hh hw ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (momentum_graph ε a h w hε ha hh hw hb)

theorem state_adjoint_graph :
    (ψ,stateOutput ε a h w hε ha hh hw hb) ∈
      (KFCausalOrderedOperatorComposition.composition
        (orderedExponential ε hε h).adjoint (orderedExponential ε hε h)).graph :=
  square_adjoint_graph ε hε h (by have hp := mul_pos Real.pi_pos hε; linarith) _ _
    (state_graph ε a h w hε ha hh hw hb)

theorem momentum_adjoint_graph :
    (momentum ε a h w hε ha hh hw,momentumOutput ε a h w hε ha hh hw hb) ∈
      (KFCausalOrderedOperatorComposition.composition
        (orderedExponential ε hε h).adjoint (orderedExponential ε hε h)).graph :=
  square_adjoint_graph ε hε h (by have hp := mul_pos Real.pi_pos hε; linarith) _ _
    (momentum_graph ε a h w hε ha hh hw hb)

theorem state_pairing (v : Hilbert) (hv : v ∈ (orderedExponential ε hε h).domain) :
    inner ℂ (KFCausalReciprocalGaussianMomentum.output ε a h w hε ha hh hw
      (original_strip ε h hε hb) 7) (orderedExponential ε hε h ⟨v,hv⟩) =
      inner ℂ (stateOutput ε a h w hε ha hh hw hb) v :=
  square_pairing ε hε h _ _ _ v
    (KFCausalReciprocalGaussianMomentum.output_graph ε a h w hε ha hh hw
      (original_strip ε h hε hb) 7) (state_graph ε a h w hε ha hh hw hb) hv

theorem momentum_pairing (v : Hilbert) (hv : v ∈ (orderedExponential ε hε h).domain) :
    inner ℂ (KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw
      (original_strip ε h hε hb) 7) (orderedExponential ε hε h ⟨v,hv⟩) =
      inner ℂ (momentumOutput ε a h w hε ha hh hw hb) v :=
  square_pairing ε hε h _ _ _ v
    (KFCausalReciprocalGaussianMomentum.momentumOutput_graph ε a h w hε ha hh hw
      (original_strip ε h hε hb) 7) (momentum_graph ε a h w hε ha hh hw hb) hv

#print axioms square_graph_transport
#print axioms square_domain_transport
#print axioms state_graph
#print axioms momentum_graph
#print axioms state_domain
#print axioms momentum_domain
#print axioms state_adjoint_graph
#print axioms momentum_adjoint_graph
#print axioms state_pairing
#print axioms momentum_pairing
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianVacuumSquare
