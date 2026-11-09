/- The actual clock-half output of every coherent-span state is in the
pure-clock momentum domain. The negative clock response is therefore
identified with the actual weak pairing, with its input norm bound. -/
import UnifiedTheory.Audit.KFCausalClockHalfMomentumDifferential
import UnifiedTheory.Audit.KFCausalCoherentMomentumFullOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentClockWeakResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (clockFunction neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile)
open UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain (profile_smooth)
open UnifiedTheory.Audit.KFCausalCoherentShearDomain (state_eq_toLp)
open UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit (pureOutput clockMomentumOutput clockMomentumOutput_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (clockOutput clockOutput_graph)
open UnifiedTheory.Audit.KFCausalOriginalPureClockOutput (preOutput preOutput_coe)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (differential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "B" => pureMomentum ε hε h
local notation "H" => clockHalf ε

theorem pureOutput_coe (k : Joint 2 4) : pureOutput ε a h hε ha hh k =ᵐ[volume]
    fun x => (-Complex.I*(h:ℂ))*differential ε
      (physicalProfile (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
        (sourceCoefficients h k) (clockFunction ε a)) x := by
  have he : pureOutput ε a h hε ha hh k = (-Complex.I*(h:ℂ)) •
      preOutput ε a hε ha (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
        (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (sourceCoefficients h k) := by
    unfold pureOutput
    rw [state_eq_toLp ε a h hε ha hh k,state_eq_toLp ε (a/2) h hε (by positivity) hh k]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (preOutput ε a hε ha (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (sourceCoefficients h k)),
    preOutput_coe ε a hε ha (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (sourceCoefficients h k)]
    with x hs hd
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hd]

theorem clockOutput_domain (k : Joint 2 4) : clockOutput ε a h hε ha hh k ∈ (B).domain := by
  apply KFCausalClockHalfMomentumDifferential.half_momentum_domain ε hε h hh
    (physicalProfile (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
      (sourceCoefficients h k) (clockFunction ε a))
    ((profile_smooth ε a _ _ _ _ _).differentiable (by norm_num))
    (state ε a h hε ha hh k) (pureOutput ε a h hε ha hh k) _ (clockMomentumOutput ε a h hε ha hh k)
    _ (pureOutput_coe ε a h hε ha hh k) (clockOutput_graph ε a h hε ha hh k)
    (clockMomentumOutput_graph ε a h hε ha hh k)
  rw [state_eq_toLp]
  exact MemLp.coeFn_toLp _

theorem actual_clockOutput_domain (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : Hilbert) (hg : (f,g) ∈ (H).graph) : g ∈ (B).domain := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hs : (∑ j, z j • state ε a h hε ha hh (q j),∑ j, z j • clockOutput ε a h hε ha hh (q j)) ∈ (H).graph := by
    have hs := (H).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      (H).graph.smul_mem (z j) (clockOutput_graph ε a h hε ha hh (q j)))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have eg : g = ∑ j, z j • clockOutput ε a h hε ha hh (q j) := (H).mem_graph_snd_inj' hg hs rfl
  rw [eg]
  exact (B).domain.sum_mem (fun j _ => (B).domain.smul_mem (z j) (clockOutput_domain ε a h hε ha hh (q j)))

theorem clock_weak_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g k : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (H).graph) (hk : (b,k) ∈ (H).graph) :
    (-2/h)*(inner ℂ g k).im = -KFCausalClockFloorPureClockKineticResponse.response ε hε g := by
  let hd := actual_clockOutput_domain ε a h hε ha hh f hf g hg
  exact KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f g b k
    ((B) ⟨g,hd⟩) hg hB hk ((B).mem_graph ⟨g,hd⟩)

theorem clock_weak_response_bounds (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b g k : Hilbert) (hB : (f,b) ∈ (B).graph) (hg : (f,g) ∈ (H).graph) (hk : (b,k) ∈ (H).graph) :
    -‖f‖^2 ≤ (-2/h)*(inner ℂ g k).im ∧ (-2/h)*(inner ℂ g k).im ≤ 0 := by
  rw [clock_weak_response ε a h hε ha hh f hf b g k hB hg hk]
  exact KFCausalClockFloorPureClockClockResponse.response_norm_bound ε hε f g hg

#print axioms pureOutput_coe
#print axioms clockOutput_domain
#print axioms actual_clockOutput_domain
#print axioms clock_weak_response
#print axioms clock_weak_response_bounds
end
end UnifiedTheory.Audit.KFCausalCoherentClockWeakResponse
