/- A concrete even neutral excitation lies outside the Hilbert closure
of all finite reciprocal Gaussian sums. It and its actual clock momentum
have completed Hamiltonian form lifts. Thus the response-pair closure
cannot exhaust the regular zero-charge response domain. This does not
assert that a trajectory leaves the reciprocal closure. -/
import UnifiedTheory.Audit.KFCausalNeutralGaussianConstraint
import UnifiedTheory.Audit.KFCausalReciprocalResponseClosure
import UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalClosureObstruction
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalNeutralTranslationCoordinates (action action_coe vector)
open KFCausalNeutralGaussianConstraint
open KFCausalClockFloorInvariantTrial
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalChargeGaussianIdentities (configurationProfile)
open KFCausalNeutralExponentialProfiles (neutralSource exponentialProfile)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalGaussianVacuumSquare (original_strip)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def witness : Hilbert :=
  KFCausalPolynomialGaussianDomain.input ε a h hε ha hh 1 0 (neutralSource 0) 4 (Polynomial.X^2)
def profile (x : Configuration) : ℂ :=
  (x.2 4:ℂ)^2*configurationProfile (groundWidth h) (neutralWidth h) (clockFunction ε a) x

theorem witness_coe : witness ε a h hε ha hh =ᵐ[volume] profile ε a h := by
  filter_upwards [KFCausalNeutralFiniteCharge.packet_relation ε a h hε ha hh 0 1 (Polynomial.X^2),
    trialState_coe ε a h hε ha hh] with x hx ht
  change witness ε a h hε ha hh x = _ at hx
  rw [hx,ht]
  simp [profile,exponentialProfile]

theorem profile_continuous : Continuous (profile ε a h) := by
  unfold profile
  have hq : Continuous (fun x : Configuration => (x.2 4:ℂ)^2) := by fun_prop
  exact hq.mul
    (KFCausalChargeGaussianIdentities.configurationProfile_continuous _ _ _
      (clockFunction_continuous ε a))

theorem witness_zeroSector : witness ε a h hε ha hh ∈ zeroSector h hh :=
  KFCausalNeutralFiniteCharge.packet_mem_zeroSector ε a h hε ha hh 0 1 (Polynomial.X^2)

theorem witness_not_constrained : witness ε a h hε ha hh ∉ constrained (neutralWidth h) := by
  intro hf
  have hr := (mem_constrained _ _).mp hf
  have he : (fun x : Configuration => profile ε a h (x+vector 1)) =ᵐ[volume]
      fun x => ratio (neutralWidth h) (x.2 4)*profile ε a h x := by
    filter_upwards [hr,action_coe 1 (witness ε a h hε ha hh),witness_coe ε a h hε ha hh,
      (KFCausalLpPhaseTranslation.shift_preserves volume (vector 1)).quasiMeasurePreserving.ae
        (witness_coe ε a h hε ha hh)] with x hr ht hf hs
    change witness ε a h hε ha hh (x+vector 1) = profile ε a h (x+vector 1) at hs
    rw [ht,hs,hf] at hr
    exact hr
  have heq := Measure.eq_of_ae_eq he
    ((profile_continuous ε a h).comp (continuous_id.add continuous_const))
    (((ratio_continuous _).comp (by fun_prop)).mul (profile_continuous ε a h))
  have hz := congrFun heq (0 : Configuration)
  have hn := mul_ne_zero (clockFunction_ne_zero ε a hε.le 0)
    (Complex.exp_ne_zero (-((neutralWidth h:ℝ):ℂ)))
  apply hn
  simpa [profile,configurationProfile,KFCausalClockFloorShearBounds.physicalGaussian,
    vector,Fin.sum_univ_succ] using hz

theorem witness_not_reciprocalClosure :
    witness ε a h hε ha hh ∉ closure (reciprocalStates ε h hε hh) :=
  fun hf => witness_not_constrained ε a h hε ha hh (reciprocalClosure_constrained ε h hε hh hf)

include a ha in
theorem zeroSector_not_subset_reciprocalClosure :
    ¬ (zeroSector h hh : Set Hilbert) ⊆ closure (reciprocalStates ε h hε hh) :=
  fun hs => witness_not_reciprocalClosure ε a h hε ha hh (hs (witness_zeroSector ε a h hε ha hh))

theorem completedPairs_input_constrained (hb : |h| ≤ Real.pi*ε/3) (t : ℝ)
    (z : FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t ×
      FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t)
    (hz : z ∈ KFCausalReciprocalResponseClosure.completedPairs ε h hε hh hb t) :
    embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t z.1 ∈ constrained (neutralWidth h) := by
  let J := embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t
  have hc : IsClosed {w :
      FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t ×
        FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t |
      J w.1 ∈ constrained (neutralWidth h)} :=
    (constrained_closed _).preimage (J.continuous.comp continuous_fst)
  apply closure_minimal (s := KFCausalReciprocalResponseClosure.packetPairs ε h hε hh hb t)
    (t := {w | J w.1 ∈ constrained (neutralWidth h)}) _ hc hz
  rintro w ⟨n,a,w,c,ha,hw,rfl⟩
  exact reciprocal_sum_constrained n ε h a w c hε ha hh hw

theorem witness_regular_pair (hb : |h| ≤ Real.pi*ε/3) (t : ℝ) :
    ∃ u v : FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t,
      embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t u = witness ε a h hε ha hh ∧
      (embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t u,
        embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t v) ∈ (pureMomentum ε hε h).graph ∧
      embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t v ∈ zeroSector h hh ∧
      (u,v) ∉ KFCausalReciprocalResponseClosure.completedPairs ε h hε hh hb t := by
  let u := KFCausalNeutralMixedClockHamiltonian.inputLift ε h hε hh (original_strip ε h hε hb)
    1 (fun _ => a) (fun _ => 0) (fun _ => ha) (fun _ => 0) (fun _ => 1)
      (fun _ => Polynomial.X^2) 1 1 1 t
  let v := KFCausalNeutralMixedClockHamiltonian.momentumLift ε h hε hh (original_strip ε h hε hb)
    1 (fun _ => a) (fun _ => 0) (fun _ => ha) (fun _ => 0) (fun _ => 1)
      (fun _ => Polynomial.X^2) 1 1 1 t
  have hu : embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t u = witness ε a h hε ha hh := by
    change KFCausalNeutralMixedClockState.state ε h hε hh 1 (fun _ => a) (fun _ => 0)
      (fun _ => ha) (fun _ => 0) (fun _ => 1) (fun _ => Polynomial.X^2) = _
    simp [KFCausalNeutralMixedClockState.state,witness]
  refine ⟨u,v,hu,?_,?_,?_⟩
  · exact KFCausalNeutralMixedClockHamiltonian.lifted_momentum_graph ε h hε hh
      (original_strip ε h hε hb) 1 (fun _ => a) (fun _ => 0) (fun _ => ha)
      (fun _ => 0) (fun _ => 1) (fun _ => Polynomial.X^2) 1 1 1 t
  · exact KFCausalNeutralMixedClockCharge.momentum_mem_zeroSector ε h hε hh 1
      (fun _ => a) (fun _ => 0) (fun _ => ha) (fun _ => 0) (fun _ => 1) (fun _ => Polynomial.X^2)
  · intro hz
    have hc := completedPairs_input_constrained ε h hε hh hb t (u,v) hz
    rw [hu] at hc
    exact witness_not_constrained ε a h hε ha hh hc

#print axioms witness_coe
#print axioms profile_continuous
#print axioms witness_zeroSector
#print axioms witness_not_constrained
#print axioms witness_not_reciprocalClosure
#print axioms zeroSector_not_subset_reciprocalClosure
#print axioms completedPairs_input_constrained
#print axioms witness_regular_pair
end
end UnifiedTheory.Audit.KFCausalReciprocalClosureObstruction
