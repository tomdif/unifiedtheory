/- The projected clock response has a derived momentum composition.
The five clock/kinetic contributions are uniformly controlled by the
actual projected Hamiltonian energy. The remaining ordered response is
retained explicitly; no uniform bound on it is assumed. -/
import UnifiedTheory.Audit.KFCausalProjectedKineticResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedClockResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic (correction)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState clockFunction neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input momentumOutput inputOrbit momentumOrbit momentum_graph
    inputOrbit_continuous momentumOrbit_continuous)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
  (meanInput meanMomentum factorRate factorEnergy projectedEnergy projectedResponse reducedRate
    physical_energy full_reduced_response)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse
  (integral_closed_graph input_clock_graph momentum_clock_graph kinetic_bounds)

private theorem sourced_clock_graph (ε a α β h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    (KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b,
      KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb modelDirections pointField 0-
        correction ε hε h (KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b)) ∈
      (pureMomentum ε hε h).graph := by
  let u := KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b
  let v := KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw C p b h
  let g := KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b
  let k := KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb modelDirections pointField 0
  have hv : v =ᵐ[volume] fun x : Configuration => (-Complex.I*(h:ℂ))*
      KFCausalClockFloorPureClockDerivative.differential ε
        (KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a)) x := by
    filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
      (KFCausalOriginalPureClockOutput.preOutput ε a hε ha C p α β hα hβ hw b),
      KFCausalOriginalPureClockOutput.preOutput_coe ε a hε ha C p α β hα hβ hw b] with x hs hd
    change ((-Complex.I*(h:ℂ)) • KFCausalOriginalPureClockOutput.preOutput ε a hε ha C p α β hα hβ hw b) x = _
    rw [hs]
    simp only [Pi.smul_apply,hd,smul_eq_mul]
  have hg : (u,g) ∈ (clockHalf ε).graph :=
    KFCausalClockFloorSourcedClockMomentum.clockOutput_graph ε a α β hε ha hα hβ hw C p b
  have hk : (v,k) ∈ (clockHalf ε).graph :=
    KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb modelDirections pointField 0
  have hu := KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw C p b h hh
  have hd := KFCausalClockHalfMomentumDifferential.half_momentum_domain ε hε h hh
    (KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a))
    ((KFCausalCoherentLongitudinalDomain.profile_smooth ε a C p α β b).differentiable (by norm_num))
    u v g k (KFCausalClockFloorSourcedClockMomentum.state_coe ε a α β hε ha hα hβ hw C p b) hv hg hk
  let bg := (pureMomentum ε hε h) ⟨g,hd⟩
  have hbg : (g,bg) ∈ (pureMomentum ε hε h).graph := (pureMomentum ε hε h).mem_graph ⟨g,hd⟩
  have he : bg = k-correction ε hε h g := by
    have hc := KFCausalClockFloorPureClockClockResponse.commutator ε hε h hh u g v k bg hg hu hk hbg
    simpa only [sub_eq_add_neg,add_comm] using sub_eq_iff_eq_add.mp hc
  exact (congrArg (fun z : Hilbert => (g,z) ∈ (pureMomentum ε hε h).graph) he).mp hbg

private theorem displaced_clock_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    (KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections pointField 0,
      KFCausalDisplacedMomentumOrbit.factorOutput ε a h hε ha hh hb q k modelDirections pointField 0-
        correction ε hε h (KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  have hx := sourced_clock_graph ε a (groundWidth h) (neutralWidth h) h hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hh hb
    (KFCausalClockFloorDisplacedSources.amplitude h q k) (KFCausalClockFloorDisplacedSources.clockFrequency h k)
    (KFCausalClockFloorDisplacedSources.source h q k)
  have hs := ((pureMomentum ε hε h).graph.restrictScalars ℝ).smul_mem (‖trialState ε a h hε ha hh‖⁻¹) hx
  simpa only [KFCausalClockFloorDisplacedCommonDomain.factorOutput,KFCausalDisplacedMomentumOrbit.factorOutput,
    Prod.smul_mk,smul_sub,ContinuousLinearMap.map_smul_of_tower] using hs

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem clock_orbit_graph (θ : ℝ) :
    (inputOrbit ε h hε hh hb S 0 θ,
      momentumOrbit ε h hε hh hb S 0 θ-correction ε hε h (inputOrbit ε h hε hh hb S 0 θ)) ∈
      (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin S.size))) =>
      (pureMomentum ε hε h).graph.smul_mem (S.coefficient j)
        (displaced_clock_graph ε (S.packet j).width h hε (S.packet j).width_pos hh hb
          (parameter (2*Real.pi*θ) (S.packet j).centre) (parameter (2*Real.pi*θ) (S.packet j).frequency)))
  simpa only [inputOrbit,momentumOrbit,Prod.smul_mk,← prod_mk_sum,smul_sub,
    Finset.sum_sub_distrib,map_sum,map_smul] using hs

theorem projected_clock_graph :
    (meanInput ε h hε hh hb S 0,meanMomentum ε h hε hh hb S 0-
      correction ε hε h (meanInput ε h hε hh hb S 0)) ∈ (pureMomentum ε hε h).graph := by
  have hc := inputOrbit_continuous ε h hε hh hb S 0
  have hd := momentumOrbit_continuous ε h hε hh hb S 0
  have hi := (continuous_angle_memLp _ hc).integrable (by norm_num)
  have hj := (continuous_angle_memLp _ hd).integrable (by norm_num)
  have hs := integral_closed_graph (pureMomentum ε hε h) (pure_selfAdjoint ε hε h hh).isClosed _ _
    hc (hd.sub ((correction ε hε h).continuous.comp hc)) (clock_orbit_graph ε h hε hh hb S)
  have he : (∫ θ, momentumOrbit ε h hε hh hb S 0 θ-
      correction ε hε h (inputOrbit ε h hε hh hb S 0 θ) ∂angleMeasure) =
      meanMomentum ε h hε hh hb S 0-correction ε hε h (meanInput ε h hε hh hb S 0) := by
    rw [integral_sub hj ((correction ε hε h).integrable_comp hi),(correction ε hε h).integral_comp_comm hi]
    rfl
  exact (congrArg (fun z : Hilbert => (meanInput ε h hε hh hb S 0,z) ∈ (pureMomentum ε hε h).graph) he).mp hs

theorem clock_response : factorRate ε h hε hh hb S 0 =
    -KFCausalClockFloorPureClockKineticResponse.response ε hε (meanInput ε h hε hh hb S 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh
    (zeroProjection h hh (input ε h hε hh S)) (meanInput ε h hε hh hb S 0)
    (zeroProjection h hh (momentumOutput ε h hε hh S)) (meanMomentum ε h hε hh hb S 0)
    (meanMomentum ε h hε hh hb S 0-correction ε hε h (meanInput ε h hε hh hb S 0))
    (input_clock_graph ε h hε hh hb S)
    (KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _ (momentum_graph ε h hε hh S))
    (momentum_clock_graph ε h hε hh hb S) (projected_clock_graph ε h hε hh hb S)

theorem clock_energy_bounds :
    -(1/(4*ε))*factorEnergy ε h hε hh hb S 0 ≤ factorRate ε h hε hh hb S 0 ∧
      factorRate ε h hε hh hb S 0 ≤ 0 := by
  rw [clock_response ε h hε hh hb S]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε
    (zeroProjection h hh (input ε h hε hh S)) (meanInput ε h hε hh hb S 0)

theorem clock_norm_bounds :
    -‖zeroProjection h hh (input ε h hε hh S)‖^2 ≤ factorRate ε h hε hh hb S 0 ∧
      factorRate ε h hε hh hb S 0 ≤ 0 := by
  rw [clock_response ε h hε hh hb S]
  exact KFCausalClockFloorPureClockClockResponse.response_norm_bound ε hε _ _ (input_clock_graph ε h hε hh hb S)

variable (mass2 quartic vacuum t : ℝ)

def orderedResponse : ℝ := Real.exp (2*t)*(mass2/2*reducedRate ε h hε hh S 1+
  quartic/4*reducedRate ε h hε hh S 2+vacuum*reducedRate ε h hε hh S 0)

theorem static_remainder_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    |projectedResponse ε h hε hh hb S mass2 quartic vacuum t-orderedResponse ε h hε hh S mass2 quartic vacuum t| ≤
      (1/(4*ε))*projectedEnergy ε h hε hh hb S mass2 quartic vacuum t := by
  let E := factorEnergy ε h hε hh hb S
  let r := factorRate ε h hε hh hb S
  let c : ℝ := 1/(4*ε)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hE (i : Fin 8) : 0 ≤ E i := sq_nonneg _
  have h0 := clock_energy_bounds ε h hε hh hb S
  have h1 := kinetic_bounds ε h hε hh hb S 0
  have h2 := kinetic_bounds ε h hε hh hb S 1
  have h3 := kinetic_bounds ε h hε hh hb S 2
  have h4 := kinetic_bounds ε h hε hh hb S 3
  change -c*E 0 ≤ r 0 ∧ r 0 ≤ 0 at h0
  change 0 ≤ r 1 ∧ r 1 ≤ c*E 1 at h1
  change 0 ≤ r 2 ∧ r 2 ≤ c*E 2 at h2
  change 0 ≤ r 3 ∧ r 3 ≤ c*E 3 at h3
  change 0 ≤ r 4 ∧ r 4 ≤ c*E 4 at h4
  have ht := (Real.exp_pos (2*t)).le
  have hrest : 0 ≤ Real.exp (2*t)*(mass2/2*E 5+quartic/4*E 6+vacuum*E 7) :=
    mul_nonneg ht (add_nonneg (add_nonneg
      (mul_nonneg (by positivity) (hE 5)) (mul_nonneg (by positivity) (hE 6))) (mul_nonneg hv (hE 7)))
  have htotal : (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2) ≤
      projectedEnergy ε h hε hh hb S mass2 quartic vacuum t := by
    rw [physical_energy ε h hε hh hb S mass2 quartic vacuum t hm hq hv]
    change _ ≤ (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7)
    nlinarith
  have hd : projectedResponse ε h hε hh hb S mass2 quartic vacuum t-orderedResponse ε h hε hh S mass2 quartic vacuum t =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2) := by
    rw [full_reduced_response ε h hε hh hb S mass2 quartic vacuum t hm hq hv]
    unfold orderedResponse
    dsimp only [r]
    ring
  rw [hd]
  have htE := mul_le_mul_of_nonneg_left htotal hc
  have he1 := mul_nonneg hc (hE 1)
  have he2 := mul_nonneg hc (hE 2)
  have he3 := mul_nonneg ht (mul_nonneg hc (hE 3))
  have he4 := mul_nonneg ht (mul_nonneg hc (hE 4))
  have hr3 := mul_nonneg ht h3.1
  have hr4 := mul_nonneg ht h4.1
  have hu3 := mul_le_mul_of_nonneg_left h3.2 ht
  have hu4 := mul_le_mul_of_nonneg_left h4.2 ht
  change _ ≤ c*projectedEnergy ε h hε hh hb S mass2 quartic vacuum t
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hc (hE 0)]

#print axioms clock_orbit_graph
#print axioms projected_clock_graph
#print axioms clock_response
#print axioms clock_energy_bounds
#print axioms clock_norm_bounds
#print axioms static_remainder_bound
end
end UnifiedTheory.Audit.KFCausalProjectedClockResponse
