/- The actual vacuum factor of the projected structured Hamiltonian has
nonnegative pure-clock response. The unbounded momentum graph is passed
through the charge integral by closedness, with its correction retained. -/
import UnifiedTheory.Audit.KFCausalProjectedStructuredShearSign
import UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedStructuredVacuumSign
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (Packet StructuredState input momentumOutput inputOrbit momentumOrbit inputOrbit_continuous
    momentumOrbit_continuous momentum_graph momentumOrbit_graph)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput meanMomentum factorRate reducedRate)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt meanShearAt mean_input_one angle_continuous)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (factorOutput factorOutput_graph)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (core_compositions pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response pure_pairing_real)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem packet_regular (P : Packet) (θ : ℝ) :
    (state ε P.width h hε P.width_pos hh (parameter θ P.centre) (parameter θ P.frequency),
      factorOutput ε P.width h hε P.width_pos hh hb (parameter θ P.centre) (parameter θ P.frequency)
        modelDirections pointField 7) ∈ regularGraph ε hε h := by
  have hq := (KFCausalClockFloorDisplacedBoostOrbit.parameter_clock θ P.centre).trans P.clock_zero
  have hr := KFCausalDisplacedMatterWeakResponse.state_regular_graph ε P.width h hε P.width_pos hh hb
    (parameter θ P.centre) (parameter θ P.frequency) hq
  have ht := factorOutput_graph ε P.width h hε P.width_pos hh hb
    (parameter θ P.centre) (parameter θ P.frequency) hq modelDirections pointField 7
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hr.1.1 ht rfl
  dsimp only at he
  rw [← he]
  exact hr

variable (S : StructuredState)
local notation "G" => meanInput ε h hε hh hb S 7
local notation "M" => meanMomentum ε h hε hh hb S 7
local notation "J" => meanShearAt ε h hε hh hb S 1

theorem orbit_regular (θ : ℝ) :
    (action h hh (2*Real.pi*θ) (input ε h hε hh S),inputOrbit ε h hε hh hb S 7 θ) ∈
      regularGraph ε hε h := by
  simp only [input,map_sum,map_smul,action_state]
  have hs := (regularGraph ε hε h).sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin S.size))) =>
      (regularGraph ε hε h).smul_mem (S.coefficient i) (packet_regular ε h hε hh hb (S.packet i) (2*Real.pi*θ)))
  simpa only [inputOrbit,Prod.smul_mk,← prod_mk_sum] using hs

theorem orbit_pure_graph (θ : ℝ) :
    (inputOrbit ε h hε hh hb S 7 θ,momentumOrbit ε h hε hh hb S 7 θ+
      pureCorrection ε hε h hb (inputOrbit ε h hε hh hb S 7 θ)
        (KFCausalStructuredShearInterpolation.shear ε h hε hh hb S (2*Real.pi*θ) 1)) ∈
      (pureMomentum ε hε h).graph := by
  obtain ⟨b,tb,bg,jg,hb',htb,hbg,hjg,he⟩ := core_compositions ε hε h hb hh _ _ (orbit_regular ε h hε hh hb S θ)
  have hB := KFCausalClockFloorPureClockChargeGraph.graph_charge ε hε h hh (2*Real.pi*θ)
    _ _ (momentum_graph ε h hε hh S)
  have eb := (pureMomentum ε hε h).mem_graph_snd_inj' hb' hB rfl
  have et := (orderedExponential ε hε h).mem_graph_snd_inj' htb (momentumOrbit_graph ε h hε hh hb S θ 7) eb
  have hJ := KFCausalStructuredShearInterpolation.input_graph ε h hε hh hb S (2*Real.pi*θ)
    ⟨1,by constructor <;> norm_num⟩
  change (KFCausalStructuredShearInterpolation.input ε h hε hh hb S (2*Real.pi*θ) 1,
    KFCausalStructuredShearInterpolation.shear ε h hε hh hb S (2*Real.pi*θ) 1) ∈ _ at hJ
  rw [KFCausalStructuredShearInterpolation.input_one] at hJ
  have ej := (KFCausalTransverseShearMomentum.shearMomentum h).mem_graph_snd_inj' hjg hJ rfl
  dsimp only at et ej
  rw [et,ej] at he
  have eg : bg = momentumOrbit ε h hε hh hb S 7 θ+
      pureCorrection ε hε h hb (inputOrbit ε h hε hh hb S 7 θ)
        (KFCausalStructuredShearInterpolation.shear ε h hε hh hb S (2*Real.pi*θ) 1) := by
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  rw [← eg]
  exact hbg

theorem mean_pure_graph : (G,M+pureCorrection ε hε h hb G J) ∈ (pureMomentum ε hε h).graph := by
  let gi := inputOrbit ε h hε hh hb S 7
  let mi := momentumOrbit ε h hε hh hb S 7
  let ji : ℝ → Hilbert := fun θ => KFCausalStructuredShearInterpolation.shear ε h hε hh hb S (2*Real.pi*θ) 1
  have hg : Continuous gi := inputOrbit_continuous ε h hε hh hb S 7
  have hm : Continuous mi := momentumOrbit_continuous ε h hε hh hb S 7
  have hj : Continuous ji := (angle_continuous ε h hε hh hb S ⟨1,by constructor <;> norm_num⟩).2.comp
    (continuous_const.mul continuous_id)
  have hi (f : ℝ → Hilbert) (hf : Continuous f) : Integrable f angleMeasure :=
    (continuous_angle_memLp f hf).integrable (by norm_num)
  have hc : Continuous (fun θ => (correction ε hε h hb) (gi θ)) := (correction ε hε h hb).continuous.comp hg
  have hs : Continuous (fun θ => (shearCorrection ε hε h hb) (ji θ)) := (shearCorrection ε hε h hb).continuous.comp hj
  have he := KFCausalProjectedKineticResponse.integral_closed_graph (pureMomentum ε hε h)
    (pure_selfAdjoint ε hε h hh).isClosed gi
    (fun θ => mi θ+((correction ε hε h hb) (gi θ)-(shearCorrection ε hε h hb) (ji θ)))
    hg (hm.add (hc.sub hs)) (orbit_pure_graph ε h hε hh hb S)
  change (∫ θ, gi θ ∂angleMeasure,
    ∫ θ, mi θ+((correction ε hε h hb) (gi θ)-(shearCorrection ε hε h hb) (ji θ)) ∂angleMeasure) ∈ _ at he
  rw [integral_add (hi mi hm) (hi _ (hc.sub hs)),integral_sub (hi _ hc) (hi _ hs),
    (correction ε hε h hb).integral_comp_comm (hi gi hg),
    (shearCorrection ε hε h hb).integral_comp_comm (hi ji hj)] at he
  exact he

theorem vacuum_response : factorRate ε h hε hh hb S 7 = response ε hε h hb G J := by
  have he := pure_pairing_real ε hε h hh G _ (mean_pure_graph ε h hε hh hb S)
  rw [inner_add_right,Complex.add_im] at he
  change (-2/h)*(inner ℂ G M).im = (2/h)*(inner ℂ G (pureCorrection ε hε h hb G J)).im
  rw [show (inner ℂ G M).im = -(inner ℂ G (pureCorrection ε hε h hb G J)).im by linarith]
  ring

theorem vacuum_nonnegative : 0 ≤ factorRate ε h hε hh hb S 7 := by
  have hj := KFCausalStructuredShearMean.mean_graph ε h hε hh hb S ⟨1,by constructor <;> norm_num⟩
  change (meanInputAt ε h hε hh hb S 1,J) ∈ _ at hj
  rw [mean_input_one] at hj
  have hs := KFCausalProjectedStructuredShearSign.projected_root_nonnegative ε h hε hh hb S
  rw [mean_input_one] at hs
  rw [vacuum_response,KFCausalClockFloorSignedShearResponse.response_weighted_shear ε hε h hb hh G J hj]
  exact add_nonneg (KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hb G).1
    (mul_nonneg (by positivity) hs)

include hb in
theorem reduced_vacuum_nonnegative : 0 ≤ reducedRate ε h hε hh S 0 := by
  rw [KFCausalStructuredProjectedHamiltonian.reduced_rate_eq ε h hε hh hb S 0]
  exact vacuum_nonnegative ε h hε hh hb S

#print axioms packet_regular
#print axioms orbit_regular
#print axioms orbit_pure_graph
#print axioms mean_pure_graph
#print axioms vacuum_response
#print axioms vacuum_nonnegative
#print axioms reduced_vacuum_nonnegative
end
end UnifiedTheory.Audit.KFCausalProjectedStructuredVacuumSign
