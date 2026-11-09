/- Bounds for actual charge-averaged factor responses on the coherent span.
The clock term can be negative, the four kinetic terms are nonnegative,
and the vacuum term is nonnegative after averaging. The two ordered
matter terms are kept separate and have no sign asserted here. -/
import UnifiedTheory.Audit.KFCausalCoherentClockWeakResponse
import UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph (graph_charge)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate rate_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)

def kineticIndex (i : Fin 4) : Fin 8 := ⟨i.val+1,by omega⟩

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (f b : Hilbert) (g k : Fin 8 → ℝ → Hilbert)
  (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
  (hOut : ∀ θ i,
    (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
    (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)

include hB hOut in
theorem clock_pointwise_bounds (a : ℝ) (ha : 0 < a) (hf : f ∈ coherentSpan ε a h hε ha hh) (θ : ℝ) :
    -‖f‖^2 ≤ (-2/h)*(inner ℂ (g 0 θ) (k 0 θ)).im ∧
      (-2/h)*(inner ℂ (g 0 θ) (k 0 θ)).im ≤ 0 := by
  have hr := KFCausalCoherentClockWeakResponse.clock_weak_response_bounds ε a h hε ha hh
    (action h hh (2*Real.pi*θ) f) (action_coherentSpan ε a h hε ha hh _ f hf)
    (action h hh (2*Real.pi*θ) b) (g 0 θ) (k 0 θ)
    (graph_charge ε hε h hh _ f b hB) (hOut θ 0).1 (hOut θ 0).2
  simpa only [(action h hh (2*Real.pi*θ)).norm_map f] using hr

include hB hOut in
theorem clock_bounds (a : ℝ) (ha : 0 < a) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (hg : Continuous (g 0)) (hk : Continuous (k 0)) :
    -‖f‖^2 ≤ rate h g k 0 ∧ rate h g k 0 ≤ 0 := by
  have hp := clock_pointwise_bounds ε h hε hh f b g k hB hOut a ha hf
  refine ⟨?_,integral_nonpos (fun θ => (hp θ).2)⟩
  have hi := integral_mono (integrable_const (-‖f‖^2)) (rate_integrable h (g 0) (k 0) hg hk)
    (fun θ => (hp θ).1)
  simpa only [integral_const,probReal_univ,one_smul] using hi

include hB hOut in
theorem kinetic_pointwise (i : Fin 4) (θ : ℝ) :
    (-2/h)*(inner ℂ (g (kineticIndex i) θ) (k (kineticIndex i) θ)).im =
      KFCausalClockFloorPureClockKineticResponse.response ε hε (g (kineticIndex i) θ) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    (action h hh (2*Real.pi*θ) f) _ (action h hh (2*Real.pi*θ) b) _
  · have hg := (hOut θ (kineticIndex i)).1
    fin_cases i <;> exact hg
  · exact graph_charge ε hε h hh _ f b hB
  · have hk := (hOut θ (kineticIndex i)).2
    fin_cases i <;> exact hk

include hB hOut in
theorem kinetic_bounds (i : Fin 4) (hg : Continuous (g (kineticIndex i)))
    (hk : Continuous (k (kineticIndex i))) :
    0 ≤ rate h g k (kineticIndex i) ∧ rate h g k (kineticIndex i) ≤
      (1/(4*ε))*(∫ θ, ‖g (kineticIndex i) θ‖^2 ∂angleMeasure) := by
  have hp (θ : ℝ) := KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (g (kineticIndex i) θ)
  have he := kinetic_pointwise ε h hε hh f b g k hB hOut i
  refine ⟨integral_nonneg (fun θ => (he θ).symm ▸ (hp θ).1),?_⟩
  have hi := integral_mono (rate_integrable h _ _ hg hk)
    (((continuous_angle_memLp _ (hg.norm.pow 2)).integrable (by norm_num)).const_mul (1/(4*ε)))
    (fun θ => (he θ).symm ▸ (hp θ).2)
  exact hi.trans_eq (integral_const_mul _ _)

include hB hOut hb in
theorem vacuum_nonneg (a : ℝ) (ha : 0 < a) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    0 ≤ rate h g k 7 := by
  obtain ⟨b',g',j',k',bg',hB',hOut',_,_,_,hp⟩ :=
    KFCausalCoherentVacuumCompositionL2.exists_actual_L2_response ε a h hε ha hh hb f hf
  have eb : b' = b := (pureMomentum ε hε h).mem_graph_snd_inj' hB' hB rfl
  have eg (θ : ℝ) : g 7 θ = g' θ :=
    (orderedExponential ε hε h).mem_graph_snd_inj' (hOut θ 7).1 (hOut' θ).1 rfl
  have ek (θ : ℝ) : k 7 θ = k' θ :=
    (orderedExponential ε hε h).mem_graph_snd_inj' (hOut θ 7).2 (hOut' θ).2.2.1
      (congrArg (action h hh (2*Real.pi*θ)) eb.symm)
  simpa only [rate,KFCausalCoherentVacuumWeakForce.weakResponse,eg,ek] using hp

#print axioms clock_pointwise_bounds
#print axioms clock_bounds
#print axioms kinetic_pointwise
#print axioms kinetic_bounds
#print axioms vacuum_nonneg
end
end UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds
