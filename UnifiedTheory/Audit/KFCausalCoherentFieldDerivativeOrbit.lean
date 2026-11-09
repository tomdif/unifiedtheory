/- The field derivative correction has a norm-continuous charge orbit.
Polarization expresses the quadratic correction using already controlled
field-square outputs, preserving complex coherent superpositions. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterShearCorrection
import UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentFieldDerivativeOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit (factorOutput factorOutput_graph factorOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (fieldSlope powerSlope)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
include hb in
theorem actual_field_orbit (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph)
    (l : Transverse →L[ℝ] ℝ) (i : Fin 2) :
    ∃ u : ℝ → Hilbert, Continuous u ∧ ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  let idx : Fin 8 := ⟨i.val+5,by omega⟩
  have hF : energyFactor ε hε h modelDirections l idx = matterFactor ε hε h (fieldPower l i) := by
    fin_cases i <;> rfl
  let u : ℝ → Hilbert := fun θ => ∑ j, z j •
    factorOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (q j)) modelDirections l idx
  have hc : Continuous u := continuous_finset_sum Finset.univ (fun j _ =>
    ((factorOutput_orbit_continuous ε a h hε ha hh hb (q j) modelDirections l idx).comp
      (continuous_const.mul continuous_id)).const_smul (z j))
  refine ⟨u,hc,?_⟩
  intro θ
  have hm : (action h hh (2*Real.pi*θ) (∑ j, z j • state ε a h hε ha hh (q j)),u θ) ∈
      (matterFactor ε hε h (fieldPower l i)).graph := by
    rw [← hF,map_sum]
    simp only [map_smul,action_state]
    have hs := (energyFactor ε hε h modelDirections l idx).graph.sum_mem
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        (energyFactor ε hε h modelDirections l idx).graph.smul_mem (z j)
          (factorOutput_graph ε a h hε ha hh hb (parameter (2*Real.pi*θ) (q j)) modelDirections l idx))
    simpa only [u,Prod.smul_mk,← prod_mk_sum] using hs
  obtain ⟨g',ht,hu⟩ := (composition_graph _ _ _ _).mp hm
  have eg : g' = g θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hg θ) rfl
  exact eg ▸ hu

include hb in
theorem derivative_orbit (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph)
    (l : Transverse →L[ℝ] ℝ) (i : Fin 2) :
    ∃ d : ℝ → Hilbert, Continuous d ∧ ∀ θ,
      d θ =ᵐ[volume] fun x => powerSlope l i x*g θ x := by
  fin_cases i
  · obtain ⟨d,hc,hd⟩ := actual_field_orbit ε a h hε ha hh hb f hf g hg (fieldSlope l) 0
    refine ⟨d,hc,fun θ => ?_⟩
    simpa only [powerSlope,Fin.val_zero,Nat.zero_add,Nat.cast_one,pow_zero,one_mul,pow_one] using
      (fieldPower_graph (fieldSlope l) 0 (g θ) (d θ)).mp (hd θ)
  · obtain ⟨u,hu,hug⟩ := actual_field_orbit ε a h hε ha hh hb f hf g hg (l+fieldSlope l) 1
    obtain ⟨v,hv,hvg⟩ := actual_field_orbit ε a h hε ha hh hb f hf g hg l 1
    obtain ⟨w,hw,hwg⟩ := actual_field_orbit ε a h hε ha hh hb f hf g hg (fieldSlope l) 1
    refine ⟨fun θ => u θ-v θ-w θ,(hu.sub hv).sub hw,fun θ => ?_⟩
    filter_upwards [Lp.coeFn_sub (u θ-v θ) (w θ),Lp.coeFn_sub (u θ) (v θ),
      (fieldPower_graph (l+fieldSlope l) 1 (g θ) (u θ)).mp (hug θ),
      (fieldPower_graph l 1 (g θ) (v θ)).mp (hvg θ),
      (fieldPower_graph (fieldSlope l) 1 (g θ) (w θ)).mp (hwg θ)] with x hx hy hu hv hw
    simp only [hx,Pi.sub_apply,hy,hu,hv,hw,powerSlope,ContinuousLinearMap.add_apply,Complex.ofReal_add]
    norm_num
    ring

#print axioms actual_field_orbit
#print axioms derivative_orbit
end
end UnifiedTheory.Audit.KFCausalCoherentFieldDerivativeOrbit
