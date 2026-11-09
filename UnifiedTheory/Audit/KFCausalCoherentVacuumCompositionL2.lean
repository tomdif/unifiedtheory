/- Full norm-square integrability of the actual vacuum/momentum outputs
on the coherent span. Complex coefficients and distinct seed frequencies
are retained. This supplies a form pairing, not a time-evolution theorem. -/
import UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionL2
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit
open UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator (state_regular span_regular)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph (graph_charge)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "T" => orderedExponential ε hε h
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h

include hb in
theorem actual_ordered_momentum_continuous (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b₀ : Hilbert) (hB : (f,b₀) ∈ (B).graph) (tb : ℝ → Hilbert)
    (hT : ∀ θ, (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph) : Continuous tb := by
  obtain ⟨n,k,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hd (i : Fin n) : state ε a h hε ha hh (k i) ∈ (B).domain :=
    (KFCausalClockFloorPureClockVacuumCommutator.core_pure_domains ε hε h hh _ _
      (state_regular ε a h hε ha hh hb (k i))).1
  let b (i : Fin n) : Hilbert := (B) ⟨state ε a h hε ha hh (k i),hd i⟩
  have hbi (i : Fin n) : (state ε a h hε ha hh (k i),b i) ∈ (B).graph := (B).mem_graph ⟨_,hd i⟩
  have hsum : (∑ i, z i • state ε a h hε ha hh (k i),∑ i, z i • b i) ∈ (B).graph := by
    have hs := (B).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (B).graph.smul_mem (z i) (hbi i))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have eb : b₀ = ∑ i, z i • b i := (B).mem_graph_snd_inj' hB hsum rfl
  have hti (θ : ℝ) (i : Fin n) :
      (action h hh (2*Real.pi*θ) (b i),orderedMomentumOutput ε a h hε ha hh hb
        (parameter (2*Real.pi*θ) (k i))) ∈ (T).graph := by
    apply orderedMomentumOutput_graph ε a h hε ha hh hb
    rw [← action_state]
    exact graph_charge ε hε h hh (2*Real.pi*θ) _ _ (hbi i)
  have ht (θ : ℝ) : (action h hh (2*Real.pi*θ) b₀,
      ∑ i, z i • orderedMomentumOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (k i))) ∈ (T).graph := by
    rw [eb,map_sum]
    simp only [map_smul]
    have hs := (T).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (T).graph.smul_mem (z i) (hti θ i))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have et : tb = fun θ => ∑ i, z i • orderedMomentumOutput ε a h hε ha hh hb
      (parameter (2*Real.pi*θ) (k i)) :=
    funext (fun θ => (T).mem_graph_snd_inj' (hT θ) (ht θ) rfl)
  rw [et]
  exact continuous_finset_sum Finset.univ (fun i _ =>
    ((orderedMomentumOutput_orbit_continuous ε a h hε ha hh hb (k i)).comp
      (continuous_const.mul continuous_id)).const_smul (z i))

include hb in
theorem actual_outputs_continuous (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b₀ : Hilbert) (g j tb bg : ℝ → Hilbert) (hB : (f,b₀) ∈ (B).graph)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
      (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph ∧ (g θ,bg θ) ∈ (B).graph) :
    Continuous g ∧ Continuous j ∧ Continuous tb ∧ Continuous bg := by
  obtain ⟨hcg,hcj⟩ := KFCausalCoherentVacuumWeakForce.actual_outputs_continuous ε a h hε ha hh hb f hf g j
    (fun θ => ⟨(hg θ).1,(hg θ).2.1⟩)
  have hct := actual_ordered_momentum_continuous ε a h hε ha hh hb f hf b₀ hB tb (fun θ => (hg θ).2.2.1)
  have he : bg = fun θ => tb θ+pureCorrection ε hε h hb (g θ) (j θ) := by
    funext θ
    have hc := KFCausalClockFloorPureClockVacuumCommutator.commutator_graph ε hε h hb hh
      _ _ _ _ _ _ (span_regular ε a h hε ha hh hb _
        (action_coherentSpan ε a h hε ha hh (2*Real.pi*θ) f hf) _ (hg θ).1)
      (graph_charge ε hε h hh (2*Real.pi*θ) f b₀ hB) (hg θ).2.2.1 (hg θ).2.2.2 (hg θ).2.1
    rw [← hc]
    abel
  refine ⟨hcg,hcj,hct,?_⟩
  rw [he]
  exact hct.add (((correction ε hε h hb).continuous.comp hcg).sub
    ((shearCorrection ε hε h hb).continuous.comp hcj))

include hb in
theorem actual_outputs_memLp (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b₀ : Hilbert) (g j tb bg : ℝ → Hilbert) (hB : (f,b₀) ∈ (B).graph)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
      (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph ∧ (g θ,bg θ) ∈ (B).graph) :
    MemLp g 2 angleMeasure ∧ MemLp j 2 angleMeasure ∧ MemLp tb 2 angleMeasure ∧ MemLp bg 2 angleMeasure := by
  obtain ⟨hc,hj,ht,hbg⟩ := actual_outputs_continuous ε a h hε ha hh hb f hf b₀ g j tb bg hB hg
  exact ⟨continuous_angle_memLp _ hc,continuous_angle_memLp _ hj,
    continuous_angle_memLp _ ht,continuous_angle_memLp _ hbg⟩

include hb in
theorem complex_pairing_integrable (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b₀ : Hilbert) (g j tb bg : ℝ → Hilbert) (hB : (f,b₀) ∈ (B).graph)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
      (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph ∧ (g θ,bg θ) ∈ (B).graph) :
    Integrable (fun θ => inner ℂ (g θ) (tb θ)) angleMeasure := by
  obtain ⟨hc,_,ht,_⟩ := actual_outputs_continuous ε a h hε ha hh hb f hf b₀ g j tb bg hB hg
  exact (continuous_angle_memLp _ (hc.inner ht)).integrable (by norm_num)

include hb in
theorem exists_actual_L2_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b₀ : Hilbert) (g j tb bg : ℝ → Hilbert), (f,b₀) ∈ (B).graph ∧
      (∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
        (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph ∧ (g θ,bg θ) ∈ (B).graph) ∧
      (Continuous g ∧ Continuous j ∧ Continuous tb ∧ Continuous bg) ∧
      (MemLp g 2 angleMeasure ∧ MemLp j 2 angleMeasure ∧ MemLp tb 2 angleMeasure ∧ MemLp bg 2 angleMeasure) ∧
      Integrable (fun θ => inner ℂ (g θ) (tb θ)) angleMeasure ∧
      0 ≤ ∫ θ, KFCausalCoherentVacuumWeakForce.weakResponse h g tb θ ∂angleMeasure := by
  obtain ⟨b₀,g,j,tb,bg,_,_,hB,hg,_,_,hL,hle⟩ :=
    KFCausalCoherentVacuumWeakForce.exists_fixed_momentum_response ε a h hε ha hh hb f hf
  exact ⟨b₀,g,j,tb,bg,hB,hg,
    actual_outputs_continuous ε a h hε ha hh hb f hf b₀ g j tb bg hB hg,
    actual_outputs_memLp ε a h hε ha hh hb f hf b₀ g j tb bg hB hg,
    complex_pairing_integrable ε a h hε ha hh hb f hf b₀ g j tb bg hB hg,hL.trans hle⟩

#print axioms actual_ordered_momentum_continuous
#print axioms actual_outputs_continuous
#print axioms actual_outputs_memLp
#print axioms complex_pairing_integrable
#print axioms exists_actual_L2_response
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionL2
