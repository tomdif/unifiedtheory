/- Common clock, kinetic and vacuum graphs for the actual momentum of
every finite coherent superposition. All output charge orbits are continuous
and square integrable. The two ordered matter factors remain separate. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit
import UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumFactorL2
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "B" => pureMomentum ε hε h

theorem coherentSpan_le_pureDomain : coherentSpan ε a h hε ha hh ≤ (B).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (pureOutput_graph ε a h hε ha hh k)

theorem actual_clock_kinetic_outputs (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (B).graph) :
    ∃ (c : ℝ → Hilbert) (k : Transverse → ℝ → Hilbert),
      (∀ θ, (action h hh (2*Real.pi*θ) b,c θ) ∈ (clockHalf ε).graph ∧
        ∀ v, (action h hh (2*Real.pi*θ) b,k v θ) ∈ (clockMomentum ε h v).graph) ∧
      Continuous c ∧ (∀ v, Continuous (k v)) ∧ MemLp c 2 angleMeasure ∧
      ∀ v, MemLp (k v) 2 angleMeasure := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hs : (∑ i, z i • state ε a h hε ha hh (q i),
      ∑ i, z i • pureOutput ε a h hε ha hh (q i)) ∈ (B).graph := by
    have hs := (B).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (B).graph.smul_mem (z i) (pureOutput_graph ε a h hε ha hh (q i)))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have eb : b = ∑ i, z i • pureOutput ε a h hε ha hh (q i) := (B).mem_graph_snd_inj' hB hs rfl
  let c : ℝ → Hilbert := fun θ => ∑ i, z i • clockMomentumOutput ε a h hε ha hh (parameter (2*Real.pi*θ) (q i))
  let k : Transverse → ℝ → Hilbert := fun v θ =>
    ∑ i, z i • kineticMomentumOutput ε a h hε ha hh (parameter (2*Real.pi*θ) (q i)) v
  have hc : Continuous c := continuous_finset_sum Finset.univ (fun i _ =>
    ((clockMomentumOutput_orbit_continuous ε a h hε ha hh (q i)).comp
      (continuous_const.mul continuous_id)).const_smul (z i))
  have hk (v : Transverse) : Continuous (k v) := continuous_finset_sum Finset.univ (fun i _ =>
    ((kineticMomentumOutput_orbit_continuous ε a h hε ha hh (q i) v).comp
      (continuous_const.mul continuous_id)).const_smul (z i))
  refine ⟨c,k,?_,hc,hk,continuous_angle_memLp _ hc,fun v => continuous_angle_memLp _ (hk v)⟩
  intro θ
  rw [eb,map_sum]
  simp only [map_smul]
  constructor
  · have hs := (clockHalf ε).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (clockHalf ε).graph.smul_mem (z i) (clockMomentumOutput_action_graph ε a h hε ha hh (2*Real.pi*θ) (q i)))
    simpa only [c,Prod.smul_mk,← prod_mk_sum] using hs
  · intro v
    have hs := (clockMomentum ε h v).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (clockMomentum ε h v).graph.smul_mem (z i)
        (kineticMomentumOutput_action_graph ε a h hε ha hh (2*Real.pi*θ) (q i) v))
    simpa only [k,Prod.smul_mk,← prod_mk_sum] using hs

theorem exists_clock_kinetic_outputs (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (c : ℝ → Hilbert) (k : Transverse → ℝ → Hilbert),
      (f,b) ∈ (B).graph ∧
      (∀ θ, (action h hh (2*Real.pi*θ) b,c θ) ∈ (clockHalf ε).graph ∧
        ∀ v, (action h hh (2*Real.pi*θ) b,k v θ) ∈ (clockMomentum ε h v).graph) ∧
      Continuous c ∧ (∀ v, Continuous (k v)) ∧ MemLp c 2 angleMeasure ∧
      ∀ v, MemLp (k v) 2 angleMeasure := by
  let hd := coherentSpan_le_pureDomain ε a h hε ha hh hf
  let b := (B) ⟨f,hd⟩
  have hb : (f,b) ∈ (B).graph := (B).mem_graph ⟨f,hd⟩
  obtain ⟨c,k,hg,hc,hk,hm,hn⟩ := actual_clock_kinetic_outputs ε a h hε ha hh f hf b hb
  exact ⟨b,c,k,hb,hg,hc,hk,hm,hn⟩

theorem exists_clock_kinetic_vacuum_outputs (hb : |h| ≤ 2*Real.pi*ε/3)
    (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (c : ℝ → Hilbert) (k : Transverse → ℝ → Hilbert) (g tb : ℝ → Hilbert),
      (f,b) ∈ (B).graph ∧
      (∀ θ, (action h hh (2*Real.pi*θ) b,c θ) ∈ (clockHalf ε).graph ∧
        (∀ v, (action h hh (2*Real.pi*θ) b,k v θ) ∈ (clockMomentum ε h v).graph) ∧
        (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph ∧
        (action h hh (2*Real.pi*θ) b,tb θ) ∈ (orderedExponential ε hε h).graph) ∧
      (Continuous c ∧ (∀ v, Continuous (k v)) ∧ Continuous g ∧ Continuous tb) ∧
      (MemLp c 2 angleMeasure ∧ (∀ v, MemLp (k v) 2 angleMeasure) ∧
        MemLp g 2 angleMeasure ∧ MemLp tb 2 angleMeasure) ∧
      Integrable (fun θ => inner ℂ (g θ) (tb θ)) angleMeasure ∧
      0 ≤ ∫ θ, KFCausalCoherentVacuumWeakForce.weakResponse h g tb θ ∂angleMeasure := by
  obtain ⟨b,g,j,tb,bg,hB,hg,hc,hm,hi,hs⟩ :=
    KFCausalCoherentVacuumCompositionL2.exists_actual_L2_response ε a h hε ha hh hb f hf
  obtain ⟨c,k,hck,hcc,hkc,hcm,hkm⟩ := actual_clock_kinetic_outputs ε a h hε ha hh f hf b hB
  exact ⟨b,c,k,g,tb,hB,fun θ => ⟨(hck θ).1,(hck θ).2,(hg θ).1,(hg θ).2.2.1⟩,
    ⟨hcc,hkc,hc.1,hc.2.2.1⟩,⟨hcm,hkm,hm.1,hm.2.2.1⟩,hi,hs⟩

#print axioms coherentSpan_le_pureDomain
#print axioms actual_clock_kinetic_outputs
#print axioms exists_clock_kinetic_outputs
#print axioms exists_clock_kinetic_vacuum_outputs
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumFactorL2
