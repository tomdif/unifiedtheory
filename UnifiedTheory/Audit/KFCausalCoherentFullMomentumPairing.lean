/- The full energy-form pairing of f with its actual B f is the integral
of all eight weighted factor pairings. Its signed weak response is thus
well defined on the coherent span. This is not a time-derivative theorem. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit (factorOutput factorOutput_graph factorOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift (lift lift_embedding lift_pairing)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

include hb in
theorem input_outputs (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ g : Fin 8 → ℝ → Hilbert, (∀ i, Continuous (g i)) ∧ (∀ i, MemLp (g i) 2 angleMeasure) ∧
      ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  let g : Fin 8 → ℝ → Hilbert := fun i θ =>
    ∑ j, z j • factorOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (q j)) modelDirections pointField i
  have hc (i : Fin 8) : Continuous (g i) := continuous_finset_sum Finset.univ (fun j _ =>
    ((factorOutput_orbit_continuous ε a h hε ha hh hb (q j) modelDirections pointField i).comp
      (continuous_const.mul continuous_id)).const_smul (z j))
  refine ⟨g,hc,fun i => continuous_angle_memLp _ (hc i),?_⟩
  intro θ i
  rw [map_sum]
  simp only [map_smul,action_state]
  have hs := (F i).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    (F i).graph.smul_mem (z j)
      (factorOutput_graph ε a h hε ha hh hb (parameter (2*Real.pi*θ) (q j)) modelDirections pointField i))
  simpa only [g,Prod.smul_mk,← prod_mk_sum] using hs

def pairingDensity (g k : Fin 8 → ℝ → Hilbert) (θ : ℝ) : ℂ :=
  ∑ i : Fin 8, inner ℂ (energyWeight mass2 quartic vacuum t i • g i θ)
    (energyWeight mass2 quartic vacuum t i • k i θ)

theorem pairingDensity_continuous (g k : Fin 8 → ℝ → Hilbert)
    (hg : ∀ i, Continuous (g i)) (hk : ∀ i, Continuous (k i)) :
    Continuous (pairingDensity mass2 quartic vacuum t g k) :=
  continuous_finset_sum Finset.univ (fun i _ => ((hg i).const_smul _).inner ((hk i).const_smul _))

theorem pairingDensity_integrable (g k : Fin 8 → ℝ → Hilbert)
    (hg : ∀ i, Continuous (g i)) (hk : ∀ i, Continuous (k i)) :
    Integrable (pairingDensity mass2 quartic vacuum t g k) angleMeasure :=
  (continuous_angle_memLp _ (pairingDensity_continuous mass2 quartic vacuum t g k hg hk)).integrable (by norm_num)

theorem actual_pairing (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (u v : Full) (hu : embed u = f) (hv : embed v = b) :
    ∃ g k : Fin 8 → ℝ → Hilbert,
      (∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (∀ i, MemLp (g i) 2 angleMeasure ∧ MemLp (k i) 2 angleMeasure) ∧
      Integrable (pairingDensity mass2 quartic vacuum t g k) angleMeasure ∧
      inner ℂ (out u) (out v) = ∫ θ, pairingDensity mass2 quartic vacuum t g k θ ∂angleMeasure ∧
      (-2/h)*(inner ℂ (out u) (out v)).im =
        ∫ θ, (-2/h)*(pairingDensity mass2 quartic vacuum t g k θ).im ∂angleMeasure := by
  exact (input_outputs ε h hε hh hb a ha f hf).elim fun g hg =>
    (KFCausalCoherentMomentumFullOrbit.actual_outputs ε a h hε ha hh hb modelDirections pointField f hf b hB).elim
      fun k hk => by
        have eu : lift ε h hε hh hb mass2 quartic vacuum t f g hg.1 hg.2.2 = u :=
          embedding_injective ε hε h hp hh mass2 quartic vacuum t
            ((lift_embedding ε h hε hh hb mass2 quartic vacuum t f g hg.1 hg.2.2).trans hu.symm)
        have ev : lift ε h hε hh hb mass2 quartic vacuum t b k hk.1 hk.2.2 = v :=
          embedding_injective ε hε h hp hh mass2 quartic vacuum t
            ((lift_embedding ε h hε hh hb mass2 quartic vacuum t b k hk.1 hk.2.2).trans hv.symm)
        have he : inner ℂ (out u) (out v) =
            ∫ θ, pairingDensity mass2 quartic vacuum t g k θ ∂angleMeasure :=
          (congrArg₂ (inner ℂ) (congrArg out eu) (congrArg out ev)).symm.trans
            (lift_pairing ε h hε hh hb mass2 quartic vacuum t f b g k hg.1 hk.1 hg.2.2 hk.2.2)
        have hi := pairingDensity_integrable mass2 quartic vacuum t g k hg.1 hk.1
        refine ⟨g,k,fun θ i => ⟨hg.2.2 θ i,hk.2.2 θ i⟩,fun i => ⟨hg.1 i,hk.1 i⟩,
          fun i => ⟨hg.2.1 i,hk.2.1 i⟩,hi,he,?_⟩
        exact (congrArg (fun z : ℂ => (-2/h)*z.im) he).trans
          ((congrArg (fun r : ℝ => (-2/h)*r) (integral_im hi).symm).trans
            (integral_const_mul (-2/h) _).symm)

#print axioms input_outputs
#print axioms pairingDensity_continuous
#print axioms pairingDensity_integrable
#print axioms actual_pairing
end
end UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing
