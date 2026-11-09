/- Neutral polynomial excitations of displaced physical Gaussians are
closed under the actual charge circle. Every orbit state and its actual
pure-clock momentum lie in all eight natural factor domains. No
integrability of the energy-factor orbit is inferred from membership. -/
import UnifiedTheory.Audit.KFCausalNeutralPolynomialProjection
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (input input_coe output output_graph)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (rawState action_rawState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge (relation relation_action)
open UnifiedTheory.Audit.KFCausalNeutralPolynomialProjection (weight_measurable)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_strong_continuous)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (q k : Joint 2 4) (P : Polynomial ℂ)

def packet : Hilbert :=
  input ε a h hε ha hh (amplitude h q k) (clockFrequency h k) (source h q k) 4 P

def packetFactor (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  output ε a h hε ha hh (amplitude h q k) (clockFrequency h k) (source h q k) 4 hb P v l j

def momentum : Hilbert :=
  KFCausalPolynomialMomentumDomain.momentum ε a h hε ha hh
    (clockFrequency h k) (source h q k) 4 (amplitude h q k) P

def momentumFactor (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  KFCausalPolynomialMomentumDomain.momentumFactor ε a h hε ha hh
    (clockFrequency h k) (source h q k) 4 (amplitude h q k) hb P v l j

theorem packet_relation (hq : q (.inr 0) = 0) :
    relation (fun s : ℝ => P.eval (s:ℂ)) (rawState ε a h hε ha hh q k)
      (packet ε a h hε ha hh q k P) := by
  filter_upwards [input_coe ε a h hε ha hh (amplitude h q k) (clockFrequency h k) (source h q k) 4 P,
    rawState_configuration_coe ε a h hε ha hh q k hq] with x hp hs
  exact hp.trans (congrArg (fun z : ℂ => P.eval (x.2 4:ℂ)*z) hs.symm)

theorem packet_action (hq : q (.inr 0) = 0) (θ : ℝ) :
    action h hh θ (packet ε a h hε ha hh q k P) =
      packet ε a h hε ha hh (parameter θ q) (parameter θ k) P := by
  have hc := relation_action _ (weight_measurable P) h hh θ _ _
    (packet_relation ε a h hε ha hh q k P hq)
  rw [action_rawState] at hc
  apply Lp.ext
  exact hc.trans (packet_relation ε a h hε ha hh (parameter θ q) (parameter θ k) P
    ((parameter_clock θ q).trans hq)).symm

theorem packet_orbit_continuous (hq : q (.inr 0) = 0) :
    Continuous (fun θ => packet ε a h hε ha hh (parameter θ q) (parameter θ k) P) := by
  simp_rw [← packet_action ε a h hε ha hh q k P hq]
  exact action_strong_continuous h hh _

theorem packetFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (packet ε a h hε ha hh q k P,packetFactor ε a h hε ha hh q k P hb v l j) ∈
      (energyFactor ε hε h v l j).graph :=
  output_graph ε a h hε ha hh (amplitude h q k) (clockFrequency h k) (source h q k) 4 hb P v l j

theorem packetFactor_action_graph (hq : q (.inr 0) = 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (θ : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (action h hh θ (packet ε a h hε ha hh q k P),
      packetFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j) ∈
        (energyFactor ε hε h v l j).graph := by
  rw [packet_action ε a h hε ha hh q k P hq]
  exact packetFactor_graph ε a h hε ha hh _ _ P hb v l j

theorem packet_action_domain (hq : q (.inr 0) = 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (θ : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    action h hh θ (packet ε a h hε ha hh q k P) ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph
    (packetFactor_action_graph ε a h hε ha hh q k P hq hb θ v l j)

theorem momentum_graph :
    (packet ε a h hε ha hh q k P,momentum ε a h hε ha hh q k P) ∈
      (pureMomentum ε hε h).graph :=
  KFCausalPolynomialMomentumDomain.momentum_graph ε a h hε ha hh
    (clockFrequency h k) (source h q k) 4 (amplitude h q k) P

theorem momentum_action (hq : q (.inr 0) = 0) (θ : ℝ) :
    action h hh θ (momentum ε a h hε ha hh q k P) =
      momentum ε a h hε ha hh (parameter θ q) (parameter θ k) P := by
  have hg := KFCausalClockFloorPureClockChargeGraph.graph_charge ε hε h hh θ _ _
    (momentum_graph ε a h hε ha hh q k P)
  rw [packet_action ε a h hε ha hh q k P hq] at hg
  exact (pureMomentum ε hε h).mem_graph_snd_inj' hg
    (momentum_graph ε a h hε ha hh _ _ P) rfl

theorem momentum_orbit_continuous (hq : q (.inr 0) = 0) :
    Continuous (fun θ => momentum ε a h hε ha hh (parameter θ q) (parameter θ k) P) := by
  simp_rw [← momentum_action ε a h hε ha hh q k P hq]
  exact action_strong_continuous h hh _

theorem momentumFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a h hε ha hh q k P,momentumFactor ε a h hε ha hh q k P hb v l j) ∈
      (energyFactor ε hε h v l j).graph :=
  KFCausalPolynomialMomentumDomain.momentumFactor_graph ε a h hε ha hh
    (clockFrequency h k) (source h q k) 4 (amplitude h q k) hb P v l j

theorem momentumFactor_action_graph (hq : q (.inr 0) = 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (θ : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (action h hh θ (momentum ε a h hε ha hh q k P),
      momentumFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j) ∈
        (energyFactor ε hε h v l j).graph := by
  rw [momentum_action ε a h hε ha hh q k P hq]
  exact momentumFactor_graph ε a h hε ha hh _ _ P hb v l j

theorem momentum_action_domain (hq : q (.inr 0) = 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (θ : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    action h hh θ (momentum ε a h hε ha hh q k P) ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph
    (momentumFactor_action_graph ε a h hε ha hh q k P hq hb θ v l j)

#print axioms packet_relation
#print axioms packet_action
#print axioms packet_orbit_continuous
#print axioms packetFactor_graph
#print axioms packetFactor_action_graph
#print axioms packet_action_domain
#print axioms momentum_graph
#print axioms momentum_action
#print axioms momentum_orbit_continuous
#print axioms momentumFactor_graph
#print axioms momentumFactor_action_graph
#print axioms momentum_action_domain
end
end UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit
