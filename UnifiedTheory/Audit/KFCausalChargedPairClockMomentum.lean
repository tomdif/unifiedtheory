/- The existing paired quadratic state has an actual pure-clock momentum
with all eight natural energy-factor outputs. The construction preserves
the physical state and obtains zero charge of the momentum from proved
commutation with the physical charge projection. -/
import UnifiedTheory.Audit.KFCausalDirectionalClockMomentum
import UnifiedTheory.Audit.KFCausalChargedPairCharge
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargedPairClockMomentum
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairDomain (state combine directions)
open KFCausalChargedPairCharge (state_zeroSector)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open KFCausalStandingChargeOperator

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "ψ" => state ε a h hε ha hh

def momentum : Hilbert :=
  combine (fun i => KFCausalDirectionalClockMomentum.momentum ε a h hε ha hh 0 (directions i) 1 2)

def factor (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  combine (fun i =>
    KFCausalDirectionalClockMomentum.factor ε a h hε ha hh 0 (directions i) 1 hb 2 v l j)

theorem momentum_graph : (ψ,momentum ε a h hε ha hh) ∈ (pureMomentum ε hε h).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockMomentum.momentum_graph
    ε a h hε ha hh 0 (directions i) 1 2
  exact (pureMomentum ε hε h).graph.smul_mem (1/4:ℂ)
    ((pureMomentum ε hε h).graph.add_mem
      ((pureMomentum ε hε h).graph.sub_mem
        ((pureMomentum ε hε h).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem factor_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a h hε ha hh,factor ε a h hε ha hh hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockMomentum.factor_graph
    ε a h hε ha hh 0 (directions i) 1 hb 2 v l j
  exact (energyFactor ε hε h v l j).graph.smul_mem (1/4:ℂ)
    ((energyFactor ε hε h v l j).graph.add_mem
      ((energyFactor ε hε h v l j).graph.sub_mem
        ((energyFactor ε hε h v l j).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    momentum ε a h hε ha hh ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr fun j =>
    LinearPMap.mem_domain_of_mem_graph (factor_graph ε a h hε ha hh hb v l j)

theorem momentum_zeroSector : momentum ε a h hε ha hh ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h hε ha hh) (state_zeroSector ε a h hε ha hh)

theorem momentum_projection :
    zeroProjection h hh (momentum ε a h hε ha hh) = momentum ε a h hε ha hh :=
  zeroProjection_fixes h hh _ (momentum_zeroSector ε a h hε ha hh)

theorem momentum_charge_zero :
    (momentum ε a h hε ha hh,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (momentum_zeroSector ε a h hε ha hh)

#print axioms momentum_graph
#print axioms factor_graph
#print axioms momentum_commonEnergyDomain
#print axioms momentum_zeroSector
#print axioms momentum_projection
#print axioms momentum_charge_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairClockMomentum
