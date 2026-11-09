/- The completed physical free Hamiltonian is diagonal in the derived
circular charge transform, including both continuous spectator variables
and the entire maximal operator domain. -/
import UnifiedTheory.Audit.KFCausalFreeCircularPacketGraph
import UnifiedTheory.Audit.KFCausalSpectatorEnergyCore
import UnifiedTheory.Audit.KFCausalCompleteFiberGraphs
import UnifiedTheory.Audit.KFCausalCircularChargeDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFreeCircularSpectral
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (Index)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalCompleteFiberGraphs (column)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_graph)
open KFCausalSpectatorEnergyPackets (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hbound : |h| ≤ Real.pi*ε/3) (t : ℝ)

def width : ℝ := Real.exp t/(2*h)

include hpos in
theorem width_positive : 0 < width h t :=
  div_pos (Real.exp_pos t) (mul_pos (by norm_num) hpos)

def transform : Hilbert ≃ₗᵢ[ℂ] KFCausalJointHermiteFourierTransform.Coefficients :=
  KFCausalCircularChargeTransform.transform h hpos.ne' (width h t) (width_positive h hpos t)

def chargedEnergy (i : Index) : ℝ :=
  h*Real.exp t*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2)

def fiberEnergy (i : Index) : Block 2 → ℝ := energy ε (momentumScale h) (chargedEnergy h t i)

include hε in
theorem fiberEnergy_continuous (i : Index) : Continuous (fiberEnergy ε h t i) :=
  KFCausalSpectatorEnergyPackets.energy_continuous ε hε _ _

def fiber (i : Index) : BlockHilbert 2 →ₗ.[ℂ] BlockHilbert 2 :=
  realPullback (LinearIsometryEquiv.refl ℂ _) (fiberEnergy ε h t i)
    (fiberEnergy_continuous ε hε h t i).measurable

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert :=
  KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne'
    (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hbound) 0 0 0 t

theorem selfAdjoint : IsSelfAdjoint (hamiltonian ε hε h hpos hbound t) :=
  KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hpos.ne'
    (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hbound) 0 0 0 t

theorem fiber_selfAdjoint (i : Index) : IsSelfAdjoint (fiber ε hε h t i) :=
  KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint _ _ _

theorem core_graph (i : Index) (k : Block 2) :
    (column (transform h hpos t) i (KFCausalSpectatorEnergyCore.input ε hε k),
      column (transform h hpos t) i
        (KFCausalSpectatorEnergyCore.coreOutput ε hε (momentumScale h) (chargedEnergy h t i) k)) ∈
      (hamiltonian ε hε h hpos hbound t).graph := by
  let B := KFCausalFourCircularChargeBasis.basis (momentumScale h)
    (momentumScale_ne_zero h hpos.ne') (width h t) (width_positive h hpos t)
  have hc (u v : BlockHilbert 1) :
      column (transform h hpos t) i (KFCausalJoinedMultiplierSum.joinProduct 1 1 u v) =
        KFCausalPhysicalSpectatorPackets.packet (B i) u v :=
    (KFCausalPhysicalSpectatorPackets.circular_packet h hpos.ne'
      (width h t) (width_positive h hpos t) i u v).symm
  simp only [KFCausalSpectatorEnergyCore.input_join, KFCausalSpectatorEnergyCore.coreOutput,
    KFCausalSpectatorEnergyPackets.output, map_add, map_smul, hc]
  exact KFCausalFreeCircularPacketGraph.hamiltonian_packet_graph ε hε h hpos.ne'
    hpos hbound t i _ _ _ _ _
    (KFCausalSpectatorCoreWeights.clock_state ε hε _)
    (KFCausalSpectatorCoreWeights.clockInverse_state ε hε _)
    (KFCausalSpectatorCoreWeights.neutralSquare_state _)

theorem fiber_inclusion (i : Index) (u v : BlockHilbert 2)
    (huv : (u,v) ∈ (fiber ε hε h t i).graph) :
    (column (transform h hpos t) i u,column (transform h hpos t) i v) ∈
      (hamiltonian ε hε h hpos hbound t).graph := by
  apply KFCausalCompleteFiberGraphs.core_inclusion
    (hamiltonian ε hε h hpos hbound t) (selfAdjoint ε hε h hpos hbound t).isClosed
    (column (transform h hpos t) i) (fiber ε hε h t i).graph
    (fun k => (KFCausalSpectatorEnergyCore.input ε hε k,
      KFCausalSpectatorEnergyCore.coreOutput ε hε (momentumScale h) (chargedEnergy h t i) k))
    (KFCausalSpectatorEnergyCore.graph_core ε hε (momentumScale h) (chargedEnergy h t i))
    (core_graph ε hε h hpos hbound t i) u v huv

/-- Full graph equality for the already constructed physical Hamiltonian. -/
theorem graph_iff (f g : Hilbert) :
    (f,g) ∈ (hamiltonian ε hε h hpos hbound t).graph ↔
      ∀ i, transform h hpos t g i =ᵐ[volume] fun x =>
        (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x := by
  rw [KFCausalCompleteFiberGraphs.graph_iff (transform h hpos t)
    (hamiltonian ε hε h hpos hbound t) (fiber ε hε h t)
    (selfAdjoint ε hε h hpos hbound t) (fiber_selfAdjoint ε hε h t)
    (fiber_inclusion ε hε h hpos hbound t)]
  apply forall_congr'
  intro i
  exact realPullback_graph _ _ _ _ _

/-- Exact maximal domain: the weighted fiber outputs exist in the direct sum. -/
theorem domain_iff (f : Hilbert) :
    f ∈ (hamiltonian ε hε h hpos hbound t).domain ↔
      ∃ G : Index → BlockHilbert 2, Memℓp G 2 ∧ ∀ i,
        G i =ᵐ[volume] fun x => (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x := by
  rw [KFCausalCompleteFiberGraphs.domain_iff (transform h hpos t)
    (hamiltonian ε hε h hpos hbound t) (fiber ε hε h t)
    (selfAdjoint ε hε h hpos hbound t) (fiber_selfAdjoint ε hε h t)
    (fiber_inclusion ε hε h hpos hbound t)]
  apply exists_congr
  intro G
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  exact realPullback_graph _ _ _ _ _

theorem zero_level_fiber (p : ℕ) (i : KFCausalCircularZeroLevelCounting.Level p) (x : Block 2) :
    fiberEnergy ε h t i.val x =
      KFCausalClockFloorFlow.clock ε (x 0)/2 +
        2*h*Real.exp t*(p+1)/KFCausalClockFloorFlow.clock ε (x 0) +
        (2*Real.pi*h)^2*x 1^2/(2*KFCausalClockFloorFlow.clock ε (x 0)) := by
  unfold fiberEnergy energy chargedEnergy momentumScale
  rw [KFCausalCircularZeroLevelCounting.level_occupation]
  push_cast
  ring

#print axioms core_graph
#print axioms fiber_inclusion
#print axioms graph_iff
#print axioms domain_iff
#print axioms zero_level_fiber
end
end UnifiedTheory.Audit.KFCausalFreeCircularSpectral
