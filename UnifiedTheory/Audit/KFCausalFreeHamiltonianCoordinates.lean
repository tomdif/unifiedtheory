/- Exact full-domain free Hamiltonian graph in charged/spectator coordinates. -/
import UnifiedTheory.Audit.KFCausalClockFloorFreeOperatorSum
import UnifiedTheory.Audit.KFCausalSpectatorFourierCoordinates
import UnifiedTheory.Audit.KFCausalMultiplierReindex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFreeHamiltonianCoordinates
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalChargedSpectatorCoordinates
open KFCausalSpectatorFourierCoordinates
open KFCausalMeasureUnitaryPullback
open KFCausalClockFloorFlow (clock)
open KFCausalNormalizedChargeFlow (momentumScale)

def dualAssemble : (Block 4 × Block 2) ≃ᵐ Joint 5 1 :=
  regroup.trans (split 5 1).symm

theorem dualAssemble_preserves : MeasurePreserving dualAssemble :=
  (split_preserves_volume 5 1).symm.comp regroup_preserves

theorem spectralRepack_coe (f : JointHilbert 5 1) :
    spectralRepack f =ᵐ[volume] f ∘ dualAssemble := by
  filter_upwards [unitaryPullback_coe regroup regroup_preserves ((coordinates 5 1).symm f),
    regroup_preserves.quasiMeasurePreserving.ae
      (unitaryPullback_symm_coe (split 5 1) (split_preserves_volume 5 1) f)] with x h1 h2
  exact h1.trans h2

def positionWeight (ε h : ℝ) (x : Block 4 × Block 2) : ℝ :=
  (momentumScale h^2*(x.1 0^2+x.1 2^2)+x.1 1^2+x.1 3^2)/(2*clock ε (x.2 0))

def staticWeight (ε h : ℝ) (x : Block 4 × Block 2) : ℝ :=
  (clock ε (x.2 0)+(x.1 0^2+x.1 2^2+
    momentumScale h^2*(x.1 1^2+x.1 3^2+x.2 1^2))/clock ε (x.2 0))/2

theorem radial_repack (ε h : ℝ) (x : Block 4 × Block 2) :
    KFCausalClockFloorRadialYosidaSymbol.radial ε h (assemble x) = positionWeight ε h x := by
  rw [KFCausalClockFloorRadialYosidaSymbol.radial_coordinates]
  rfl

theorem static_repack (ε h : ℝ) (x : Block 4 × Block 2) :
    KFCausalClockFloorStaticMultiplierForm.symbol ε h (dualAssemble x) = staticWeight ε h x := by
  rw [KFCausalClockFloorStaticMultiplierForm.symbol_coordinates]
  change (clock ε (x.2 0)+
    (momentumScale h^2*(x.1 1^2+x.1 3^2+x.2 1^2)+x.1 0^2+x.1 2^2)/clock ε (x.2 0))/2 = _
  unfold staticWeight
  ring

def dualCoordinates : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  KFCausalChargeTransverseSplit.dualPhysical.trans spectralRepack

theorem radial_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert) :
    (f,g) ∈ (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).graph ↔
      physicalCoordinates g =ᵐ[volume] fun x =>
        (positionWeight ε h x:ℂ)*(physicalCoordinates f) x := by
  rw [KFCausalClockFloorRadialYosidaDomain.operator,
    KFCausalUnitaryRealMultiplier.realPullback_graph]
  have he := KFCausalMultiplierReindex.weighted_iff assemble assemble_preserves
    mixedCoordinates mixedCoordinates_coe
    (fun x => (KFCausalClockFloorRadialYosidaSymbol.radial ε h x:ℂ))
    (KFCausalPhysicalCircleAction.chargeCoordinates f)
    (KFCausalPhysicalCircleAction.chargeCoordinates g)
  simpa only [radial_repack, physicalCoordinates, LinearIsometryEquiv.trans_apply] using he

theorem static_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert) :
    (f,g) ∈ (KFCausalClockFloorStaticOperator.operator ε hε h).graph ↔
      dualCoordinates g =ᵐ[volume] fun x =>
        (staticWeight ε h x:ℂ)*(dualCoordinates f) x := by
  rw [KFCausalClockFloorStaticOperator.graph_iff]
  have he := KFCausalMultiplierReindex.weighted_iff dualAssemble dualAssemble_preserves
    spectralRepack spectralRepack_coe
    (fun x => (KFCausalClockFloorStaticMultiplierForm.symbol ε h x:ℂ))
    (KFCausalChargeTransverseSplit.dualPhysical f) (KFCausalChargeTransverseSplit.dualPhysical g)
  simpa only [static_repack, dualCoordinates, LinearIsometryEquiv.trans_apply] using he

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (t : ℝ)
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
  (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) 0 0 0 t

theorem graph_iff (f g : Hilbert) : (f,g) ∈ (H).graph ↔ ∃ r s : Hilbert,
    (physicalCoordinates r =ᵐ[volume] fun x =>
      (positionWeight ε h x:ℂ)*(physicalCoordinates f) x) ∧
    (dualCoordinates s =ᵐ[volume] fun x =>
      (staticWeight ε h x:ℂ)*(dualCoordinates f) x) ∧
    g = (Real.exp (2*t):ℂ) • r+s := by
  constructor
  · intro hg
    have hf := (KFCausalClockFloorFreeOperatorSum.domain_iff ε hε h hh hb t f).mp
      (LinearPMap.mem_domain_of_mem_graph hg)
    let r := KFCausalClockFloorRadialYosidaDomain.operator ε hε h ⟨f,hf.1⟩
    let s := KFCausalClockFloorStaticOperator.operator ε hε h ⟨f,hf.2⟩
    have hr : (f,r) ∈ (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).graph :=
      (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).mem_graph ⟨f,hf.1⟩
    have hs : (f,s) ∈ (KFCausalClockFloorStaticOperator.operator ε hε h).graph :=
      (KFCausalClockFloorStaticOperator.operator ε hε h).mem_graph ⟨f,hf.2⟩
    exact ⟨r,s,(radial_graph_iff ε hε h f r).mp hr,(static_graph_iff ε hε h f s).mp hs,
      (H).mem_graph_snd_inj' hg
        (KFCausalClockFloorFreeOperatorSum.graph_from_components ε hε h hh hb t f r s hr hs) rfl⟩
  · rintro ⟨r,s,hr,hs,rfl⟩
    exact KFCausalClockFloorFreeOperatorSum.graph_from_components ε hε h hh hb t f r s
      ((radial_graph_iff ε hε h f r).mpr hr) ((static_graph_iff ε hε h f s).mpr hs)

#print axioms radial_graph_iff
#print axioms static_graph_iff
#print axioms graph_iff
end
end UnifiedTheory.Audit.KFCausalFreeHamiltonianCoordinates
