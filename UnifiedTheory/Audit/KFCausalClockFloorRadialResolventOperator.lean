/- On the maximal radial operator domain, the radial Yosida symbol action equals
the radial resolvent regularizer applied to the radial output. Consequently the
radial resolvent regularizer commutes with the maximal radial operator,
contracts the radial operator norm, and provides an explicit 1/N resolvent
approximation bound in the Hilbert norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRoot
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrongLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial symbol)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer (multiplier action action_coe
  action_norm radial_graph radial_domain sequence_tendsto)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

local notation "Kr" => operator ε hε h
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

theorem symbol_eq_multiplier_mul_radial (x : Joint 2 4) :
    symbol ε h N x=multiplier ε h N x*radial ε h x := by
  unfold symbol multiplier
  ring

theorem yosida_eq_action_on_graph (f r : Hilbert)
    (hfr : (f,r) ∈ (Kr).graph) :
    M f=action ε hε h N hN r := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN f,
    action_coe ε hε h N hN r,
    (realPullback_graph chargeCoordinates (radial ε h) _ f r).mp hfr]
    with x h1 h2 h3
  rw [h1,h2,h3,symbol_eq_multiplier_mul_radial ε h N x]
  push_cast
  ring

theorem graph_commute (f r : Hilbert) (hfr : (f,r) ∈ (Kr).graph) :
    (action ε hε h N hN f,action ε hε h N hN r) ∈ (Kr).graph :=
  yosida_eq_action_on_graph ε hε h N hN f r hfr ▸ radial_graph ε hε h N hN f

theorem operator_commute (x : (Kr).domain) :
    Kr ⟨action ε hε h N hN (x:Hilbert),radial_domain ε hε h N hN (x:Hilbert)⟩=
      action ε hε h N hN (Kr x) :=
  (Kr).mem_graph_snd_inj'
    ((Kr).mem_graph ⟨action ε hε h N hN (x:Hilbert),radial_domain ε hε h N hN (x:Hilbert)⟩)
    (graph_commute ε hε h N hN (x:Hilbert) (Kr x) ((Kr).mem_graph x)) rfl

theorem operator_norm_le (x : (Kr).domain) :
    ‖Kr ⟨action ε hε h N hN (x:Hilbert),radial_domain ε hε h N hN (x:Hilbert)⟩‖ ≤
      ‖Kr x‖ := by
  rw [operator_commute ε hε h N hN x]
  exact action_norm ε hε h N hN (Kr x)

theorem self_sub_action_eq (f r : Hilbert) (hfr : (f,r) ∈ (Kr).graph) :
    f-action ε hε h N hN f=(N⁻¹:ℂ) • action ε hε h N hN r := by
  have hsub : f-action ε hε h N hN f=(N⁻¹:ℂ) • M f := by
    change f-(f-(N⁻¹:ℂ) • M f)=(N⁻¹:ℂ) • M f
    exact sub_sub_cancel f ((N⁻¹:ℂ) • M f)
  rw [hsub,yosida_eq_action_on_graph ε hε h N hN f r hfr]

theorem self_sub_action_norm_le (f r : Hilbert) (hfr : (f,r) ∈ (Kr).graph) :
    ‖f-action ε hε h N hN f‖ ≤ N⁻¹*‖r‖ := by
  rw [self_sub_action_eq ε hε h N hN f r hfr,norm_smul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  exact mul_le_mul_of_nonneg_left (action_norm ε hε h N hN r) (inv_nonneg.mpr hN.le)

theorem graph_sequence_tendsto (f r : Hilbert) (hfr : (f,r) ∈ (Kr).graph) :
    Tendsto (fun n : ℕ =>
      (action ε hε h ((n:ℝ)+1) (by positivity) f,
        action ε hε h ((n:ℝ)+1) (by positivity) r))
      atTop (𝓝 (f,r)) :=
  (sequence_tendsto ε hε h f).prodMk_nhds
    ((KFCausalClockFloorRadialYosidaStrongLimit.graph_tendsto ε hε h f r hfr).congr'
      (Eventually.of_forall (fun n =>
        yosida_eq_action_on_graph ε hε h ((n:ℝ)+1) (by positivity) f r hfr)))

theorem operator_sequence_tendsto (x : (Kr).domain) :
    Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert),
        radial_domain ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert)⟩)
      atTop (𝓝 (Kr x)) :=
  (sequence_tendsto ε hε h (Kr x)).congr' (Eventually.of_forall (fun n =>
    (operator_commute ε hε h ((n:ℝ)+1) (by positivity) x).symm))

#print axioms symbol_eq_multiplier_mul_radial
#print axioms yosida_eq_action_on_graph
#print axioms graph_commute
#print axioms operator_commute
#print axioms operator_norm_le
#print axioms self_sub_action_eq
#print axioms self_sub_action_norm_le
#print axioms graph_sequence_tendsto
#print axioms operator_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator
