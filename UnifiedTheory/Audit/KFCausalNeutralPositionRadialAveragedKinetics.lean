/- Charge averaging of the actual radial-test kinetic product rule.
This constructs the output section and bounds its correction. Application
to the physical full-form input supplies its kinetic projection only;
the remaining three matter rows are not asserted here. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph
import UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedKinetics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action action_charge)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph (select graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics (OutputSpace AveragedGraph full_averaged_graph selected_output_bound)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (δ v : ℝ) (hδ : 0 < δ)

def correction (f : Hilbert) : OutputSpace :=
  (extra ε hε h δ v hδ).compLp (orbit (group h hne) (2*Real.pi) f)

def transformed (f : Hilbert) (y : OutputSpace) : OutputSpace :=
  (outputAction h δ v hδ).compLp y+correction ε hε h hne δ v hδ f

theorem outputLp_norm (y : OutputSpace) : ‖(outputAction h δ v hδ).compLp y‖ ≤ ‖y‖ := by
  have hop : ‖outputAction h δ v hδ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun y => by simpa only [one_mul] using outputAction_norm h δ v hδ y)
  exact ((outputAction h δ v hδ).norm_compLp_le y).trans
    ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (one_mul _))

theorem correction_bound (f : Hilbert) :
    ‖correction ε hε h hne δ v hδ f‖ ≤ |h| *responseConstant ε δ v*‖f‖ := by
  have hop : ‖extra ε hε h δ v hδ‖ ≤ |h| *responseConstant ε δ v :=
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (responseConstant_nonneg _ _ _))
      (extra_bound ε hε h δ v hδ)
  exact ((extra ε hε h δ v hδ).norm_compLp_le _).trans
    ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (by rw [(orbit _ _).norm_map]))

theorem averaged_graph_action (t : ℝ) (f : Hilbert) (y : OutputSpace)
    (hfy : AveragedGraph ε h hne t f y) :
    AveragedGraph ε h hne t (action h δ v hδ f) (transformed ε hε h hne δ v hδ f y) := by
  filter_upwards [hfy,
    Lp.coeFn_add ((outputAction h δ v hδ).compLp y) (correction ε hε h hne δ v hδ f),
    (outputAction h δ v hδ).coeFn_compLp y,
    (extra ε hε h δ v hδ).coeFn_compLp (orbit (group h hne) (2*Real.pi) f),
    orbitState_coe (group h hne) (2*Real.pi) f] with θ hg ha hm he ho
  change (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) (action h δ v hδ f),
    ((outputAction h δ v hδ).compLp y+correction ε hε h hne δ v hδ f) θ) ∈ _
  rw [ha]
  simp only [Pi.add_apply,hm]
  change (_,outputAction h δ v hδ (y θ)+
    (extra ε hε h δ v hδ).compLp (orbit (group h hne) (2*Real.pi) f) θ) ∈ _
  change (orbit (group h hne) (2*Real.pi) f) θ =
    KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) f at ho
  rw [he,ho,← action_charge h hne δ v hδ]
  exact graph_action ε hε h δ v hδ hne t _ _ hg

theorem transformed_correction_bound (f : Hilbert) (y : OutputSpace) :
    ‖transformed ε hε h hne δ v hδ f y-(outputAction h δ v hδ).compLp y‖ ≤
      |h| *responseConstant ε δ v*‖f‖ := by
  rw [transformed,add_sub_cancel_left]
  exact correction_bound ε hε h hne δ v hδ f

theorem transformed_bound (f : Hilbert) (y : OutputSpace) :
    ‖transformed ε hε h hne δ v hδ f y‖ ≤ ‖y‖+|h| *responseConstant ε δ v*‖f‖ := by
  exact (norm_add_le _ _).trans
    (add_le_add (outputLp_norm h δ v hδ y) (correction_bound ε hε h hne δ v hδ f))

theorem kinetic_energy_upper (f : Hilbert) (y : OutputSpace) :
    ‖transformed ε hε h hne δ v hδ f y‖^2 ≤
      ‖y‖^2+(|h| *responseConstant ε δ v*‖f‖)*(2*‖y‖+|h| *responseConstant ε δ v*‖f‖) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (transformed_bound ε hε h hne δ v hδ f y) 2).trans_eq (by ring)

variable (hh : |h| ≤ Real.pi*ε) (m g k t : ℝ)
local notation "J" => embedding ε hε h hh hne m g k t
local notation "A" => energyOutput ε hε h hh hne m g k t

theorem physical_averaged_graph (u : AveragedSpace ε hε h hh hne m g k t) :
    AveragedGraph ε h hne t (action h δ v hδ (J u))
      (transformed ε hε h hne δ v hδ (J u) ((select.compLpL 2 angleMeasure) (A u))) :=
  averaged_graph_action ε hε h hne δ v hδ t _ _ (full_averaged_graph ε hε h hh hne m g k t u)

theorem physical_output_bound (u : AveragedSpace ε hε h hh hne m g k t) :
    ‖transformed ε hε h hne δ v hδ (J u) ((select.compLpL 2 angleMeasure) (A u))‖ ≤
      ‖A u‖+|h| *responseConstant ε δ v*‖J u‖ := by
  apply (transformed_bound ε hε h hne δ v hδ (J u) _).trans
  exact add_le_add (selected_output_bound ε hε h hh hne m g k t u) le_rfl

#print axioms outputLp_norm
#print axioms correction_bound
#print axioms averaged_graph_action
#print axioms transformed_correction_bound
#print axioms transformed_bound
#print axioms kinetic_energy_upper
#print axioms physical_averaged_graph
#print axioms physical_output_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedKinetics
