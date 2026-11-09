/- Neutral-position covariance on the averaged kinetic graph. All output
sections are actual L2 functions of charge angle, and the correction is
bounded by the physical L2 norm, independently of time and matter couplings.
The three matter rows of the full energy remain a separate obligation. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (action action_charge)
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

abbrev OutputSpace := Lp Outputs 2 angleMeasure
def responseConstant (ε v : ℝ) : ℝ := |v| *Real.sqrt (1/2)*(Real.sqrt ε)⁻¹

theorem responseConstant_nonneg (ε v : ℝ) : 0 ≤ responseConstant ε v := by
  unfold responseConstant
  positivity

def AveragedGraph (ε h : ℝ) (hne : h ≠ 0) (t : ℝ) (f : Hilbert) (y : OutputSpace) : Prop :=
  ∀ᵐ θ ∂angleMeasure,
    (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) f,y θ) ∈ graph ε h t

def correction (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ) (f : Hilbert) : OutputSpace :=
  (extra ε hε h v).compLp (orbit (group h hne) (2*Real.pi) f)

def transformed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ)
    (f : Hilbert) (y : OutputSpace) : OutputSpace :=
  (modulateOutput v).compLp (y+correction ε hε h hne v f)

theorem modulateLp_norm (v : ℝ) (y : OutputSpace) :
    ‖(modulateOutput v).compLp y‖ = ‖y‖ := by
  have he : ∀ᵐ θ ∂angleMeasure, ‖(modulateOutput v).compLp y θ‖ = ‖y θ‖ := by
    filter_upwards [(modulateOutput v).coeFn_compLp y] with θ hy
    rw [hy,modulateOutput_norm]
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_norm_ae he]

theorem correction_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ) (f : Hilbert) :
    ‖correction ε hε h hne v f‖ ≤ |h| * responseConstant ε v*‖f‖ := by
  have hop : ‖extra ε hε h v‖ ≤ |h| *responseConstant ε v :=
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (responseConstant_nonneg _ _))
      (extra_bound ε hε h v)
  exact ((extra ε hε h v).norm_compLp_le _).trans
    ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (by rw [(orbit _ _).norm_map]))

theorem averaged_graph_action (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v t : ℝ)
    (f : Hilbert) (y : OutputSpace) (hfy : AveragedGraph ε h hne t f y) :
    AveragedGraph ε h hne t (action v f) (transformed ε hε h hne v f y) := by
  filter_upwards [hfy,
    (modulateOutput v).coeFn_compLp (y+correction ε hε h hne v f),
    Lp.coeFn_add y (correction ε hε h hne v f),
    (extra ε hε h v).coeFn_compLp (orbit (group h hne) (2*Real.pi) f),
    orbitState_coe (group h hne) (2*Real.pi) f] with θ hg hm ha he ho
  change (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) (action v f),
    (modulateOutput v).compLp (y+correction ε hε h hne v f) θ) ∈ _
  rw [hm,ha]
  change (_,modulateOutput v (y θ+(extra ε hε h v).compLp (orbit (group h hne) (2*Real.pi) f) θ)) ∈ _
  change (orbit (group h hne) (2*Real.pi) f) θ =
    KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) f at ho
  rw [he,ho]
  rw [← action_charge]
  exact graph_action ε hε h hne v t _ _ hg

theorem transformed_correction_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (v : ℝ) (f : Hilbert) (y : OutputSpace) :
    ‖transformed ε hε h hne v f y-(modulateOutput v).compLp y‖ ≤
      |h| *responseConstant ε v*‖f‖ := by
  have he : transformed ε hε h hne v f y-(modulateOutput v).compLp y =
      (modulateOutput v).compLp (correction ε hε h hne v f) := by
    change (modulateOutput v).compLpL 2 angleMeasure (y+correction ε hε h hne v f)-
      (modulateOutput v).compLpL 2 angleMeasure y = _
    rw [map_add,add_sub_cancel_left]
    rfl
  rw [he,modulateLp_norm]
  exact correction_bound ε hε h hne v f

theorem kinetic_energy_response (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (v : ℝ) (f : Hilbert) (y : OutputSpace) :
    |‖transformed ε hε h hne v f y‖^2-‖y‖^2| ≤
      (|h| *responseConstant ε v*‖f‖)*(2*‖y‖+|h| *responseConstant ε v*‖f‖) := by
  let δ := |h| *responseConstant ε v*‖f‖
  have hd : 0 ≤ δ := mul_nonneg (mul_nonneg (abs_nonneg _) (responseConstant_nonneg _ _)) (norm_nonneg _)
  have habs : |‖transformed ε hε h hne v f y‖-‖y‖| ≤ δ := by
    rw [← modulateLp_norm v y]
    exact (abs_norm_sub_norm_le _ _).trans (transformed_correction_bound ε hε h hne v f y)
  have hup := (abs_le.mp habs).2
  have hsum : |‖transformed ε hε h hne v f y‖+‖y‖| ≤ 2*‖y‖+δ := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  rw [sq_sub_sq,abs_mul,mul_comm]
  exact mul_le_mul habs hsum (abs_nonneg _) hd

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε) (hne : h ≠ 0)
  (m g k t : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hh m g k t
local notation "J" => embedding ε hε h hh hne m g k t
local notation "A" => energyOutput ε hε h hh hne m g k t
local notation "L" => sectionMap ε hε h hh hne m g k t

theorem full_averaged_graph (u : AveragedSpace ε hε h hh hne m g k t) :
    AveragedGraph ε h hne t (J u) ((select.compLpL 2 angleMeasure) (A u)) := by
  filter_upwards [orbit_lift_ae ε hε h hh hne m g k t u,
    select.coeFn_compLp (A u),
    (KFCausalClosedGraphForm.energyOutput B).coeFn_compLp (L u)] with θ ho hs ha
  change A u θ = KFCausalClosedGraphForm.energyOutput B (L u θ) at ha
  have hg := full_graph ε hε h hh m g k t _ _ (L u θ).property
  exact (congrArg₂ (fun (f : Hilbert) (y : Outputs) => (f,y) ∈ graph ε h t)
    ho (hs.trans (congrArg select ha)).symm).mp hg

theorem selected_output_bound (u : AveragedSpace ε hε h hh hne m g k t) :
    ‖(select.compLpL 2 angleMeasure) (A u)‖ ≤ ‖A u‖ := by
  have hop : ‖select‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun y => by simpa only [one_mul] using select_norm y)
  exact (select.norm_compLp_le _).trans ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (one_mul _))

theorem averaged_graph_unique (hbar : ℝ) (hn : hbar ≠ 0) (f : Hilbert)
    (x y : OutputSpace) (hx : AveragedGraph ε hbar hn t f x)
    (hy : AveragedGraph ε hbar hn t f y) : x = y := by
  apply Lp.ext
  filter_upwards [hx,hy] with θ hxθ hyθ
  apply PiLp.ext
  intro i
  exact (factor ε hbar i).mem_graph_snd_inj' (hxθ i) (hyθ i) rfl

#print axioms averaged_graph_unique
#print axioms modulateLp_norm
#print axioms correction_bound
#print axioms averaged_graph_action
#print axioms transformed_correction_bound
#print axioms kinetic_energy_response
#print axioms full_averaged_graph
#print axioms selected_output_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics
