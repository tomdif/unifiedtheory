/- The actual growing group inherits forward clock-defect monotonicity
from the proved local limit of the full dynamics. Decay is not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorLateTimeAutonomy
import UnifiedTheory.Audit.KFCausalClockFloorResidualDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingDefect
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorGrowingEvolution (evolution evolution_compose)
open KFCausalClockFloorDefectOperator (defectOperator)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "G" => evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε

theorem defect_le_initial (t : ℝ) (ht : 0 ≤ t) (f : Hilbert) : ‖D (G t f)‖ ≤ ‖D f‖ := by
  have hl := ((D).continuous.tendsto _).comp
    (KFCausalClockFloorLateTimeAutonomy.strong_limit ε hε h hne hb m g k f t ht)
  apply le_of_tendsto hl.norm
  filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
  exact KFCausalClockFloorDefectMonotonicity.evolution_defect_le_initial ε hε h hne hb m g k
    (physicalTime U) (physicalTime (U+t))
    (div_le_div_of_nonneg_right (Real.log_le_log hU (by linarith)) (by norm_num)) f

theorem defect_antitone (f : Hilbert) : Antitone (fun t => ‖D (G t f)‖) := by
  intro s t hst
  have he := defect_le_initial ε hε h hne hb m g k (t-s) (sub_nonneg.mpr hst) (G s f)
  rw [← evolution_compose,add_sub_cancel] at he
  exact he

def residual (f : Hilbert) : ℝ := ⨅ t : ℝ, ‖D (G t f)‖

theorem residual_limit (f : Hilbert) :
    Tendsto (fun t => ‖D (G t f)‖) atTop (𝓝 (residual ε hε h hne hb m g k f)) :=
  tendsto_atTop_ciInf (defect_antitone ε hε h hne hb m g k f)
    ⟨0,by rintro _ ⟨t,rfl⟩; exact norm_nonneg _⟩

theorem recovery_iff (f : Hilbert) :
    Tendsto (fun t => ‖D (G t f)‖) atTop (𝓝 0) ↔ residual ε hε h hne hb m g k f=0 := by
  constructor
  · exact fun ht => tendsto_nhds_unique (residual_limit ε hε h hne hb m g k f) ht
  · intro hz
    simpa only [hz] using residual_limit ε hε h hne hb m g k f

#print axioms defect_le_initial
#print axioms defect_antitone
#print axioms residual_limit
#print axioms recovery_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingDefect
