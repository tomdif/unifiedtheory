/- Uniform graph-output control and weighted vacuum detection along every
finite-energy physical trajectory, retaining the complete charge orbit. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumDetection
import UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_energy_bound)
open UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph
open UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumDetection
open UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget (dissipation)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "E" => timeEnergy ε hε h hne hb m g k
local notation "v" => vacuum ε hε h hne hb m g k 0

theorem vacuum_square_bound (s t : ℝ) (hst : s ≤ t) (w : V) :
    ‖v (F s t w)‖^2 ≤ Real.exp (-2*s)*E s w := by
  have he := formFlow_energy_bound ε hε h hne hb m g k s t w
  rw [abs_of_nonneg (sub_nonneg.mpr hst)] at he
  have hx : Real.exp (2*(t-s)) = Real.exp (2*t)*Real.exp (-2*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hx] at he
  have hv := pow_le_pow_left₀ (norm_nonneg _)
    (vacuum_norm_bound ε hε h hne hb m g k (F s t w)) 2
  have hg : Real.exp (2*t)*‖growingPart ε hε h hne hb m g k (F s t w)‖^2 ≤
      Real.exp (2*t)*(Real.exp (-2*s)*E s w) := by
    have hl : Real.exp (2*t)*‖growingPart ε hε h hne hb m g k (F s t w)‖^2 ≤ E t (F s t w) := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    simpa only [mul_assoc] using hl.trans he
  exact hv.trans ((mul_le_mul_iff_right₀ (Real.exp_pos (2*t))).mp hg)

theorem weighted_detection_bound (s t : ℝ) (w : V) :
    Real.exp (2*t)*detection ε hε (v (F s t w)) ≤
      dissipation ε hε h hne hb m g k s t w := by
  let y := F s t w
  let u := formTransfer ε hε h hne hb m g k 0 t y
  have hd : detection ε hε (vacuum ε hε h hne hb m g k t u) ≤
      dissipation ε hε h hne hb m g k s t w :=
    output_detection_bound ε hε (energyOutput ε hε h hne hb m g k t u)
  have he := vacuum_scaling ε hε h hne hb m g k t y
  have hc : ‖(Real.exp t:ℂ)‖^2 = Real.exp (2*t) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t),← Real.exp_nat_mul]
    norm_num
  have hs : detection ε hε (vacuum ε hε h hne hb m g k t u) =
      Real.exp (2*t)*detection ε hε (v y) :=
    (congrArg (detection ε hε) he).trans
      ((detection_smul ε hε (Real.exp t:ℂ) (v y)).trans
        (congrArg (fun c : ℝ => c*detection ε hε (v y)) hc))
  exact hs.symm.le.trans hd

#print axioms vacuum_square_bound
#print axioms weighted_detection_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumBounds
