/- Every nonzero finite-energy solution of the actual full quantum dynamics
has energy tending to infinity. This is an energy conclusion, and does not
identify which coordinate escapes or prove decay of the clock defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorUncertaintyEnergy
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyGrowth
noncomputable section
open Filter
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance

theorem scalar_energy_lower (H N t E : ℝ) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hb : H*Real.exp t*N^4 ≤ 8*E^2) :
    Real.sqrt (H/8)*Real.exp (t/2)*N^2 ≤ E := by
  have hs : (Real.sqrt (H/8))^2 = H/8 := Real.sq_sqrt (by positivity)
  have he : (Real.exp (t/2))^2 = Real.exp t := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (by positivity) hE).mp
  rw [mul_pow,mul_pow,hs,he]
  nlinarith only [hb]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k

theorem energy_lower (s t : ℝ) (w : V) :
    Real.sqrt (|h|/8)*Real.exp (t/2)*‖J w‖^2 ≤ energy ε hε h hne hh m g k s t w := by
  have hb := (KFCausalClockFloorUncertaintyEnergy.reference_uncertainty_energy
    ε hε h hne hh m g k t (F s t w)).2
  rw [formFlow_physical_norm] at hb
  exact scalar_energy_lower |h| ‖J w‖ t _ (abs_nonneg h)
    (timeEnergy_nonneg ε hε h hne hh m g k t (F s t w)) hb

theorem energy_tendsto_atTop (s : ℝ) (w : V) (hw : J w ≠ 0) :
    Tendsto (fun t => energy ε hε h hne hh m g k s t w) atTop atTop := by
  have hc : 0 < Real.sqrt (|h|/8)*‖J w‖^2 :=
    mul_pos (Real.sqrt_pos.mpr (div_pos (abs_pos.mpr hne) (by norm_num)))
      (sq_pos_of_pos (norm_pos_iff.mpr hw))
  have he : Tendsto (fun t : ℝ => Real.exp (t/2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))
  have hl := he.const_mul_atTop hc
  apply tendsto_atTop_mono _ hl
  intro t
  calc
    (Real.sqrt (|h|/8)*‖J w‖^2)*Real.exp (t/2) =
        Real.sqrt (|h|/8)*Real.exp (t/2)*‖J w‖^2 := by ring
    _ ≤ _ := energy_lower ε hε h hne hh m g k s t w

#print axioms scalar_energy_lower
#print axioms energy_lower
#print axioms energy_tendsto_atTop
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyGrowth
