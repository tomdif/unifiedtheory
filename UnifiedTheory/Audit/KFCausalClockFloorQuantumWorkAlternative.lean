/- Energy divergence gives a precise alternative on the actual quantum
flow: divergent mean chart clock or divergent accumulated transverse work.
The second branch is not excluded. Mean-clock divergence alone would not
establish probability escape or decay of the clock defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorEnergyClockWork
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumWorkAlternative
noncomputable section
open Filter MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance (energy)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyGrowth (energy_lower energy_tendsto_atTop)
open UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest (chartMoment chart_monotone)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyClockWork

theorem monotone_tail_bounded_or_tendsto (s : ℝ) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ici s)) :
    (∃ B : ℝ, ∀ t, s ≤ t → f t ≤ B) ∨ Tendsto f atTop atTop := by
  by_cases hb : ∃ B : ℝ, ∀ t, s ≤ t → f t ≤ B
  · exact Or.inl hb
  · right
    have hu (B : ℝ) : ∃ t, s ≤ t ∧ B ≤ f t := by
      by_contra! hn
      exact hb ⟨B,fun t ht => (hn t ht).le⟩
    apply tendsto_atTop_atTop.mpr
    intro B
    obtain ⟨t,ht,hB⟩ := hu B
    exact ⟨t,fun u htu => hB.trans (hf ht (ht.trans htu) htu)⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "E" => energy ε hε h hne hh m g k
local notation "Q" => chartMoment ε hε h hne hh m g k
local notation "K" => kineticEnergy ε hε h hne hh m g k
local notation "C" => correctedEnergy ε hε h hne hh m g k

def transverseWork (s t : ℝ) (w : V) : ℝ := ∫ u in s..t, K s u w
local notation "W" => transverseWork ε hε h hne hh m g k

theorem work_lower_if_chart_bounded (s t B : ℝ) (ht : s ≤ t) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w)))
    (hB : Q s t w ≤ B) :
    (Real.sqrt (|h|/8)*Real.exp (t/2)*‖J w‖^2-C s s w-2*B)/2 ≤ W s t w := by
  have hb := corrected_energy_integral ε hε h hne hh m g k s s t le_rfl ht w hw
  have he := energy_lower ε hε h hne hh m g k s t w
  change 2*W s t w = E s t w-2*Q s t w-C s s w at hb
  linarith only [hb,he,hB]

theorem work_tendsto_if_chart_bounded (s B : ℝ) (w : V) (hneW : J w ≠ 0)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w)))
    (hB : ∀ t, s ≤ t → Q s t w ≤ B) :
    Tendsto (fun t => W s t w) atTop atTop := by
  have he := energy_tendsto_atTop ε hε h hne hh m g k s w hneW
  have hl : Tendsto (fun t => (E s t w-C s s w-2*B)/2) atTop atTop := by
    simp only [sub_eq_add_neg]
    exact ((he.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_ge_atTop s] with t ht
  have hb := corrected_energy_integral ε hε h hne hh m g k s s t le_rfl ht w hw
  change 2*W s t w = E s t w-2*Q s t w-C s s w at hb
  linarith only [hb,hB t ht]

theorem chart_tendsto_if_work_bounded (s B : ℝ) (w : V) (hneW : J w ≠ 0)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w)))
    (hB : ∀ t, s ≤ t → W s t w ≤ B) :
    Tendsto (fun t => Q s t w) atTop atTop := by
  have he := energy_tendsto_atTop ε hε h hne hh m g k s w hneW
  have hl : Tendsto (fun t => (E s t w-C s s w-2*B)/2) atTop atTop := by
    simp only [sub_eq_add_neg]
    exact ((he.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_ge_atTop s] with t ht
  have hb := corrected_energy_integral ε hε h hne hh m g k s s t le_rfl ht w hw
  change 2*W s t w = E s t w-2*Q s t w-C s s w at hb
  linarith only [hb,hB t ht]

theorem chart_or_work_tendsto_atTop (s : ℝ) (w : V) (hneW : J w ≠ 0)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    Tendsto (fun t => Q s t w) atTop atTop ∨ Tendsto (fun t => W s t w) atTop atTop := by
  rcases monotone_tail_bounded_or_tendsto s (fun t => Q s t w)
    (chart_monotone ε hε h hne hh m g k s w hw) with ⟨B,hB⟩ | hQ
  · exact Or.inr (work_tendsto_if_chart_bounded ε hε h hne hh m g k s B w hneW hw hB)
  · exact Or.inl hQ

#print axioms monotone_tail_bounded_or_tendsto
#print axioms work_lower_if_chart_bounded
#print axioms work_tendsto_if_chart_bounded
#print axioms chart_tendsto_if_work_bounded
#print axioms chart_or_work_tendsto_atTop
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumWorkAlternative
