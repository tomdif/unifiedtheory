/- The actual dissipation budget has uniformly vanishing tails.
The limiting clock-defect expectation need not be zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDissipationTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "e" => expectation ε hε h hne hb m g k
local notation "d" => dissipation ε hε h hne hb m g k

theorem expectation_tendsto_infimum (s : ℝ) (w : V) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ ≤ e s t w) ∧
      Tendsto (fun t => e s t w) atTop (𝓝 ℓ) := by
  have ha : Antitone (fun t => e s t w) := by
    intro a b hab
    have hi := interval_budget ε hε h hne hb m g k s a b hab w
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
      (fun t => dissipation_nonnegative ε hε h hne hb m g k s t w)
    linarith
  have h0 (t : ℝ) := expectation_nonnegative ε hε h hne hb m g k s t w
  have hbd : BddBelow (Set.range (fun t => e s t w)) :=
    ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  exact ⟨⨅ t, e s t w,le_ciInf h0,fun t => ciInf_le hbd t,tendsto_atTop_ciInf ha hbd⟩

theorem tail_budget (s : ℝ) (w : V) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ a b, R ≤ a → a ≤ b → (∫ t in a..b, d s t w) < η := by
  obtain ⟨ℓ,_,hl,ht⟩ := expectation_tendsto_infimum ε hε h hne hb m g k s w
  have hz : Tendsto (fun t => 32*(e s t w-ℓ)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using (ht.sub_const ℓ).const_mul 32
  have he : ∀ᶠ t : ℝ in atTop, 32*(e s t w-ℓ) < η :=
    (tendsto_order.mp hz).2 η hη
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨R,?_⟩
  intro a b ha hab
  have hi := interval_budget ε hε h hne hb m g k s a b hab w
  have hb' := hl b
  have ha' := hR a ha
  linarith

#print axioms expectation_tendsto_infimum
#print axioms tail_budget
end
end UnifiedTheory.Audit.KFCausalClockFloorDissipationTail
