/- At a fixed time, normalized zero-charge states in one bounded energy
window have the same positive defect expectation but arbitrarily small
exact defect-decay rate and classical-output dissipation. This excludes
a state-uniform instantaneous coercivity estimate on that window. It
does not exclude clock recovery along any fixed actual trajectory. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyClockRate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectCoercivityObstruction
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
open UnifiedTheory.Audit.KFCausalNegativeFrequencyClockRate
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (input)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (projectedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget
  (dissipation dissipation_nonnegative dissipation_rate_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector zeroProjection_mem zeroProjection_fixes)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hp : 0 < h)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "hh" => hp.ne'
local notation "V" => FormSpace ε hε h hh hb m g k 0
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "D" => defectOperator ε hε
local notation "w" p:arg => packetForm ε a h hε ha hp hb m g k t p
local notation "f" p:arg => input ε h hε hh (structured a h p ha)
local notation "E" p:arg => projectedEnergy ε h hε hh hb (structured a h p ha) m g k t
local notation "R" => exactRate ε hε h hh hb m g k t t
local notation "d" => Complex.re (inner ℂ (f 0) (D (f 0)))

theorem packet_energy (p : ℝ) : timeEnergy ε hε h hh hb m g k t (w p) = E p := by
  rw [← timeEnergy_actual,packetForm,transfer_inverse]
  rfl

theorem dissipation_tendsto_zero :
    Tendsto (fun n : ℕ => dissipation ε hε h hh hb m g k t t (w (-(n:ℝ))))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n : ℕ => dissipation_nonnegative ε hε h hh hb m g k t t (w (-(n:ℝ))))
    (fun n : ℕ => show dissipation ε hε h hh hb m g k t t (w (-(n:ℝ))) ≤
      (-32)*R (w (-(n:ℝ))) by
      linarith [dissipation_rate_bound ε hε h hh hb m g k t t (w (-(n:ℝ)))])
  simpa only [mul_zero] using (exact_rate_tendsto_zero ε a h hε ha hp hb m g k t).const_mul (-32)

theorem bounded_energy_small_rate (η : ℝ) (hη : 0 < η) :
    ∃ v : V, ‖J v‖ = 1 ∧ J v ∈ zeroSector h hh ∧
      timeEnergy ε hε h hh hb m g k t v ≤ E 0 ∧
      (inner ℂ (J v) (D (J v))).re = d ∧ |R v| < η := by
  have hz := (exact_rate_tendsto_zero ε a h hε ha hp hb m g k t).abs
  have he : ∀ᶠ n : ℕ in atTop, |R (w (-(n:ℝ)))| < η := by
    exact (tendsto_order.mp (by simpa only [abs_zero] using hz)).2 η hη
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨w (-(n:ℝ)),?_,?_,?_,?_,hn⟩
  · rw [packet_embedding,input_norm]
  · rw [packet_embedding]
    have hz := zeroProjection_mem h hh (f (-(n:ℝ)))
    rwa [zeroProjection_fixes h hh _ (input_fixed ε a h hε ha hh _)] at hz
  · rw [packet_energy]
    exact energy_le ε a h hε ha hh hb hp _ (neg_nonpos.mpr (Nat.cast_nonneg n)) m g k t
  · rw [packet_embedding]
    exact packet_defect_constant ε a h hε ha hp (-(n:ℝ))

theorem no_positive_error_only_rate (Φ : ℝ → ℝ) (hΦ : 0 < Φ d) :
    ¬ ∀ v : V, ‖J v‖ = 1 → J v ∈ zeroSector h hh →
      timeEnergy ε hε h hh hb m g k t v ≤ E 0 →
      Φ ((inner ℂ (J v) (D (J v))).re) ≤ -R v := by
  intro hbound
  obtain ⟨v,hn,hq,he,hdef,hr⟩ := bounded_energy_small_rate ε a h hε ha hp hb m g k t
    (Φ d) hΦ
  have hl := hbound v hn hq he
  rw [hdef] at hl
  exact (not_lt_of_ge (hl.trans (neg_le_abs _))) hr

theorem no_uniform_rate_coercivity :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : V, ‖J v‖ = 1 → J v ∈ zeroSector h hh →
      timeEnergy ε hε h hh hb m g k t v ≤ E 0 →
      c*(inner ℂ (J v) (D (J v))).re ≤ -R v := by
  rintro ⟨c,hc,hbound⟩
  have hd := packet_defect_positive ε a h hε ha hp
  exact no_positive_error_only_rate ε a h hε ha hp hb m g k t (fun x => c*x)
    (mul_pos hc hd) hbound

theorem no_uniform_dissipation_coercivity :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : V, ‖J v‖ = 1 → J v ∈ zeroSector h hh →
      timeEnergy ε hε h hh hb m g k t v ≤ E 0 →
      c*(inner ℂ (J v) (D (J v))).re ≤ dissipation ε hε h hh hb m g k t t v := by
  rintro ⟨c,hc,hbound⟩
  apply no_uniform_rate_coercivity ε a h hε ha hp hb m g k t
  refine ⟨c/32,by positivity,?_⟩
  intro v hn hq he
  have hl := hbound v hn hq he
  have hr := dissipation_rate_bound ε hε h hh hb m g k t t v
  linarith

#print axioms packet_energy
#print axioms dissipation_tendsto_zero
#print axioms bounded_energy_small_rate
#print axioms no_positive_error_only_rate
#print axioms no_uniform_rate_coercivity
#print axioms no_uniform_dissipation_coercivity
end
end UnifiedTheory.Audit.KFCausalClockFloorDefectCoercivityObstruction
