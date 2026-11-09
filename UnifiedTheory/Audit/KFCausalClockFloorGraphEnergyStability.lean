/- Uniform energy estimates for the auxiliary equation determining the
generator output. The new correction is bounded on each admissible interval. -/
import UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
import UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
import UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorGraphEnergyStability
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "F'" => referenceFormDerivative ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "D" => graphCorrection ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "θ" => coordinateRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k

def correctionRate (a lam s t : ℝ) : ℝ :=
  ‖F a t‖*‖(S a s t*(-D a lam s t))*S a t s‖/KFCausalShiftedForm.lowerConstant a t
def graphEnergyRate (a lam s t : ℝ) : ℝ := ρ a s t+2*correctionRate ε hε h hne hh m g k a lam s t

theorem correction_rate_nonnegative (a lam s t : ℝ) (ha : 0 < a) :
    0 ≤ correctionRate ε hε h hne hh m g k a lam s t :=
  div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (KFCausalShiftedForm.lowerConstant_positive a t ha).le

theorem base_rate_le_graph_rate (a lam s t : ℝ) (ha : 0 < a) :
    ρ a s t ≤ graphEnergyRate ε hε h hne hh m g k a lam s t :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (correction_rate_nonnegative ε hε h hne hh m g k a lam s t ha))

theorem negative_correction_bound (a lam s t : ℝ) (ha : 0 < a) (x : V) :
    (inner ℂ (S a s t x) (F a t (S a s t ((-D a lam s t) x)))).re ≤
      correctionRate ε hε h hne hh m g k a lam s t*energy (F a t) (S a s t x) :=
  KFCausalTransportedEnergyForm.bounded_transported_output (F a t) (S a s t) (S a t s)
    (S a s t*(-D a lam s t)) (KFCausalShiftedForm.lowerConstant a t)
    (KFCausalShiftedForm.lowerConstant_positive a t ha)
    (transport_inverse ε hε h hne hh m g k a t s ha)
    (shift_energy_coercive ε hε h hne hh m g k a t) x

theorem correction_rate_continuousOn (a lam s : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ContinuousOn (correctionRate ε hε h hne hh m g k a lam s) {t | q a s t < lam} := by
  obtain ⟨hf,hs,hu,_,_⟩ := coefficient_continuity ε hε h hne hh m g k a s ha
  have hd := graph_correction_continuousOn ε hε h hne hh m g k a lam s ha hlam
  have hd₀ : Continuous (KFCausalShiftedForm.lowerConstant a) :=
    continuous_const.min (continuous_const.min (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  exact (hf.continuousOn.norm.mul (((hs.continuousOn.mul hd.neg).mul hu.continuousOn).norm)).div hd₀.continuousOn
    (fun t _ => ne_of_gt (KFCausalShiftedForm.lowerConstant_positive a t ha))

theorem graph_energy_rate_continuousOn (a lam s : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ContinuousOn (graphEnergyRate ε hε h hne hh m g k a lam s) {t | q a s t < lam} :=
  (energy_rate_continuous ε hε h hne hh m g k a s ha).continuousOn.add
    (continuousOn_const.mul (correction_rate_continuousOn ε hε h hne hh m g k a lam s ha hlam))

theorem auxiliary_energy_growth (a lam b s κ l r : ℝ) (ha : 0 < a) (hb : 0 < b) (hlr : l ≤ r)
    (hparams : ∀ t ∈ Icc l r, q a s t < b ∧ 2*ω a s t ≤ b ∧
      graphEnergyRate ε hε h hne hh m g k a lam s t ≤ κ)
    (z : ℝ → V) (hc : ContinuousOn z (Icc l r))
    (hz : ∀ t ∈ Ioo l r, HasDerivAt z ((A a b s t-D a lam s t) (z t)) t) :
    energy (F a r) (S a s r (z r)) ≤ Real.exp (κ*(r-l))*energy (F a l) (S a s l (z l)) := by
  have hcont := coefficient_continuity ε hε h hne hh m g k a s ha
  exact KFCausalTransportedPerturbedGrowth.perturbed_growth (F a) F' (S a s) (S' a s)
    (A a b s) (D a lam s) (θ a s) (ω a s) (correctionRate ε hε h hne hh m g k a lam s)
    κ l r hlr hcont.1 hcont.2.1
    (fun t => KFCausalMassResolventStability.shift_symmetric M (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)
    (referenceShift_derivative ε hε h hne hh m g k a)
    (fun t => transport_derivative ε hε h hne hh m g k a s t ha)
    (fun t _ x => KFCausalClockFloorLiftedEnergyStability.form_derivative_bound ε hε h hne hh m g k
      a t ha.le (S a s t x))
    (fun t _ x => coordinate_derivative_bound ε hε h hne hh m g k a s t ha x)
    (fun t ht x => full_transported_bound ε hε h hne hh m g k a b s t ha hb
      (hparams t ht).1 (hparams t ht).2.1 x)
    (fun t _ x => negative_correction_bound ε hε h hne hh m g k a lam s t ha x)
    (fun t _ x => shift_energy_nonnegative ε hε h hne hh m g k a t ha (S a s t x))
    (fun t ht => (hparams t ht).2.2) z hc hz

theorem uniform_auxiliary_parameters (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q a s t < b ∧ 2*ω a s t ≤ b ∧ graphEnergyRate ε hε h hne hh m g k a lam s t ≤ κ :=
  KFCausalTransportedPerturbedGrowth.compact_rates (q a s) (ω a s)
    (graphEnergyRate ε hε h hne hh m g k a lam s) l r
    (threshold_continuous ε hε h hne hh m g k a s ha).continuousOn
    (quasi_rate_continuous ε hε h hne hh m g k a s ha).continuousOn
    ((graph_energy_rate_continuousOn ε hε h hne hh m g k a lam s ha hlam).mono hadm)

#print axioms correction_rate_nonnegative
#print axioms base_rate_le_graph_rate
#print axioms negative_correction_bound
#print axioms correction_rate_continuousOn
#print axioms graph_energy_rate_continuousOn
#print axioms auxiliary_energy_growth
#print axioms uniform_auxiliary_parameters
end
end UnifiedTheory.Audit.KFCausalClockFloorGraphEnergyStability
