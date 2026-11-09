/- Independent real clock phases preserve physical charge zero.
Thus the mixed-clock neutral states and their actual clock momenta
belong to the same zero-charge sector used by the model. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockState
import UnifiedTheory.Audit.KFCausalNeutralFiniteCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles (neutralSource)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState
open UnifiedTheory.Audit.KFCausalClockChargeMultiplier

theorem phase_measurable (p : ℝ) : Measurable (fun s : ℝ => clockPhase p (s:ℂ)) := by
  unfold clockPhase
  fun_prop

theorem phase_bound (p s : ℝ) : ‖clockPhase p (s:ℂ)‖ ≤ 1 := by
  simp [clockPhase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

def phaseOperator (p : ℝ) : Hilbert →L[ℂ] Hilbert :=
  clockMultiplier (fun s : ℝ => clockPhase p (s:ℂ)) (phase_measurable p) (phase_bound p)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

theorem packet_frequency (p : ℝ) (b C : ℂ) (P : Polynomial ℂ) :
    KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C p (neutralSource b) 4 P =
      phaseOperator p
        (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P) := by
  apply Lp.ext
  filter_upwards [
    KFCausalPolynomialGaussianDomain.input_coe ε a h hε ha hh C p (neutralSource b) 4 P,
    KFCausalPolynomialGaussianDomain.input_coe ε a h hε ha hh C 0 (neutralSource b) 4 P,
    clockMultiplier_coe (fun s : ℝ => clockPhase p (s:ℂ)) (phase_measurable p) (phase_bound p)
      (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P)]
    with x hi h0 hm
  change _ = (clockMultiplier _ _ _ _) x
  rw [hi,hm,h0]
  simp only [KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,clockPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  ring

theorem packet_mem_zeroSector (p : ℝ) (b C : ℂ) (P : Polynomial ℂ) :
    KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C p (neutralSource b) 4 P ∈
      zeroSector h hh := by
  rw [packet_frequency]
  have hf := KFCausalNeutralFiniteCharge.packet_mem_zeroSector ε a h hε ha hh b C P
  change ∀ θ, action h hh θ
    (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P) =
    KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P at hf
  change ∀ θ, action h hh θ (phaseOperator p _) = phaseOperator p _
  intro θ
  unfold phaseOperator
  rw [← multiplier_action,hf θ]

omit a ha in
theorem state_mem_zeroSector (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    state ε h hε hh N a p ha b C P ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem fun i _ =>
    packet_mem_zeroSector ε (a i) h hε (ha i) hh (p i) (b i) (C i) (P i)

omit a ha in
theorem momentum_mem_zeroSector (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    momentum ε h hε hh N a p ha b C P ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε h hε hh N a p ha b C P)
    (state_mem_zeroSector ε h hε hh N a p ha b C P)

omit a ha in
theorem state_projection (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    zeroProjection h hh (state ε h hε hh N a p ha b C P) = state ε h hε hh N a p ha b C P :=
  zeroProjection_fixes h hh _ (state_mem_zeroSector ε h hε hh N a p ha b C P)

omit a ha in
theorem state_charge_zero (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    (state ε h hε hh N a p ha b C P,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (state_mem_zeroSector ε h hε hh N a p ha b C P)

#print axioms phase_measurable
#print axioms phase_bound
#print axioms packet_frequency
#print axioms packet_mem_zeroSector
#print axioms state_mem_zeroSector
#print axioms momentum_mem_zeroSector
#print axioms state_projection
#print axioms state_charge_zero
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge
