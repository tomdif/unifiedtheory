/- The enlarged reciprocal/neutral packets have actual zero charge.
They include both previous packet families and the even regular witness
excluded from the reciprocal Gaussian closure. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
import UnifiedTheory.Audit.KFCausalReciprocalClosureObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralCharge
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralPackets
open KFCausalStandingChargeOperator (zeroSector zeroProjection zeroProjection_fixes zeroProjection_mem)
open KFCausalNeutralMixedClockCharge (phaseOperator phase_measurable phase_bound)
open KFCausalClockChargeMultiplier (clockMultiplier_coe multiplier_action)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalUnboundedNeutralCharge (relation relation_projection)
open KFCausalNeutralExponentialProfiles (neutralSource exponentialProfile)
open KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)
open KFCausalChargeGaussianGeometry (groundWidth)

theorem phase_zeroSector (h : ℝ) (hh : h ≠ 0) (p : ℝ) (f : Hilbert)
    (hf : f ∈ zeroSector h hh) : phaseOperator p f ∈ zeroSector h hh := by
  change ∀ θ, KFCausalPhysicalCircleAction.action h hh θ (phaseOperator p f) = phaseOperator p f
  intro θ
  unfold phaseOperator
  rw [← multiplier_action]
  exact congrArg _ (hf θ)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "ψ" => state ε a h w hε ha hh hw C p b P
local notation "g" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)

theorem state_relation :
    relation (fun q : ℝ => exponentialProfile b C P (q:ℂ)) (phaseOperator p g) ψ := by
  filter_upwards [state_coe ε a h w hε ha hh hw C p b P,
    clockMultiplier_coe (fun s : ℝ => clockPhase p (s:ℂ)) (phase_measurable p) (phase_bound p) g,
    KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h w hε ha hh (by linarith)]
    with x hs hp hg
  change phaseOperator p g x = _ at hp
  rw [hs,hp,hg]
  unfold profile exponentialProfile
  ring

theorem state_zeroSector : ψ ∈ zeroSector h hh := by
  have hc : Continuous (fun q : ℝ => exponentialProfile b C P (q:ℂ)) := by
    unfold exponentialProfile
    fun_prop
  have hr := state_relation ε a h w hε ha hh hw C p b P
  have hp := relation_projection _ hc.measurable h hh _ _ hr
  rw [zeroProjection_fixes h hh _
    (phase_zeroSector h hh p g (KFCausalReciprocalGaussianCharge.state_zeroSector ε a h w hε ha hh (by linarith)))] at hp
  have he : zeroProjection h hh ψ = ψ := Lp.ext (hp.trans hr.symm)
  rw [← he]
  exact zeroProjection_mem h hh ψ

theorem momentum_zeroSector : momentum ε a h w hε ha hh hw C p b P ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h w hε ha hh hw C p b P)
    (state_zeroSector ε a h w hε ha hh hw C p b P)

omit C p b P in
theorem constant_eq_reciprocal :
    state ε a h w hε ha hh hw 1 0 0 1 = g := by
  apply Lp.ext
  filter_upwards [state_coe ε a h w hε ha hh hw 1 0 0 1,
    KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h w hε ha hh (by linarith)] with x hs hg
  rw [hs,hg]
  simp [profile,clockPhase]

omit w hw in
theorem one_eq_neutral :
    state ε a h 1 hε ha hh (by norm_num) C p b P =
      KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C p (neutralSource b) 4 P := by
  apply Lp.ext
  filter_upwards [state_coe ε a h 1 hε ha hh (by norm_num) C p b P,
    KFCausalPolynomialGaussianDomain.input_coe ε a h hε ha hh C p (neutralSource b) 4 P] with x hs hp
  rw [hs,hp,neutral_source_profile]
  have hd := KFCausalReciprocalGaussianDomain.profile_squeeze
    (groundWidth h) (neutralWidth h) 0 (clockFunction ε a) x
  simp only [mul_zero,Real.exp_zero,mul_one,KFCausalReciprocalSqueezeFlow.squeeze_initial] at hd
  unfold profile
  rw [← hd]
  ring

omit w hw C p b P in
theorem quadratic_outside_reciprocalClosure :
    state ε a h 1 hε ha hh (by norm_num) 1 0 0 (Polynomial.X^2) ∉
      closure (KFCausalNeutralGaussianConstraint.reciprocalStates ε h hε hh) := by
  rw [one_eq_neutral]
  exact KFCausalReciprocalClosureObstruction.witness_not_reciprocalClosure ε a h hε ha hh

#print axioms phase_zeroSector
#print axioms state_relation
#print axioms state_zeroSector
#print axioms momentum_zeroSector
#print axioms constant_eq_reciprocal
#print axioms one_eq_neutral
#print axioms quadratic_outside_reciprocalClosure
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralCharge
