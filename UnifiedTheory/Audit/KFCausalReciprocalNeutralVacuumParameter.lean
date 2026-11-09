/- The vacuum exponential parameter is independent of the physical
packet widths. Exact input and momentum graphs and representatives keep
those widths fixed while changing only the operator parameter. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile
import UnifiedTheory.Audit.KFCausalVacuumParameterRescale

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumParameter
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial state)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile profile_squeeze)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "τ" => Real.log w/2
local notation "hτ" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h τ
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh τ
local notation "hwidth" => baseWidth_bound h hh τ hτ
local notation "d" => neutralSource ((Real.exp (-τ):ℂ)*b)
local notation "Q" => rescaledPolynomial τ P
local notation "c" => (Real.exp (-τ/2):ℂ)
local notation "S" => state ε a h w hε ha hh hw C p b P

def momentum (k : ℝ) : Hilbert := c • transport (-τ)
  (KFCausalVariableWidthPolynomialMomentum.momentum ε a α β hε ha hα hβ hwidth k p d 4 C Q)

theorem momentum_graph (k : ℝ) (hk : k ≠ 0) :
    (S,momentum ε a h w hε ha hh hw C p b P k) ∈ (pureMomentum ε hε k).graph :=
  (pureMomentum ε hε k).graph.smul_mem c
    (KFCausalReciprocalGaussianMomentum.pure_graph_transport ε hε k hk (-τ) _ _
      (KFCausalVariableWidthPolynomialMomentum.momentum_graph ε a α β hε ha hα hβ hwidth k hk p d 4 C Q))

variable (k : ℝ) (hk : k ≠ 0) (hb : |k| ≤ 2*Real.pi*ε/3)

def output : Hilbert := c • transport (-τ)
  (KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth k C p d 4 hb Q modelDirections pointField 7)

def momentumOutput : Hilbert := c • transport (-τ)
  (KFCausalVariableWidthPolynomialMomentum.momentumFactor ε a α β hε ha hα hβ hwidth k p d 4 C hb Q modelDirections pointField 7)

theorem output_graph : (S,output ε a h w hε ha hh hw C p b P k hb) ∈
    (orderedExponential ε hε k).graph :=
  (orderedExponential ε hε k).graph.smul_mem c
    (KFCausalReciprocalSqueezeExponential.ordered_graph_squeeze ε hε k (-τ) _ _
      (KFCausalVariableWidthPolynomialDomain.output_graph ε a α β hε ha hα hβ hwidth k C p d 4 hb Q modelDirections pointField 7))

include hk in
theorem momentumOutput_graph :
    (momentum ε a h w hε ha hh hw C p b P k,momentumOutput ε a h w hε ha hh hw C p b P k hb) ∈
      (orderedExponential ε hε k).graph :=
  (orderedExponential ε hε k).graph.smul_mem c
    (KFCausalReciprocalSqueezeExponential.ordered_graph_squeeze ε hε k (-τ) _ _
      (KFCausalVariableWidthPolynomialMomentum.momentumFactor_graph ε a α β hε ha hα hβ hwidth k hk p d 4 C hb Q modelDirections pointField 7))

theorem output_coe : output ε a h w hε ha hh hw C p b P k hb =ᵐ[volume]
    shiftedProfile ε a α (neutralWidth h) k w C p b P := by
  let v := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth k C p d 4 hb Q modelDirections pointField 7
  filter_upwards [Lp.coeFn_smul c (transport (-τ) v),transport_coe (-τ) v,
    (squeezeFlow_quasiMeasurePreserving (-τ)).ae
      (KFCausalVariableWidthOrderedProfile.output_vacuum_coe ε a α β hε ha hα hβ hwidth k hb C p d 4 Q modelDirections pointField)] with x hc ht hv
  change v (squeezeFlow (-τ) x) = _ at hv
  change (c • transport (-τ) v) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,ht,hv]
  simp only [squeezeFlow_apply,neg_neg,baseWidth]
  rw [profile_squeeze]
  have he : Real.exp (2*τ) = w := by
    rw [show 2*τ=Real.log w by ring,Real.exp_log (by linarith)]
  rw [he,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,
    show -τ/2+τ/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]

include hk in
theorem momentum_relation : KFCausalUnboundedMultiplierIntegral.relation (clockSlope ε a k p)
    (output ε a h w hε ha hh hw C p b P k hb)
    (momentumOutput ε a h w hε ha hh hw C p b P k hb) := by
  let u := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth k C p d 4 hb Q modelDirections pointField 7
  let v := KFCausalVariableWidthPolynomialMomentum.momentumFactor ε a α β hε ha hα hβ hwidth k p d 4 C hb Q modelDirections pointField 7
  have hr := KFCausalVariableWidthOrderedMomentum.polynomial_relation ε a α β hε ha hα hβ hwidth k hk hb C p d 4 Q modelDirections pointField 0
  filter_upwards [Lp.coeFn_smul c (transport (-τ) u),Lp.coeFn_smul c (transport (-τ) v),
    transport_coe (-τ) u,transport_coe (-τ) v,
    (squeezeFlow_quasiMeasurePreserving (-τ)).ae hr] with x hu hv htu htv hr
  change v (squeezeFlow (-τ) x) = clockSlope ε a k p (squeezeFlow (-τ) x)*u (squeezeFlow (-τ) x) at hr
  change (c • transport (-τ) v) x = clockSlope ε a k p x*(c • transport (-τ) u) x
  rw [hv,hu]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [htu,htv,hr]
  simp only [clockSlope,squeezeFlow_apply]
  ring

include hk in
theorem momentumOutput_coe : momentumOutput ε a h w hε ha hh hw C p b P k hb =ᵐ[volume]
    fun x => clockSlope ε a k p x*shiftedProfile ε a α (neutralWidth h) k w C p b P x := by
  filter_upwards [momentum_relation ε a h w hε ha hh hw C p b P k hk hb,
    output_coe ε a h w hε ha hh hw C p b P k hb] with x hm hu
  rw [hm,hu]

#print axioms momentum_graph
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms output_coe
#print axioms momentum_relation
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumParameter
