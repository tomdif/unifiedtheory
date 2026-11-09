/- The actual two-radial-width packet is a scalar multiple of two
unitary squeeze transports of an isotropic sourced polynomial packet.
This exact identity leaves the physical operators and neutral width fixed. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueezeCoordinates
import UnifiedTheory.Audit.KFCausalIndependentRadialPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueeze
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalIndependentRadialPacketProfiles (prefactor configurationProfile)
open KFCausalIndependentRadialPackets (state clock state_configuration_coe)

def reciprocalParameter (wL wR : ℝ) : ℝ := (Real.log wL+Real.log wR)/4
def pairedParameter (wL wR : ℝ) : ℝ := (Real.log wR-Real.log wL)/4
def neutralParameter (wL wR : ℝ) : ℝ := reciprocalParameter wL wR+pairedParameter wL wR

theorem neutralParameter_eq (wL wR : ℝ) : neutralParameter wL wR=Real.log wR/2 := by
  unfold neutralParameter reciprocalParameter pairedParameter
  ring

theorem parameter_widths (wL wR : ℝ) (hL : 0 < wL) (hR : 0 < wR) :
    Real.exp (2*(reciprocalParameter wL wR-pairedParameter wL wR))=wL ∧
      Real.exp (2*(reciprocalParameter wL wR+pairedParameter wL wR))=wR := by
  unfold reciprocalParameter pairedParameter
  constructor
  · rw [show 2*((Real.log wL+Real.log wR)/4-(Real.log wR-Real.log wL)/4)=Real.log wL by ring]
    exact Real.exp_log hL
  · rw [show 2*((Real.log wL+Real.log wR)/4+(Real.log wR-Real.log wL)/4)=Real.log wR by ring]
    exact Real.exp_log hR

def seedWidth (h wL wR : ℝ) : ℝ :=
  KFCausalReciprocalGaussianDomain.baseWidth h (neutralParameter wL wR)

theorem seedWidth_eq (h wL wR : ℝ) (hR : 0 < wR) : seedWidth h wL wR=neutralWidth h/wR := by
  rw [seedWidth,KFCausalReciprocalGaussianDomain.baseWidth,neutralParameter_eq]
  rw [show -2*(Real.log wR/2)= -(Real.log wR) by ring,Real.exp_neg,Real.exp_log hR]
  rfl

theorem seedWidth_positive (h wL wR : ℝ) (hh : h ≠ 0) : 0 < seedWidth h wL wR :=
  KFCausalReciprocalGaussianDomain.baseWidth_positive h hh _

theorem seedWidth_bound (h wL wR : ℝ) (hh : h ≠ 0) (hR : 1 ≤ wR) :
    32*seedWidth h wL wR ≤ groundWidth h := by
  apply KFCausalReciprocalGaussianDomain.baseWidth_bound h hh
  rw [neutralParameter_eq]
  exact div_nonneg (Real.log_nonneg hR) (by norm_num)

def normalization (wL wR : ℝ) : ℝ :=
  prefactor wL wR*Real.exp (-(neutralParameter wL wR)/2)

def seed (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hR : 1 ≤ wR) : Hilbert :=
  KFCausalVariableWidthPolynomialDomain.input ε a (groundWidth h) (seedWidth h wL wR)
    hε ha (groundWidth_positive h hh) (seedWidth_positive h wL wR hh)
    (seedWidth_bound h wL wR hh hR) C p
    (neutralSource ((Real.exp (-(neutralParameter wL wR)):ℂ)*b)) 4
    (rescaledPolynomial (neutralParameter wL wR) P)

theorem state_transport (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) :
    state ε a h wL wR C p b P hε ha hh hL hR =
      (normalization wL wR:ℂ) •
        KFCausalPairedSqueezeTransport.transport (-(pairedParameter wL wR))
          (KFCausalReciprocalSqueezeTransport.transport (-(reciprocalParameter wL wR))
            (seed ε a h wL wR C p b P hε ha hh hR)) := by
  let t := reciprocalParameter wL wR
  let s := pairedParameter wL wR
  let f := seed ε a h wL wR C p b P hε ha hh hR
  let u := KFCausalReciprocalSqueezeTransport.transport (-t) f
  have hf := KFCausalVariableWidthPolynomialDomain.input_coe ε a (groundWidth h) (seedWidth h wL wR)
    hε ha (groundWidth_positive h hh) (seedWidth_positive h wL wR hh)
    (seedWidth_bound h wL wR hh hR) C p
    (neutralSource ((Real.exp (-(neutralParameter wL wR)):ℂ)*b)) 4
    (rescaledPolynomial (neutralParameter wL wR) P)
  change f =ᵐ[volume] _ at hf
  have hfu := (KFCausalReciprocalSqueezeTransport.squeezeFlow_quasiMeasurePreserving (-t)).ae hf
  have hfv := (KFCausalPairedSqueezeTransport.squeezeFlow_quasiMeasurePreserving (-s)).ae hfu
  have huv := (KFCausalPairedSqueezeTransport.squeezeFlow_quasiMeasurePreserving (-s)).ae
    (KFCausalReciprocalSqueezeTransport.transport_coe (-t) f)
  apply Lp.ext
  filter_upwards [state_configuration_coe ε a h wL wR C p b P hε ha hh hL hR,
    Lp.coeFn_smul (normalization wL wR:ℂ) (KFCausalPairedSqueezeTransport.transport (-s) u),
    KFCausalPairedSqueezeTransport.transport_coe (-s) u,huv,hfv] with x hx hc hv hu hf
  change _=((normalization wL wR:ℂ) • KFCausalPairedSqueezeTransport.transport (-s) u) x
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hv]
  change u (KFCausalPairedSqueezeTransport.squeezeFlow (-s) x)=_ at hu
  rw [hu]
  change f (KFCausalReciprocalSqueezeTransport.squeezeFlow (-t)
    (KFCausalPairedSqueezeTransport.squeezeFlow (-s) x))=_ at hf
  rw [hf]
  simp only [KFCausalReciprocalSqueezeTransport.squeezeFlow_apply,
    KFCausalPairedSqueezeTransport.squeezeFlow_apply,neg_neg]
  have hn : (normalization wL wR:ℂ)*((Real.exp (s/2):ℂ)*(Real.exp (t/2):ℂ))=(prefactor wL wR:ℂ) := by
    have he : normalization wL wR*(Real.exp (s/2)*Real.exp (t/2))=prefactor wL wR := by
      unfold normalization
      rw [mul_assoc,← Real.exp_add,← Real.exp_add]
      rw [show -(neutralParameter wL wR)/2+(s/2+t/2)=0 by dsimp [neutralParameter,t,s]; ring,
        Real.exp_zero,mul_one]
    exact_mod_cast he
  have he := KFCausalIndependentRadialDoubleSqueezeCoordinates.profile_transport
    (groundWidth h) (neutralWidth h) t s C p b P
    (KFCausalClockFloorInvariantTrial.clockFunction ε a) x
  obtain ⟨hleft,hright⟩ := parameter_widths wL wR (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR)
  change Real.exp (2*(t-s))=wL at hleft
  change Real.exp (2*(t+s))=wR at hright
  rw [hleft,hright] at he
  change configurationProfile _ _ _ _ _ _ _ _ =
    (normalization wL wR:ℂ)*((Real.exp (s/2):ℂ)*((Real.exp (t/2):ℂ)*_))
  rw [← mul_assoc (Real.exp (s/2):ℂ),← mul_assoc,hn]
  exact he.symm

#print axioms neutralParameter_eq
#print axioms parameter_widths
#print axioms seedWidth_eq
#print axioms seedWidth_positive
#print axioms seedWidth_bound
#print axioms state_transport
end
end UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueeze
