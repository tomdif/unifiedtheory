/- Actual physical sourced packets with independently variable charge-
radial widths. The diagonal is the original reciprocal neutral packet.
This source proves state and charge identities, not Hamiltonian domains. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketProfiles
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPackets
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Joint split coordinates_coe split_preserves_volume)
open KFCausalEuclideanConfiguration (euclideanPullback euclideanPullback_coe)
open KFCausalPhysicalMixedCoordinates (pairedState pairedState_position_coe mixedCoordinates mixedCoordinates_functions_coe)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable)
open KFCausalIndependentRadialPacketProfiles
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous clockFunction_memLp
  neutralWidth neutralWidth_positive)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flow_preserves_volume)
open KFCausalStandingChargeOperator (zeroSector)

section Generic
variable (α β wL wR : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def genericState : Hilbert := (prefactor wL wR:ℂ) •
  pairedState ((product_memLp (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR)).toLp
    (product (α*wL) (α/wR)))
    ((spectator_memLp α β wL wR hα hβ hL hR b P g hc hg).toLp (spectator α β wL wR b P g))

theorem generic_configuration_coe :
    genericState α β wL wR hα hβ hL hR b P g hc hg =ᵐ[volume]
      configurationProfile α β wL wR b P g := by
  let f := pairedState ((product_memLp (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR)).toLp
    (product (α*wL) (α/wR)))
    ((spectator_memLp α β wL wR hα hβ hL hR b P g hc hg).toLp (spectator α β wL wR b P g))
  have hp := pairedState_position_coe (product (α*wL) (α/wR)) (spectator α β wL wR b P g)
    (product_memLp (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR))
    (spectator_memLp α β wL wR hα hβ hL hR b P g hc hg)
  have he : (fun x : KFCausalEuclideanConfiguration.Space =>
      genericState α β wL wR hα hβ hL hR b P g hc hg
        (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationProfile α β wL wR b P g (KFCausalEuclideanConfiguration.split x) := by
    have hs := Lp.coeFn_smul (prefactor wL wR:ℂ) (euclideanPullback f)
    filter_upwards [euclideanPullback_coe (genericState α β wL wR hα hβ hL hR b P g hc hg),hp,hs]
      with x hx hp hs
    change euclideanPullback ((prefactor wL wR:ℂ) • f) x=_ at hx
    rw [map_smul,hs] at hx
    simp only [Function.comp_apply] at hx
    rw [← hx]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hp]
    simpa only [pairedProfile,mul_assoc] using
      paired_configuration α β wL wR b P g (KFCausalEuclideanConfiguration.split x)
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem generic_charge_coe (c : ℝ) (hmatch : Real.pi^2/α=α*c^2) :
    chargeCoordinates (genericState α β wL wR hα hβ hL hR b P g hc hg) =ᵐ[volume]
      chargeProfile α β wL wR c b P g := by
  let f := pairedState ((product_memLp (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR)).toLp
    (product (α*wL) (α/wR)))
    ((spectator_memLp α β wL wR hα hβ hL hR b P g hc hg).toLp (spectator α β wL wR b P g))
  have hm := mixedCoordinates_functions_coe (product (α*wL) (α/wR)) (spectator α β wL wR b P g)
    (product_integrable (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR))
    (product_memLp (α*wL) (α/wR) (mul_pos hα hL) (div_pos hα hR))
    (spectator_memLp α β wL wR hα hβ hL hR b P g hc hg)
  change chargeCoordinates ((prefactor wL wR:ℂ) • f) =ᵐ[volume] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (prefactor wL wR:ℂ) (chargeCoordinates f),
    coordinates_coe 2 4 (mixedCoordinates f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx ht hm
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul]
  change (prefactor wL wR:ℂ)*(KFCausalEuclideanProductCoordinates.coordinates 2 4 (mixedCoordinates f)) x=_
  rw [ht]
  simp only [Function.comp_apply]
  rw [hm]
  simpa only [mul_assoc] using fourier_profile α β wL wR c hα hL hR hmatch b P g x

end Generic

def clock (ε a : ℝ) (C : ℂ) (p s : ℝ) : ℂ := C*clockPhase p (s:ℂ)*clockFunction ε a s

theorem clock_continuous (ε a : ℝ) (C : ℂ) (p : ℝ) : Continuous (clock ε a C p) := by
  unfold clock
  exact (continuous_const.mul (by unfold clockPhase; fun_prop)).mul (clockFunction_continuous ε a)

theorem clock_memLp (ε a : ℝ) (C : ℂ) (p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (clock ε a C p) 2 volume := by
  apply ((clockFunction_memLp ε a hε ha).const_mul C).of_le (clock_continuous ε a C p).aestronglyMeasurable
  filter_upwards [] with s
  simp only [clock,norm_mul]
  have hp : ‖clockPhase p (s:ℂ)‖ ≤ 1 := KFCausalNeutralMixedClockCharge.phase_bound p s
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (norm_nonneg C)) (norm_nonneg (clockFunction ε a s))

def state (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hwL : 1 ≤ wL) (hwR : 1 ≤ wR) : Hilbert :=
  genericState (groundWidth h) (neutralWidth h) wL wR (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (zero_lt_one.trans_le hwL) (zero_lt_one.trans_le hwR)
    b P (clock ε a C p) (clock_continuous ε a C p) (clock_memLp ε a C p hε ha)

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hwL : 1 ≤ wL) (hwR : 1 ≤ wR)

theorem state_configuration_coe :
    state ε a h wL wR C p b P hε ha hh hwL hwR =ᵐ[volume]
      configurationProfile (groundWidth h) (neutralWidth h) wL wR b P (clock ε a C p) :=
  generic_configuration_coe _ _ _ _ _ _ _ _ _ _ _ _ _

theorem state_charge_coe : chargeCoordinates (state ε a h wL wR C p b P hε ha hh hwL hwR) =ᵐ[volume]
    chargeProfile (groundWidth h) (neutralWidth h) wL wR (momentumScale h) b P (clock ε a C p) :=
  generic_charge_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ (groundWidth_matching h hh)

omit wL wR hwL hwR in
theorem state_diagonal (w : ℝ) (hw : 1 ≤ w) :
    state ε a h w w C p b P hε ha hh hw hw=
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P := by
  apply Lp.ext
  filter_upwards [state_configuration_coe ε a h w w C p b P hε ha hh hw hw,
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P] with x hn ho
  rw [hn,ho]
  simp only [configurationProfile,prefactor_diagonal w (zero_lt_one.trans_le hw),Complex.ofReal_one,one_mul,
    chargedQuadratic_diagonal,clock,KFCausalNeutralLinePackets.packet,KFCausalNeutralLinePackets.entire,
    KFCausalReciprocalNeutralPackets.profile,KFCausalReciprocalGaussianStates.configurationDensity]
  push_cast
  simp only [neg_add,Complex.exp_add]
  ring

theorem action_state (θ : ℝ) :
    action h hh θ (state ε a h wL wR C p b P hε ha hh hwL hwR)=
      state ε a h wL wR C p b P hε ha hh hwL hwR := by
  apply chargeCoordinates.injective
  rw [action_coordinates]
  apply Lp.ext
  have he := state_charge_coe ε a h wL wR C p b P hε ha hh hwL hwR
  filter_upwards [KFCausalMixedCircleAction.action_coe (momentumScale h) (momentumScale_ne_zero h hh) θ _,
    (flow_preserves_volume (momentumScale h) (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae he,he]
    with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,chargeProfile_flow,hz]

theorem state_zeroSector : state ε a h wL wR C p b P hε ha hh hwL hwR ∈ zeroSector h hh :=
  action_state ε a h wL wR C p b P hε ha hh hwL hwR

#print axioms generic_configuration_coe
#print axioms generic_charge_coe
#print axioms clock_continuous
#print axioms clock_memLp
#print axioms state_configuration_coe
#print axioms state_charge_coe
#print axioms state_diagonal
#print axioms action_state
#print axioms state_zeroSector
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPackets
