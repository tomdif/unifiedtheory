/- L2 densities for the actual polynomial ordered outputs and their
clock momenta, plus the differentiated-polynomial shear correction.
All integrability is derived from the established physical widths. -/
import UnifiedTheory.Audit.KFCausalPolynomialRadiusEnvelope
import UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
import UnifiedTheory.Audit.KFCausalProjectedPolynomialOrderedProfile
import UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction profile)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth scale_bound)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalPolynomialKernelResponse (weight)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalPolynomialRadiusEnvelope
open UnifiedTheory.Audit.KFCausalClockResponseTransport (weakSlope)

variable (ε a h : ℝ) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (P : Polynomial ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "r" => scale ε (-h/2)
local notation "A" => clockAmplitude ε a p (-h/2)

def amplitude (x : Configuration) : ℂ :=
  (l x.2:ℂ)^n.val*weight ε (-h/2) P x.2 x.1*(C*profile A r α β b x)

def momentum (x : Configuration) : ℂ :=
  (-Complex.I*(h:ℂ))*weakSlope ε a p (-h/2) x.1*amplitude ε a h C p b P l n x

def slopeWeight (x : Configuration) : ℂ :=
  (l x.2:ℂ)^n.val*(P.derivative.eval (position (r x.1) x.2 4)*direction (r x.1) x.2 4+
    weight ε (-h/2) P x.2 x.1*KFCausalRelativeGaussianDifferential.slope r α β b x)*C

def slopeDensity (x : Configuration) : ℂ :=
  slopeWeight ε h C b P l n x*profile A r α β b x

variable (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem amplitude_density :
    KFCausalPolynomialGaussianDomain.output ε a h hε ha hh C p b 4 hb P modelDirections l (index n)
      =ᵐ[volume] amplitude ε a h C p b P l n := by
  filter_upwards [KFCausalProjectedPolynomialOrderedProfile.source_factor_coe
    ε a h hε ha hh hb C p b P modelDirections l n] with x hx
  rw [hx]
  unfold amplitude weight KFCausalPolynomialOrderedProfile.orderedProfile
    KFCausalPolynomialOrderedProfile.gaussianProfile
  ring

include hε ha hh hb in
theorem amplitude_memLp : MemLp (amplitude ε a h C p b P l n) 2 volume :=
  (Lp.memLp (KFCausalPolynomialGaussianDomain.output ε a h hε ha hh C p b 4 hb P
    modelDirections l (index n))).ae_eq (amplitude_density ε a h C p b P l n hε ha hh hb)

theorem momentum_density :
    KFCausalPolynomialMomentumDomain.momentumFactor ε a h hε ha hh p b 4 C hb P modelDirections l (index n)
      =ᵐ[volume] momentum ε a h C p b P l n := by
  filter_upwards [KFCausalPolynomialOrderedMomentumDensity.polynomial_relation
    ε a h hε ha hh hb C p b 4 P modelDirections l n,
    amplitude_density ε a h C p b P l n hε ha hh hb] with x hm hi
  rw [hm,hi]
  rfl

include hε ha hh hb in
theorem momentum_memLp : MemLp (momentum ε a h C p b P l n) 2 volume :=
  (Lp.memLp (KFCausalPolynomialMomentumDomain.momentumFactor ε a h hε ha hh p b 4 C hb P
    modelDirections l (index n))).ae_eq (momentum_density ε a h C p b P l n hε ha hh hb)

include hε hb in
theorem slopeWeight_continuous : Continuous (slopeWeight ε h C b P l n) := by
  have hr := (scale_smooth ε (-h/2) hε (shift_bound ε h hb)).continuous
  have hp (i : Fin 5) : Continuous (fun x : Configuration => position (r x.1) x.2 i) :=
    KFCausalShiftedPolynomialMoments.position_continuous r hr i
  have hd (i : Fin 5) : Continuous (fun x : Configuration => direction (r x.1) x.2 i) := by
    unfold direction
    split_ifs <;> fun_prop
  have hs : Continuous (KFCausalRelativeGaussianDifferential.slope r α β b) := by
    unfold KFCausalRelativeGaussianDifferential.slope
    exact continuous_finset_sum _ (fun i _ =>
      (continuous_const.sub (continuous_const.mul (hp i))).mul (hd i))
  exact (((Complex.continuous_ofReal.comp (l.continuous.comp continuous_snd)).pow n.val).mul
    (((P.derivative.continuous.comp (hp 4)).mul (hd 4)).add
      ((P.continuous.comp (hp 4)).mul hs))).mul continuous_const

include hε hb in
theorem slopeWeight_growth : Growth (slopeWeight ε h C b P l n) := by
  let M := Real.exp (|-h/2|/(2*ε))
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hr (s : ℝ) : ‖r s‖ ≤ M := scale_bound ε (-h/2) s hε (shift_bound ε h hb)
  have hp := growth_position r M hM hr 4
  exact growth_mul (growth_mul (growth_pow (growth_field l) n.val)
    (growth_add (growth_mul (growth_polynomial hp P.derivative) (growth_direction r M hM hr 4))
      (growth_mul (growth_polynomial hp P) (growth_slope r M hM hr α β b)))) (growth_const C)

include hε ha hh hb in
theorem slopeDensity_memLp : MemLp (slopeDensity ε a h C p b P l n) 2 volume :=
  weighted_profile_memLp ε (-h/2) hε (shift_bound ε h hb)
    (slopeWeight ε h C b P l n) (slopeWeight_continuous ε h C b P l n hε hb)
    (slopeWeight_growth ε h C b P l n hε hb)
    A (clockAmplitude_smooth ε a p (-h/2) hε (shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (shift_bound ε h hb))
    α β (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) b

#print axioms amplitude_density
#print axioms amplitude_memLp
#print axioms momentum_density
#print axioms momentum_memLp
#print axioms slopeWeight_continuous
#print axioms slopeWeight_growth
#print axioms slopeDensity_memLp
end
end UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
