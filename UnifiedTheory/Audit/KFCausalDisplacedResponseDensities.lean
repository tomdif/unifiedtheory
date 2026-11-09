/- Explicit densities of the normalized displaced growing factors.
The normalization depends on the clock width and remains inside the
complex amplitude. Both representatives are jointly continuous in the
charge angle and full configuration, including the closed clock strip. -/
import UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge
import UnifiedTheory.Audit.KFCausalDisplacedMomentumOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalDisplacedResponseDensities
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
  (source_curve_continuous amplitude_curve_continuous clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalGaussianResponseDensities (amplitude momentum)

def normalizer (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) : ℝ :=
  ‖trialState ε a h hε ha hh‖⁻¹

def coefficient (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Joint 2 4) : ℂ :=
  (normalizer ε a h hε ha hh:ℂ)*KFCausalClockFloorDisplacedSources.amplitude h q k

def inputDensity (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) : Configuration → ℂ :=
  amplitude ε a (groundWidth h) (neutralWidth h) (clockFrequency h k) (-h/2)
    (source h q k) (coefficient ε a h hε ha hh q k) l n

def momentumDensity (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) : Configuration → ℂ :=
  momentum ε a (groundWidth h) (neutralWidth h) (clockFrequency h k) (-h/2) h
    (source h q k) (coefficient ε a h hε ha hh q k) l n

private theorem family_continuous (ε a α β p y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (b : ℝ → Fin 5 → ℂ) (C : ℝ → ℂ) (hb : Continuous b) (hC : Continuous C)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    Continuous (fun z : ℝ × Configuration => amplitude ε a α β p y (b z.1) (C z.1) l n z.2) := by
  have hs := (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous
  have hA := (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p y hε hy).continuous
  have hp (i : Fin 5) : Continuous (fun z : ℝ × Configuration =>
      KFCausalRelativeGaussianDifferential.position (KFCausalClockFloorRelativeShift.scale ε y z.2.1) z.2.2 i) := by
    unfold KFCausalRelativeGaussianDifferential.position
    split_ifs <;> fun_prop
  have hbi (i : Fin 5) : Continuous (fun z : ℝ × Configuration => b z.1 i) :=
    (continuous_apply i).comp (hb.comp continuous_fst)
  unfold amplitude KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
  exact ((Complex.continuous_ofReal.comp (l.continuous.comp (continuous_snd.comp continuous_snd))).pow n.val).mul
    ((hC.comp continuous_fst).mul ((hA.comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_finset_sum _ (fun i _ => (hbi i).mul (hp i))).sub
        (continuous_finset_sum _ (fun i _ => continuous_const.mul ((hp i).pow 2)))).cexp))


variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (v : Fin 4 → Transverse)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "N" => normalizer ε a h hε ha hh
local notation "C" => KFCausalClockFloorDisplacedSources.amplitude h q k
local notation "p" => clockFrequency h k
local notation "b" => source h q k
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem input_factor_density :
    KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k v l (index n) =ᵐ[volume]
      inputDensity ε a h hε ha hh q k l n := by
  filter_upwards [Lp.coeFn_smul N
    (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)),
    KFCausalSourcedResponseFactorBridge.input_factor_density ε a α β hε ha hα hβ hw C p b h hb v l n]
    with x hs hd
  change (N • KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)) x = _
  rw [hs]
  simp only [Pi.smul_apply,hd,Complex.real_smul,inputDensity,coefficient,amplitude]
  ring

theorem momentum_factor_density :
    KFCausalDisplacedMomentumOrbit.factorOutput ε a h hε ha hh hb q k v l (index n) =ᵐ[volume]
      momentumDensity ε a h hε ha hh q k l n := by
  filter_upwards [Lp.coeFn_smul N
    (KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)),
    KFCausalSourcedResponseFactorBridge.momentum_factor_density ε a α β hε ha hα hβ hw C p b h hh hb v l n]
    with x hs hd
  change (N • KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)) x = _
  rw [hs]
  simp only [Pi.smul_apply,hd,Complex.real_smul,momentumDensity,coefficient,momentum,amplitude]
  ring


include hb in
theorem input_joint_continuous : Continuous (fun z : ℝ × Configuration =>
    inputDensity ε a h hε ha hh (parameter (2*Real.pi*z.1) q) (parameter (2*Real.pi*z.1) k) l n z.2) := by
  unfold inputDensity
  simp only [clockFrequency_parameter]
  apply family_continuous ε a α β p (-h/2) hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
    (fun θ => source h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k))
    (fun θ => coefficient ε a h hε ha hh (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)) ?_ ?_ l n
  · exact (source_curve_continuous h q k).comp (continuous_const.mul continuous_id)
  · exact continuous_const.mul ((amplitude_curve_continuous h q k).comp (continuous_const.mul continuous_id))

include hb in
theorem momentum_joint_continuous : Continuous (fun z : ℝ × Configuration =>
    momentumDensity ε a h hε ha hh (parameter (2*Real.pi*z.1) q) (parameter (2*Real.pi*z.1) k) l n z.2) := by
  have hy := KFCausalClockFloorShiftedOutput.shift_bound ε h hb
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε (-h/2) hε hy
  have hz := (KFCausalClockFloorRelativeShift.argument_smooth ε (-h/2)).continuous
  have hwc : Continuous (KFCausalClockResponseTransport.weakSlope ε a p (-h/2)) := by
    unfold KFCausalClockResponseTransport.weakSlope
    fun_prop
  change Continuous (fun z : ℝ × Configuration => (-Complex.I*(h:ℂ))*
    KFCausalClockResponseTransport.weakSlope ε a (clockFrequency h (parameter (2*Real.pi*z.1) k)) (-h/2) z.2.1*
      inputDensity ε a h hε ha hh (parameter (2*Real.pi*z.1) q) (parameter (2*Real.pi*z.1) k) l n z.2)
  simp only [clockFrequency_parameter]
  exact (continuous_const.mul (hwc.comp (continuous_fst.comp continuous_snd))).mul
    (input_joint_continuous ε a h hε ha hh hb q k l n)

#print axioms input_factor_density
#print axioms momentum_factor_density
#print axioms input_joint_continuous
#print axioms momentum_joint_continuous
end
end UnifiedTheory.Audit.KFCausalDisplacedResponseDensities
