/- The actual charge-coordinate modulation family is a translated Gaussian
in the two antisymmetric positions and a modulated Gaussian in the four
spectator positions. The Fourier sign and the 2*pi normalization are explicit. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
import UnifiedTheory.Audit.KFCausalFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalFourierTranslation (phase phase_norm phase_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_continuous clockFunction_memLp neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)

def shiftedGaussian (α : ℝ) (v : Block 2) (x : Block 2) : ℂ := gaussian 2 α (x+v)

theorem shiftedGaussian_integrable (α : ℝ) (hα : 0 < α) (v : Block 2) :
    Integrable (shiftedGaussian α v) :=
  (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussian_integrable 2 α hα)

theorem shiftedGaussian_memLp (α : ℝ) (hα : 0 < α) (v : Block 2) :
    MemLp (shiftedGaussian α v) 2 :=
  (gaussian_memLp 2 α hα).comp_measurePreserving (measurePreserving_add_right volume v)

theorem shiftedGaussian_fourier (α : ℝ) (v x : Block 2) :
    (𝓕 (shiftedGaussian α v)) x = phase v x*(𝓕 (gaussian 2 α)) x := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (Block 2)) (gaussian 2 α) v) x
  simpa only [shiftedGaussian,phase,Circle.smul_def,smul_eq_mul,
    VectorFourier.fourierIntegral,Function.comp_apply,innerₗ_apply_apply] using h

def modulatedSpectator (α β : ℝ) (g : ℝ → ℂ) (r : Block 4) (x : Block 4) : ℂ :=
  phase r x*spectator α β g x

theorem modulatedSpectator_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2) (r : Block 4) :
    MemLp (modulatedSpectator α β g r) 2 := by
  apply (spectator_memLp α β hα hβ g hc hg).of_le
    ((phase_continuous r).mul (spectator_continuous α β g hc)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖phase r x*spectator α β g x‖ ≤ ‖spectator α β g x‖
  simp only [norm_mul,phase_norm,one_mul,le_refl]

def pairedTrial (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2) (v : Block 2) (r : Block 4) :=
  pairedState ((shiftedGaussian_memLp α hα v).toLp (shiftedGaussian α v))
    ((modulatedSpectator_memLp α β hα hβ g hc hg r).toLp (modulatedSpectator α β g r))

theorem phase_split (k x : Joint 2 4) :
    phase (split 2 4 k).1 (split 2 4 x).1 * phase (split 2 4 k).2 (split 2 4 x).2 =
      (Real.fourierChar (inner ℝ x k):ℂ) := by
  rw [← real_inner_comm x k,inner_split]
  simp only [phase,AddChar.map_add_eq_mul,Circle.coe_mul]

theorem pairedTrial_chargeCoordinates (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hmatch : Real.pi^2/α = α*c^2) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2)
    (k : Joint 2 4) :
    chargeCoordinates (pairedTrial α β hα hβ g hc hg (split 2 4 k).1 (split 2 4 k).2) =ᵐ[volume]
      KFCausalEuclideanFourierUniqueness.modulate k
        (fun x => ((Real.pi/α:ℝ):ℂ)*profile α β c g x) := by
  have hm := mixedCoordinates_functions_coe (shiftedGaussian α (split 2 4 k).1)
    (modulatedSpectator α β g (split 2 4 k).2)
    (shiftedGaussian_integrable α hα _) (shiftedGaussian_memLp α hα _)
    (modulatedSpectator_memLp α β hα hβ g hc hg _)
  filter_upwards [coordinates_coe 2 4
      (mixedCoordinates (pairedTrial α β hα hβ g hc hg (split 2 4 k).1 (split 2 4 k).2)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hp
  refine hx.trans (hp.trans ?_)
  rw [shiftedGaussian_fourier,modulatedSpectator]
  change _ = (Real.fourierChar (inner ℝ x k):ℂ)*(((Real.pi/α:ℝ):ℂ)*profile α β c g x)
  rw [← mixed_profile_identity α β c hα hmatch g x,← phase_split k x]
  ring

def displacement (hbar : ℝ) (k : Joint 2 4) : Block 2 :=
  (split 2 4 (dilate (momentumScale hbar) k)).1

def spectatorParameter (k : Joint 2 4) : Block 4 := (split 2 4 k).2

theorem state_eq_pairedTrial (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k =
      pairedTrial (groundWidth hbar) (neutralWidth hbar) (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh) (clockFunction ε a) (clockFunction_continuous ε a)
        (clockFunction_memLp ε a hε ha) (displacement hbar k) (spectatorParameter k) := by
  apply chargeCoordinates.injective
  rw [KFCausalClockFloorCoherentStates.state_coordinates]
  apply Lp.ext
  exact (KFCausalClockFloorCoherentStates.mixedState_coe ε a hbar hε ha hh k).trans
    (pairedTrial_chargeCoordinates _ _ (momentumScale hbar) (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (groundWidth_matching hbar hh)
      (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)
      (dilate (momentumScale hbar) k)).symm

def positionProfile (α β : ℝ) (g : ℝ → ℂ) (v : Block 2) (r : Block 4)
    (x : KFCausalEuclideanConfiguration.Space) : ℂ :=
  shiftedGaussian α v (WithLp.toLp 2 ![KFCausalPairedModeCoordinates.scale*(x 1-x 2),
    KFCausalPairedModeCoordinates.scale*(x 3-x 4)]) *
  modulatedSpectator α β g r (WithLp.toLp 2 ![x 0,
    KFCausalPairedModeCoordinates.scale*(x 1+x 2),
    KFCausalPairedModeCoordinates.scale*(x 3+x 4),x 5])

theorem state_position_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    KFCausalEuclideanConfiguration.euclideanPullback
      (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k) =ᵐ[volume]
      positionProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a)
        (displacement hbar k) (spectatorParameter k) := by
  rw [state_eq_pairedTrial]
  exact pairedState_position_coe _ _ _ _

#print axioms shiftedGaussian_integrable
#print axioms shiftedGaussian_memLp
#print axioms shiftedGaussian_fourier
#print axioms modulatedSpectator_memLp
#print axioms phase_split
#print axioms pairedTrial_chargeCoordinates
#print axioms state_eq_pairedTrial
#print axioms state_position_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates
