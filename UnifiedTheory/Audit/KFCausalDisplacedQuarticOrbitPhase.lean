/- The actual test orbit has a positive real source amplitude, not merely
a known modulus. This checks the relative phases needed when projecting
the state, where off-diagonal charge-angle pairings must be retained. -/
import UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalDisplacedQuarticOrbitPhase
noncomputable section
open UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

theorem orbit_v_zero (A lam h θ : ℝ) :
    vParameter h (parameter θ (momentumParameter A lam h)) = 0 := by
  rw [momentum_fixed]
  ext i
  fin_cases i <;> simp [vParameter,KFCausalEuclideanProductCoordinates.split,
    KFCausalNormalizedChargeFlow.dilate,momentumParameter]
  all_goals rfl

theorem amplitude_exact (A lam h θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    amplitude h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h)) =
      (Real.exp (-(groundWidth h*A^2*(Real.cos θ)^2/2+neutralWidth h*A^2)):ℂ) := by
  rw [amplitude,KFCausalClockFloorDisplacedCentering.constant_eq]
  have hp : KFCausalFourierTranslation.phase
      (uParameter h (parameter θ (positionParameter A)))
      (vParameter h (parameter θ (momentumParameter A lam h))) = 1 := by
    rw [orbit_v_zero]
    simp [KFCausalFourierTranslation.phase]
  rw [hp,one_mul,actual_center A lam h θ hA hh,
    KFCausalClockFloorCenteredGaussian.amplitude,Complex.ofReal_exp]
  congr 1
  simp only [KFCausalClockFloorCenteredGaussian.realQuadratic,
    KFCausalClockFloorCenteredGaussian.weight,position,Fin.sum_univ_succ]
  norm_num
  push_cast
  ring

theorem amplitude_pair (A lam h θ φ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    star (amplitude h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h))) *
      amplitude h (parameter φ (positionParameter A)) (parameter φ (momentumParameter A lam h)) =
        (Real.exp (-(groundWidth h*A^2*(Real.cos θ)^2/2+neutralWidth h*A^2)-
          (groundWidth h*A^2*(Real.cos φ)^2/2+neutralWidth h*A^2)):ℂ) := by
  rw [amplitude_exact A lam h θ hA hh,amplitude_exact A lam h φ hA hh]
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← Real.exp_add,sub_eq_add_neg]

#print axioms orbit_v_zero
#print axioms amplitude_exact
#print axioms amplitude_pair
end
end UnifiedTheory.Audit.KFCausalDisplacedQuarticOrbitPhase
