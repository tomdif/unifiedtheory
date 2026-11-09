/- Actual measure substitution for the radial map on the proved positivity
box. The kernel identity retains the exact Jacobian factor. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialJacobian
import UnifiedTheory.Audit.KFCausalConformal4DCompactKernelDerivative
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialPushforward
noncomputable section
open Real Set MeasureTheory
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DRadialScale KFCausalConformal4DRadialJacobian
open KFCausalConformal4DRegularVolume (regularVolume)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalConformal4DCompactKernelDerivative (cone)

theorem integral_image (c : ℝ) (hc : |c|≤1/54) (s : Set (ℝ×ℝ))
    (hs : MeasurableSet s) (hb : s⊆closedBox) (g : (ℝ×ℝ)→ℝ) :
    (∫ y in radialMap c '' s, g y)=
      ∫ p in s, jacobianFactor c p.1 p.2/sqrt (normalized c p.1 p.2)*g (radialMap c p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p hp => (radialMap_hasFDerivAt c p
      (normalized_pos c p.1 p.2 hc (hb hp).1 (hb hp).2)).hasFDerivWithinAt)
    ((radialMap_injective c hc).mono hb) g]
  apply setIntegral_congr_fun hs
  intro p hp
  dsimp only
  rw [abs_of_pos (mapDerivative_det_pos c p hc (hb hp)),mapDerivative_det c p
    (normalized_pos c p.1 p.2 hc (hb hp).1 (hb hp).2),smul_eq_mul]

theorem integrable_image_iff (c : ℝ) (hc : |c|≤1/54) (s : Set (ℝ×ℝ))
    (hs : MeasurableSet s) (hb : s⊆closedBox) (g : (ℝ×ℝ)→ℝ) :
    IntegrableOn g (radialMap c '' s) ↔
      IntegrableOn (fun p => jacobianFactor c p.1 p.2/sqrt (normalized c p.1 p.2)*
        g (radialMap c p)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun p hp => (radialMap_hasFDerivAt c p
      (normalized_pos c p.1 p.2 hc (hb hp).1 (hb hp).2)).hasFDerivWithinAt)
    ((radialMap_injective c hc).mono hb) g]
  apply integrableOn_congr_fun
  · intro p hp
    dsimp only
    rw [abs_of_pos (mapDerivative_det_pos c p hc (hb hp)),mapDerivative_det c p
      (normalized_pos c p.1 p.2 hc (hb hp).1 (hb hp).2),smul_eq_mul]
  · exact hs

theorem cone_iff (c : ℝ) (p : ℝ×ℝ) (hp : 0<normalized c p.1 p.2) :
    radialMap c p∈cone ↔ p∈cone := by
  have hs := scale_pos c p.1 p.2 hp
  have ht : scale c p.1 p.2*p.1<0 ↔ p.1<0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hs (b := p.1) (c := 0))
  change (scale c p.1 p.2*p.1<0 ∧ 0<scale c p.1 p.2*p.2 ∧
    scale c p.1 p.2*p.2< -(scale c p.1 p.2*p.1)) ↔
    (p.1<0 ∧ 0<p.2 ∧ p.2< -p.1)
  rw [← mul_neg, mul_lt_mul_iff_right₀ hs, mul_pos_iff_of_pos_left hs,
    ht]

def flatKernel (rho : ℝ) (p : ℝ×ℝ) : ℝ :=
  p.2^2*f4D (rho*((π/24)*(p.1^2-p.2^2)^2))

def curvedKernel (rho c : ℝ) (p : ℝ×ℝ) : ℝ :=
  p.2^2*f4D (rho*regularVolume c p.1 p.2)

theorem kernel_jacobian (rho c : ℝ) (p : ℝ×ℝ) (hp : 0<normalized c p.1 p.2) :
    (jacobianFactor c p.1 p.2/sqrt (normalized c p.1 p.2))*flatKernel rho (radialMap c p)=
      curvedKernel rho c p*jacobianFactor c p.1 p.2 := by
  unfold flatKernel curvedKernel
  rw [phase_flattening c p hp.le]
  change (jacobianFactor c p.1 p.2/sqrt (normalized c p.1 p.2))*
    ((scale c p.1 p.2*p.2)^2*f4D (rho*((π/24)*
      ((radialMap c p).1^2-(radialMap c p).2^2)^2)))=_
  rw [← scale_sq]
  have hn := (scale_pos c p.1 p.2 hp).ne'
  field_simp

theorem kernel_integral_image (rho c : ℝ) (hc : |c|≤1/54) (s : Set (ℝ×ℝ))
    (hs : MeasurableSet s) (hb : s⊆closedBox) (g : (ℝ×ℝ)→ℝ) :
    (∫ y in radialMap c '' s, flatKernel rho y*g y)=
      ∫ p in s, curvedKernel rho c p*jacobianFactor c p.1 p.2*g (radialMap c p) := by
  rw [integral_image c hc s hs hb]
  apply setIntegral_congr_fun hs
  intro p hp
  dsimp only
  rw [← mul_assoc,kernel_jacobian rho c p
    (normalized_pos c p.1 p.2 hc (hb hp).1 (hb hp).2)]

#print axioms integral_image
#print axioms integrable_image_iff
#print axioms cone_iff
#print axioms kernel_jacobian
#print axioms kernel_integral_image
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialPushforward
