/- The ordered Gaussian quotient specialized to the physical reciprocal
metric, physical standing-plane rotations and the paired broad baseline.
This pointwise estimate does not assert a mixed operator graph: analytic
endpoint identification and source-polynomial absorption remain separate. -/
import UnifiedTheory.Audit.KFCausalNormalizedComplexRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPhysicalTwoShearQuotient
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalReciprocalNormalization
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalTwoShearTransverseQuotient

def physicalMass (α w c : ℝ) (x : Joint 2 4) : ℝ :=
  α*KFCausalReciprocalGaussianStates.coordinateQuadratic w c x+(α/32)*(x (.inr 3))^2

def transverseQuotient (ε h α W w c θ φ : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  clockTransverse ε h (rotationIsometry θ) (rotationIsometry φ)
    (coupling α w) (weights W w) q (normalize α w c x)

theorem physical_transverse_bound (ε h α W w c θ φ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖transverseQuotient ε h α W w c θ φ q x‖ ≤
      Real.exp (-(78/289:ℝ)*physicalMass α w c x) := by
  have hn : ‖normalize α w c x‖^2=physicalMass α w c x := by
    rw [← mass_eq_norm_sq,normalize_mass α w c hα (by linarith)]
    rfl
  simpa only [transverseQuotient,hn] using
    clock_transverse_bound ε h hε hh (rotationIsometry θ) (rotationIsometry φ)
      (coupling α w) (coupling_bound α w hα hw) (weights W w) (weights_bound W w hw hW)
      q hq (normalize α w c x) (normalize_real α w c x)

theorem physical_clock_transverse_bound (ε h α W w c θ φ a : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W) (ha : 0 ≤ a)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖KFCausalTwoShearClockQuotient.quotient ε h a q*transverseQuotient ε h α W w c θ φ q x‖ ≤
      (ε⁻¹*Real.exp (|h|/ε)*Real.exp (-(a/2)*q.re^2+4*a*h^2))*
        Real.exp (-(78/289:ℝ)*physicalMass α w c x) := by
  rw [norm_mul]
  exact mul_le_mul
    (KFCausalTwoShearClockQuotient.quotient_gaussian_bound ε h hε hh a ha q hq)
    (physical_transverse_bound ε h α W w c θ φ hε hh hα hw hW q hq x)
    (norm_nonneg _) (by positivity)

#print axioms physical_transverse_bound
#print axioms physical_clock_transverse_bound
end
end UnifiedTheory.Audit.KFCausalPhysicalTwoShearQuotient
