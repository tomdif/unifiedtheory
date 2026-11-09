/- Discharge every hypothesis of the positive joint representation for
arbitrary finite neutral exponential-polynomial / reciprocal families.
No coefficient, degree, source, or width-separation cutoff is imposed. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralActualPositive
noncomputable section
open MeasureTheory
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalCrossGeometry (A B)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity pairing)
open KFCausalReciprocalNeutralLaplace (jointMeasure)

theorem cross_widths (α β ε y s w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) :
    0 < (A α w v (scale ε y s)).re ∧ 0 < (B α w v (scale ε y s)).re := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  obtain ⟨hA,hB,_,_⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v _ hw hv ha hc hβ
  exact ⟨hA,hB⟩

variable (n : ℕ) (α β ε y s : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)
local notation "F" => fun i => exponentialProfile (b i) 1 (P i)

include hα hβ hwidth hε hy hw in
theorem positive_integrable :
    Integrable (positiveDensity n α β w (scale ε y s) c F) jointMeasure :=
  KFCausalReciprocalNeutralPositiveForm.positiveDensity_integrable n α β w _ c F
    (fun i j => (cross_widths α β ε y s (w i) (w j) hα hβ hwidth hε hy (hw i) (hw j)).2)
    (fun i j => KFCausalReciprocalNeutralPlaneIntegrability.actual_plane_integrable α β ε y s
      (w i) (w j) hα hβ hwidth hε hy (hw i) (hw j) (b i) (b j) (P i) (P j))

include hα hβ hwidth hε hy hw in
theorem pairing_positive_integral :
    pairing n α β w (scale ε y s) c c F =
      ((Real.pi/4*(∫ p, positiveDensity n α β w (scale ε y s) c F p ∂jointMeasure):ℝ):ℂ) :=
  KFCausalReciprocalNeutralPositiveForm.pairing_integral n α β w _ c F
    (fun i j => (cross_widths α β ε y s (w i) (w j) hα hβ hwidth hε hy (hw i) (hw j)).2)
    (fun i j => KFCausalReciprocalNeutralPlaneIntegrability.actual_plane_integrable α β ε y s
      (w i) (w j) hα hβ hwidth hε hy (hw i) (hw j) (b i) (b j) (P i) (P j))
    (fun i => by have := hw i; linarith)
    (fun i j => (cross_widths α β ε y s (w i) (w j) hα hβ hwidth hε hy (hw i) (hw j)).1)

#print axioms cross_widths
#print axioms positive_integrable
#print axioms pairing_positive_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralActualPositive
