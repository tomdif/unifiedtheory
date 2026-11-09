/- Exact rotation and infinitesimal laws for the standing-wave coordinate
functions. Antisymmetric frequency k enters as the momentum coordinate c*k.
The same cosine/sine orientation is checked independently in the finite model. -/
import UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalStandingCoordinateDerivatives
noncomputable section
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow

def cosine (i : Fin 2) (x : Space) : ℝ := x (.inr i.castSucc.succ)
def sine (c : ℝ) (i : Fin 2) (x : Space) : ℝ := c*x (.inl i)

theorem cosine_flow (c : ℝ) (hc : c ≠ 0) (i : Fin 2) (θ : ℝ) (x : Space) :
    cosine i (flowEquiv c hc θ x) = Real.cos θ*cosine i x+Real.sin θ*sine c i x := by
  fin_cases i
  · have h := congrArg Prod.snd (flow_first_plane c hc θ x)
    dsimp only at h
    change flowEquiv c hc θ x (.inr 1) = Real.cos θ*x (.inr 1)+Real.sin θ*(c*x (.inl 0))
    rw [h]
    ring
  · have h := congrArg Prod.snd (flow_second_plane c hc θ x)
    dsimp only at h
    change flowEquiv c hc θ x (.inr 2) = Real.cos θ*x (.inr 2)+Real.sin θ*(c*x (.inl 1))
    rw [h]
    ring

theorem sine_flow (c : ℝ) (hc : c ≠ 0) (i : Fin 2) (θ : ℝ) (x : Space) :
    sine c i (flowEquiv c hc θ x) = Real.cos θ*sine c i x-Real.sin θ*cosine i x := by
  fin_cases i
  · have h := congrArg Prod.fst (flow_first_plane c hc θ x)
    dsimp only at h
    change c*(flowEquiv c hc θ x (.inl 0)) = Real.cos θ*(c*x (.inl 0))-Real.sin θ*x (.inr 1)
    rw [h]
    field_simp
  · have h := congrArg Prod.fst (flow_second_plane c hc θ x)
    dsimp only at h
    change c*(flowEquiv c hc θ x (.inl 1)) = Real.cos θ*(c*x (.inl 1))-Real.sin θ*x (.inr 2)
    rw [h]
    field_simp

theorem cosine_derivative (c : ℝ) (hc : c ≠ 0) (i : Fin 2) (x : Space) (θ : ℝ) :
    HasDerivAt (fun φ => cosine i (flowEquiv c hc φ x))
      (sine c i (flowEquiv c hc θ x)) θ := by
  have h := ((Real.hasDerivAt_cos θ).mul_const (cosine i x)).add
    ((Real.hasDerivAt_sin θ).mul_const (sine c i x))
  simpa only [cosine_flow, sine_flow, sub_eq_add_neg, neg_mul, add_comm] using h

theorem sine_derivative (c : ℝ) (hc : c ≠ 0) (i : Fin 2) (x : Space) (θ : ℝ) :
    HasDerivAt (fun φ => sine c i (flowEquiv c hc φ x))
      (-cosine i (flowEquiv c hc θ x)) θ := by
  have h := ((Real.hasDerivAt_cos θ).mul_const (sine c i x)).sub
    ((Real.hasDerivAt_sin θ).mul_const (cosine i x))
  change HasDerivAt (fun φ => Real.cos φ*sine c i x-Real.sin φ*cosine i x)
    (-Real.sin θ*sine c i x-Real.cos θ*cosine i x) θ at h
  simpa only [cosine_flow, sine_flow, neg_add, neg_mul, sub_eq_add_neg, add_comm] using h

#print axioms cosine_flow
#print axioms sine_flow
#print axioms cosine_derivative
#print axioms sine_derivative

end
end UnifiedTheory.Audit.KFCausalStandingCoordinateDerivatives
