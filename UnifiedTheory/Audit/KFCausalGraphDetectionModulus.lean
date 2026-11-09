/- Fixed physical test vectors are controlled uniformly on bounded parts
of an injective closed graph by an injective bounded output detector.
The modulus depends on the test vector; no norm coercivity is asserted. -/
import UnifiedTheory.Audit.KFCausalWeightedGraphWeakDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGraphDetectionModulus
noncomputable section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairing_control (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hker : ∀ x, (x,0) ∈ T.graph → x = 0)
    (B : H →L[ℂ] H) (hB : Function.Injective B)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (z : H) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : H, ‖x‖ ≤ C → ‖y‖ ≤ D →
      (x,y) ∈ T.graph → ‖B y‖ < δ → ‖inner ℂ x z‖ < η := by
  by_contra hn
  push_neg at hn
  have hex (n : ℕ) := hn (1/((n:ℝ)+1)) (by positivity)
  choose x y hx hy hg hd hi using hex
  have hz : Tendsto (fun n => B (y n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hd n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat)
  have hw := KFCausalWeightedGraphWeakDecay.weak_zero T hT hker B hB x y C D hC hD hx hy hg hz z
  have he := (Metric.tendsto_nhds.mp hw η hη).exists
  obtain ⟨n,hn⟩ := he
  exact (hi n).not_gt (by simpa only [dist_zero_right] using hn)

theorem detector_lower (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hker : ∀ x, (x,0) ∈ T.graph → x = 0)
    (B : H →L[ℂ] H) (hB : Function.Injective B)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (z : H) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : H, ‖x‖ ≤ C → ‖y‖ ≤ D →
      (x,y) ∈ T.graph → η ≤ ‖inner ℂ x z‖ → δ ≤ ‖B y‖ := by
  obtain ⟨δ,hδ,hc⟩ := pairing_control T hT hker B hB C D hC hD z η hη
  refine ⟨δ,hδ,?_⟩
  intro x y hx hy hg hi
  by_contra hn
  exact hi.not_gt (hc x y hx hy hg (lt_of_not_ge hn))

#print axioms pairing_control
#print axioms detector_lower
end
end UnifiedTheory.Audit.KFCausalGraphDetectionModulus
