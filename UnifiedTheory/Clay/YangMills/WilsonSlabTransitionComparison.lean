/- The actual Wilson ground-state transition inherits a one-link row ratio.
The kernel comparison and the positive eigenfunction equation each contribute
exp(6 |beta| B), yielding exp(12 |beta| B), independently of spatial volume.
The positive eigenfunction is an explicit input. This local comparison alone
does not imply a volume-independent or physically scaled spectral gap. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
import UnifiedTheory.Clay.YangMills.WilsonSlabGauge
import UnifiedTheory.Clay.YangMills.GroundStateDirichlet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabTransitionComparison
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabGauge WilsonSlabLocalComparison GroundStateDirichlet

variable (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The actual ground-state Markov transition inherits a volume-independent
one-link row comparison from the Wilson kernel and its own eigenfunction equation. -/
theorem transition_local_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (ψ : SpatialLinks n G → ℝ) (hcψ : Continuous ψ) (hψ : ∀ u, 0 < ψ u)
    (ell : ℝ) (hell : 0 < ell)
    (heig : ∀ u, (∫ v, kernel χ β c u v * ψ v ∂spatialHaar) = ell * ψ u)
    (x : SpatialVertex n) (μ : Fin 3) (u u' v : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x, μ) → u e = u' e) :
    transition (fun uv => kernel χ β c uv.1 uv.2) ψ ell u v ≤
      Real.exp (12 * |β| * B) *
        transition (fun uv => kernel χ β c uv.1 uv.2) ψ ell u' v := by
  let R := Real.exp (6 * |β| * B)
  have hR : 0 < R := Real.exp_pos _
  have hk : kernel χ β c u v ≤ R * kernel χ β c u' v :=
    kernel_comparison n G χ hcχ B hB hχ β c x μ u u' v hu
  have hp : ψ u' ≤ R * ψ u :=
    eigenfunction_comparison n G χ hcχ B hB hχ β c spatialHaar ψ hcψ
      (fun w => (hψ w).le) ell hell heig x μ u' u (fun e he => (hu e he).symm)
  have hprod := mul_le_mul hk hp (hψ u').le
    (mul_nonneg hR.le (kernel_positive χ hcχ β c u' v).le)
  have he : Real.exp (12 * |β| * B) = R ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold transition
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hell (hψ u)) (mul_pos hell (hψ u'))).mpr
  have hm := mul_le_mul_of_nonneg_right hprod (mul_pos hell (hψ v)).le
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSlabTransitionComparison
