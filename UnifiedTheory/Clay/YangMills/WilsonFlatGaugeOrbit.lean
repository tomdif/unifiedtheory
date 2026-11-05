/- On an even periodic lattice the two flat exteriors witnessing the
microscopic influence obstruction lie on one actual gauge orbit. Physical
gauge-invariant tests cannot distinguish these endpoint configurations. -/
import UnifiedTheory.Clay.YangMills.WilsonAlignedConditional
import UnifiedTheory.Clay.YangMills.WilsonParallelColors

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonFlatGaugeOrbit
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples WilsonAlignedConditional

variable (n : ℕ)

/-- A central gauge transformation using the actual periodic bipartite parity. -/
def alternatingGauge (heven : 2 ∣ n) : GaugeTransformation (Vertex n) Q := fun x =>
  if WilsonParallelColors.parity n heven x = 0 then 1 else -1

theorem alternating_step (heven : 2 ∣ n) (x : Vertex n) (μ : Fin 4) :
    alternatingGauge n heven (step n x μ) = -alternatingGauge n heven x := by
  unfold alternatingGauge
  rw [WilsonParallelColors.parity_step]
  generalize WilsonParallelColors.parity n heven x = p
  fin_cases p
  · norm_num
  · norm_num
    intro h
    exact (h (by decide)).elim

/-- The two constant flat configurations are gauge equivalent, not distinct physical states. -/
theorem constant_neg_one_gauge (heven : 2 ∣ n) :
    gauge (Vertex n) Q (alternatingGauge n heven) (constantConfiguration n 1) =
      constantConfiguration n (-1) := by
  funext e
  rcases e with ⟨x, y, μ, hμ⟩
  cases hμ
  change alternatingGauge n heven x * 1 *
    (alternatingGauge n heven (step n x μ))⁻¹ = -1
  rw [alternating_step]
  unfold alternatingGauge
  split <;> norm_num

/-- Every gauge-invariant observable identifies the two endpoint configurations exactly. -/
theorem invariant_endpoints (heven : 2 ∣ n) (F : Configuration (Vertex n) Q → ℝ)
    (hF : ∀ g U, F (gauge (Vertex n) Q g U) = F U) :
    F (constantConfiguration n (-1)) = F (constantConfiguration n 1) := by
  rw [← constant_neg_one_gauge n heven]
  exact hF _ _

end
end UnifiedTheory.Clay.YangMills.WilsonFlatGaugeOrbit
