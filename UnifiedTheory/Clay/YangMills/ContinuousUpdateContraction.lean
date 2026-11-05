/- Reversible continuous-observable moment decay gives actual L2 norm
contraction, with no uniform observable prefactor or L2 extension premise. -/
import UnifiedTheory.Clay.YangMills.ContinuousUpdateGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction
noncomputable section
open MeasureTheory ContinuousUpdateGap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Only the geometric rate enters the one-step norm bound. -/
theorem norm_le_of_moments (P : C(X, ℝ) → C(X, ℝ))
    (hrev : ∀ F G, pairing μ F (P G) = pairing μ (P F) G)
    (F : C(X, ℝ)) (q C : ℝ) (hq : 0 ≤ q)
    (hdecay : ∀ k, |pairing μ F (iterate P k F)| ≤ C * q ^ k) :
    ‖ContinuousMap.toLp 2 μ ℝ (P F)‖ ≤ q * ‖ContinuousMap.toLp 2 μ ℝ F‖ := by
  let u : ℕ → Lp ℝ 2 μ := fun k => ContinuousMap.toLp 2 μ ℝ (iterate P k F)
  have hp : ∀ k, RCLike.re (inner ℝ (u k) (u (k + 2))) = ‖u (k + 1)‖ ^ 2 :=
    adjacent_pairing μ P hrev F
  have hb (k : ℕ) : ‖u k‖ ^ 2 ≤ C * q ^ (2 * k) := by
    change ‖ContinuousMap.toLp 2 μ ℝ (iterate P k F)‖ ^ 2 ≤ _
    rw [embedding_square, iterate_pairing μ P hrev, ← two_mul]
    exact (le_abs_self _).trans (hdecay (2 * k))
  exact ObservableMomentGap.sequence_norm_le_of_geometric_bound u hp q C hq hb

/-- Cauchy--Schwarz in the genuine L2 embeddings. -/
theorem abs_pairing_le (F G : C(X, ℝ)) :
    |pairing μ F G| ≤ ‖ContinuousMap.toLp 2 μ ℝ F‖ *
      ‖ContinuousMap.toLp 2 μ ℝ G‖ := by
  rw [← embedding_pairing]
  exact abs_real_inner_le_norm _ _

end
end UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction
