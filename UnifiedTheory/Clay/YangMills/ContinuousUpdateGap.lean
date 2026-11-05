/- Observable-dependent correlation decay implies a Dirichlet gap for
actual reversible continuous-observable updates. The proof uses their true
L2 embeddings, without assuming an L2 operator extension or uniform prefactor. -/
import UnifiedTheory.Clay.YangMills.ObservableMomentGap
import UnifiedTheory.Clay.YangMills.SquaredDensityConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuousUpdateGap
noncomputable section
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def iterate (P : C(X, ℝ) → C(X, ℝ)) : ℕ → C(X, ℝ) → C(X, ℝ)
  | 0, F => F
  | k + 1, F => P (iterate P k F)

def pairing (F G : C(X, ℝ)) : ℝ := ∫ x, F x * G x ∂μ

theorem embedding_pairing (F G : C(X, ℝ)) :
    inner ℝ (ContinuousMap.toLp 2 μ ℝ F) (ContinuousMap.toLp 2 μ ℝ G) = pairing μ F G := by
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [pairing, mul_comm]

theorem embedding_square (F : C(X, ℝ)) :
    ‖ContinuousMap.toLp 2 μ ℝ F‖ ^ 2 = pairing μ F F := by
  rw [← real_inner_self_eq_norm_sq, embedding_pairing]

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
/-- Reversibility moves powers between the two actual observables. -/
theorem iterate_pairing (P : C(X, ℝ) → C(X, ℝ))
    (hrev : ∀ F G, pairing μ F (P G) = pairing μ (P F) G)
    (F : C(X, ℝ)) (k l : ℕ) :
    pairing μ (iterate P k F) (iterate P l F) = pairing μ F (iterate P (k + l) F) := by
  induction k generalizing l with
  | zero => simp only [iterate, zero_add]
  | succ k ih =>
    change pairing μ (P (iterate P k F)) (iterate P l F) = _
    rw [← hrev]
    change pairing μ (iterate P k F) (iterate P (l + 1) F) = _
    rw [ih]
    congr 2
    omega

theorem adjacent_pairing (P : C(X, ℝ) → C(X, ℝ))
    (hrev : ∀ F G, pairing μ F (P G) = pairing μ (P F) G)
    (F : C(X, ℝ)) (k : ℕ) :
    inner ℝ (ContinuousMap.toLp 2 μ ℝ (iterate P k F))
      (ContinuousMap.toLp 2 μ ℝ (iterate P (k + 2) F)) =
        ‖ContinuousMap.toLp 2 μ ℝ (iterate P (k + 1) F)‖ ^ 2 := by
  rw [embedding_pairing, embedding_square]
  exact hrev (iterate P k F) (iterate P (k + 1) F)

/-- The constant C may depend on the observable, the cutoff and the volume.
Only the geometric rate enters the derived one-step Dirichlet inequality. -/
theorem dirichlet_gap (P : C(X, ℝ) → C(X, ℝ))
    (hrev : ∀ F G, pairing μ F (P G) = pairing μ (P F) G)
    (F : C(X, ℝ)) (q C : ℝ) (hq : 0 ≤ q)
    (hdecay : ∀ k, |pairing μ F (iterate P k F)| ≤ C * q ^ k) :
    (1 - q) * (∫ x, F x ^ 2 ∂μ) ≤ ∫ x, F x * (F x - P F x) ∂μ := by
  let u : ℕ → Lp ℝ 2 μ := fun k => ContinuousMap.toLp 2 μ ℝ (iterate P k F)
  have hp : ∀ k, RCLike.re (inner ℝ (u k) (u (k + 2))) = ‖u (k + 1)‖ ^ 2 :=
    adjacent_pairing μ P hrev F
  have hb (k : ℕ) : ‖u k‖ ^ 2 ≤ C * q ^ (2 * k) := by
    change ‖ContinuousMap.toLp 2 μ ℝ (iterate P k F)‖ ^ 2 ≤ _
    rw [embedding_square, iterate_pairing μ P hrev, ← two_mul]
    exact (le_abs_self _).trans (hdecay (2 * k))
  have h := ObservableMomentGap.sequence_quadratic_gap u hp q C hq hb
  change (1 - q) * ‖ContinuousMap.toLp 2 μ ℝ F‖ ^ 2 ≤
    inner ℝ (ContinuousMap.toLp 2 μ ℝ F)
      (ContinuousMap.toLp 2 μ ℝ F - ContinuousMap.toLp 2 μ ℝ (P F)) at h
  rw [← map_sub, embedding_pairing, embedding_square] at h
  simpa only [pairing, ContinuousMap.sub_apply, pow_two] using h

end
end UnifiedTheory.Clay.YangMills.ContinuousUpdateGap
