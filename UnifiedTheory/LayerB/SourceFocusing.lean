/-
  LayerB/SourceFocusing.lean — Source sign controls focusing behavior

  Connects the signed source algebra to gravitational behavior
  via a named hypothesis (FocusingHypothesis).

  Under this hypothesis:
    Q > 0 → focusing (attractive gravity)
    Q < 0 → defocusing (repulsive gravity)
    Q = 0 → neutral
    Screening reduces focusing, cancellation eliminates it.
-/
import UnifiedTheory.LayerB.SignedSource

namespace UnifiedTheory.LayerB.SourceFocusing

open SignedSource MetricDefects

/-- **FocusingHypothesis**: source charge controls Ricci focusing.
    There exists κ > 0 such that the focusing contribution of a
    perturbation h is κ · Q(h). Named hypothesis, not an axiom. -/
structure FocusingHypothesis (m : ℕ) where
  κ : ℝ
  hκ : 0 < κ

variable {m : ℕ}

/-- The focusing of a perturbation under the hypothesis. -/
noncomputable def focusing (F : FocusingHypothesis m) (h : Perturbation (m + 2)) : ℝ :=
  F.κ * Q h

/-- **POSITIVE SOURCE FOCUSES.** Q > 0 → focusing > 0. -/
theorem positive_source_focuses (F : FocusingHypothesis m)
    (h : Perturbation (m + 2)) (hp : 0 < Q h) :
    0 < focusing F h :=
  mul_pos F.hκ hp

/-- **NEGATIVE SOURCE DEFOCUSES.** Q < 0 → focusing < 0. -/
theorem negative_source_defocuses (F : FocusingHypothesis m)
    (h : Perturbation (m + 2)) (hn : Q h < 0) :
    focusing F h < 0 :=
  mul_neg_of_pos_of_neg F.hκ hn

/-- **NEUTRAL SOURCE IS INERT.** Q = 0 → focusing = 0. -/
theorem neutral_source_inert (F : FocusingHypothesis m)
    (h : Perturbation (m + 2)) (hz : Q h = 0) :
    focusing F h = 0 := by
  simp [focusing, hz]

/-- **CANCELLATION ELIMINATES FOCUSING.** h + (-h) → focusing = 0. -/
theorem cancellation_eliminates_focusing (F : FocusingHypothesis m)
    (h : Perturbation (m + 2)) :
    focusing F (h + (-h)) = 0 := by
  unfold focusing
  rw [perfect_cancellation, mul_zero]

/-- **SCREENING REDUCES FOCUSING.**
    Opposite signs reduce the focusing magnitude. -/
theorem screening_reduces_focusing (F : FocusingHypothesis m)
    (h₁ h₂ : Perturbation (m + 2))
    (hp : 0 < Q h₁) (hn : Q h₂ < 0) :
    focusing F (h₁ + h₂) < focusing F h₁ := by
  simp only [focusing]
  have := partial_screening h₁ h₂ hp hn
  exact mul_lt_mul_of_pos_left this F.hκ

/-- **OVERSCREENING REVERSES FOCUSING.**
    Excess negative source → net repulsive. -/
theorem overscreening_reverses_focusing (F : FocusingHypothesis m)
    (h₁ h₂ : Perturbation (m + 2))
    (hp : 0 < Q h₁) (hn : Q h₂ < 0) (hlarge : Q h₁ < -(Q h₂)) :
    focusing F (h₁ + h₂) < 0 := by
  simp only [focusing]
  exact mul_neg_of_pos_of_neg F.hκ (overscreening h₁ h₂ hp hn hlarge)

/-- **FOCUSING IS ADDITIVE.** -/
theorem focusing_additive (F : FocusingHypothesis m)
    (h₁ h₂ : Perturbation (m + 2)) :
    focusing F (h₁ + h₂) = focusing F h₁ + focusing F h₂ := by
  simp [focusing, Q_add, mul_add]

end UnifiedTheory.LayerB.SourceFocusing
