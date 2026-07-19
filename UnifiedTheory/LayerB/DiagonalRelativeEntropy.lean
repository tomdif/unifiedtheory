/-
  LayerB/DiagonalRelativeEntropy.lean
  ────────────────────────────────────

  Thin vocabulary bridge: the relative entropy of two density
  matrices that are diagonal in the *same* basis is, by definition,
  the classical Kullback–Leibler divergence of their diagonal
  (probability) vectors.

  We do NOT attempt full Umegaki quantum relative entropy here.
  This file just fixes the name

      "diagonal quantum relative entropy" ≡ klDivergence

  so the downstream spectral / DPI / Holevo files can refer to a
  single stable identifier in the diagonal regime, with all the
  scalar identities inherited by `rfl`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `relativeEntropyDiagonal P Q := klDivergence P Q`.
    2. `relativeEntropyDiagonal_eq_kl`               (definitional rfl).
    3. `relativeEntropyDiagonal_self_eq_zero`        (S(ρ‖ρ) = 0).
    4. `relativeEntropyDiagonal_delta`               (delta against Q).
    5. `relativeEntropyDiagonal_uniform`             (vs. uniform).
    6. `relativeEntropyDiagonal_product_add`         (tensor additivity).
    7. `relativeEntropyDiagonal_congr`               (extensionality).
-/

import UnifiedTheory.LayerB.ClassicalRelativeEntropy
import UnifiedTheory.LayerB.DiagonalDensityMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DiagonalRelativeEntropy

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. Definition -/

/-- The diagonal quantum relative entropy: defined as the classical
    KL divergence of the diagonal-entry probability vectors. -/
noncomputable def relativeEntropyDiagonal
    (P Q : ProbabilityVector α) : ℝ :=
  klDivergence P Q

/-! ## 2. The bridge identity (definitional) -/

theorem relativeEntropyDiagonal_eq_kl (P Q : ProbabilityVector α) :
    relativeEntropyDiagonal P Q = klDivergence P Q := rfl

/-! ## 3. Inherited identities -/

/-- **Diagonal quantum relative entropy against itself is zero.** -/
theorem relativeEntropyDiagonal_self_eq_zero (P : ProbabilityVector α) :
    relativeEntropyDiagonal P P = 0 :=
  klDivergence_self_eq_zero P

/-- **Diagonal relative entropy of a delta against an arbitrary
    distribution.** -/
theorem relativeEntropyDiagonal_delta [DecidableEq α]
    (Q : ProbabilityVector α) (i₀ : α) (hQ : Q.p i₀ ≠ 0) :
    relativeEntropyDiagonal (delta α i₀) Q = -Real.log (Q.p i₀) :=
  klDivergence_delta Q i₀ hQ

/-- **Diagonal relative entropy against the maximally-mixed state.** -/
theorem relativeEntropyDiagonal_uniform {n : ℕ}
    (P : ProbabilityVector (Fin n)) (hn : 0 < n) :
    relativeEntropyDiagonal P (uniform n hn)
      = Real.log n - shannonEntropy P :=
  klDivergence_uniform P hn

/-- **Product additivity of diagonal relative entropy.** -/
theorem relativeEntropyDiagonal_product_add
    (P₁ Q₁ : ProbabilityVector α) (P₂ Q₂ : ProbabilityVector β)
    (hAC₁ : IsAbsolutelyContinuous P₁ Q₁)
    (hAC₂ : IsAbsolutelyContinuous P₂ Q₂) :
    relativeEntropyDiagonal (productDistribution P₁ P₂)
                            (productDistribution Q₁ Q₂)
      = relativeEntropyDiagonal P₁ Q₁ + relativeEntropyDiagonal P₂ Q₂ :=
  klDivergence_product_add P₁ Q₁ P₂ Q₂ hAC₁ hAC₂

/-- **Extensionality.** -/
theorem relativeEntropyDiagonal_congr (P P' Q Q' : ProbabilityVector α)
    (hP : ∀ i, P.p i = P'.p i) (hQ : ∀ i, Q.p i = Q'.p i) :
    relativeEntropyDiagonal P Q = relativeEntropyDiagonal P' Q' :=
  klDivergence_congr P P' Q Q' hP hQ

end UnifiedTheory.LayerB.DiagonalRelativeEntropy
