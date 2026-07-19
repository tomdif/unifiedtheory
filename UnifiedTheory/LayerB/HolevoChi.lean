/-
  LayerB/HolevoChi.lean
  ──────────────────────

  **Classical / commuting Holevo χ quantity.**  Thin vocabulary
  wrapper around `ClassicalEnsemble.mutualInformation`, exposing
  the two theorems we already proved in the names the operator
  / quantum-information community expects:

      χ(E)  :=  I(E)  =  ∑_a w_a · KL(ρ_a ‖ ρ̄)

      χ(E)  ≥  0                              (Gibbs corollary)
      I(E after T)   ≤   χ(E)                 (DPI for ensembles)

  EXPLICIT SCOPE:
    This file proves only the *classical / commuting / simultaneously
    diagonalised* Holevo precursor.  The full Holevo bound for
    arbitrary non-commuting density matrices requires Umegaki
    relative entropy / operator log / spectral functional calculus,
    none of which are developed in this framework yet.  When that
    later groundwork lands, the classical χ here becomes the
    diagonal restriction of the full χ.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `holevoChiClassical E`                  — definition.
    2. `holevoChiClassical_eq_mutualInformation` (definitional rfl).
    3. `holevoChiClassical_nonneg`             — Gibbs corollary.
    4. `classical_measurement_mutualInformation_le_source_chi`
                                                 — the post-processing
                                                   DPI in χ vocabulary.
-/

import UnifiedTheory.LayerB.ClassicalEnsemble

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoChi

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.Ensemble

variable {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]

/-! ## 1. The classical Holevo χ quantity -/

/-- **Classical Holevo χ.**  The Holevo χ quantity restricted to
    classical / commuting ensembles is the mutual information of
    the ensemble.  Full quantum χ for non-commuting states is
    intentionally NOT defined here. -/
noncomputable def holevoChiClassical (E : ClassicalEnsemble α X) : ℝ :=
  mutualInformation E

/-- Definitional bridge. -/
theorem holevoChiClassical_eq_mutualInformation
    (E : ClassicalEnsemble α X) :
    holevoChiClassical E = mutualInformation E := rfl

/-! ## 2. Non-negativity (Gibbs corollary) -/

/-- **`χ(E) ≥ 0`.**  Direct corollary of Gibbs' inequality applied
    componentwise to the ensemble; zero-weight components vanish
    trivially. -/
theorem holevoChiClassical_nonneg (E : ClassicalEnsemble α X) :
    0 ≤ holevoChiClassical E :=
  mutualInformation_nonneg E

/-! ## 3. Post-processing DPI in χ vocabulary -/

/-- **Classical Holevo precursor (post-processing bound).**  Applying
    a column-stochastic channel `T` to every state of an ensemble
    cannot increase the mutual information beyond the source χ:

      I(E after T)   ≤   χ(E).

    This is the classical / commuting analogue of the Holevo
    bound; the full quantum statement requires Umegaki relative
    entropy and is intentionally deferred. -/
theorem classical_measurement_mutualInformation_le_source_chi
    (E : ClassicalEnsemble α X) (T : StochasticMatrix X Y) :
    mutualInformation (mapStates E T) ≤ holevoChiClassical E :=
  mutualInformation_contracts_under_stochastic E T

/-- The same statement phrased purely in χ vocabulary on both
    sides:  `χ(E after T) ≤ χ(E)`. -/
theorem holevoChiClassical_contracts_under_stochastic
    (E : ClassicalEnsemble α X) (T : StochasticMatrix X Y) :
    holevoChiClassical (mapStates E T) ≤ holevoChiClassical E :=
  mutualInformation_contracts_under_stochastic E T

end UnifiedTheory.LayerB.HolevoChi
