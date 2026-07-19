/-
  LayerB/GibbsInequality.lean
  ────────────────────────────

  **Gibbs' inequality** as a direct corollary of the log-sum
  inequality (`LogSumInequality.lean`): the classical KL divergence
  between two probability vectors satisfying the absolute-continuity
  condition is non-negative.  This is the missing keystone for the
  entire entropy stack — the natural positivity fact for relative
  entropy in every vocabulary layer.

  Proof (4 lines):
      ∑ klTerm (P_i) (Q_i)
        ≥ klTerm (∑ P_i) (∑ Q_i)      [log-sum]
        = klTerm 1 1                     [sum_one for P, Q]
        = 0                              [klTerm_self at p = 1]

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `klTerm_one_one`                          — klTerm 1 1 = 0.
    2. `klDivergence_nonneg_of_ac`               — the keystone:
                                                    KL(P‖Q) ≥ 0.
    3. `relativeEntropyDiagonal_nonneg_of_ac`    — bridge.
    4. `relativeEntropySpectral_nonneg_of_ac`    — bridge.
    5. `measurement_relativeEntropy_nonneg_of_ac` — bridge for
                                                    quantum-to-classical.
-/

import UnifiedTheory.LayerB.LogSumInequality
import UnifiedTheory.LayerB.MeasurementChannel

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GibbsInequality

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.DiagonalRelativeEntropy
open UnifiedTheory.LayerB.SpectralRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.MeasurementChannel
open UnifiedTheory.LayerB.LogSumInequality

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. `klTerm 1 1 = 0` -/

@[simp]
theorem klTerm_one_one : klTerm 1 1 = 0 := klTerm_self 1

/-! ## 2. The Gibbs inequality (KL ≥ 0) -/

/-- **Gibbs' inequality.**  Under absolute continuity `P ≪ Q`, the
    classical Kullback–Leibler divergence is non-negative:

      0   ≤   KL(P ‖ Q).

    Direct consequence of the log-sum inequality applied to the
    component probability vectors, since both sum to 1. -/
theorem klDivergence_nonneg_of_ac
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q) :
    0 ≤ klDivergence P Q := by
  -- log-sum: klTerm (∑ P_i) (∑ Q_i) ≤ ∑ klTerm (P_i) (Q_i)
  have h_logsum := log_sum_real P.p Q.p P.nonneg Q.nonneg hAC
  -- Normalize: ∑ P_i = 1, ∑ Q_i = 1
  rw [P.sum_one, Q.sum_one, klTerm_one_one] at h_logsum
  -- h_logsum : 0 ≤ ∑ i, klTerm (P.p i) (Q.p i)  =  klDivergence P Q
  exact h_logsum

/-! ## 3. Bridge: diagonal quantum relative entropy ≥ 0 -/

/-- **Diagonal quantum relative entropy is non-negative under AC.** -/
theorem relativeEntropyDiagonal_nonneg_of_ac
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q) :
    0 ≤ relativeEntropyDiagonal P Q :=
  klDivergence_nonneg_of_ac P Q hAC

/-! ## 4. Bridge: spectral / common-basis relative entropy ≥ 0 -/

/-- **Common-eigenbasis spectral relative entropy is non-negative
    under AC of the eigenvalue probability vectors.** -/
theorem relativeEntropySpectral_nonneg_of_ac {n : ℕ}
    (S : CommonSpectralPair n)
    (hAC : IsAbsolutelyContinuous S.ρ.spectrum S.σ.spectrum) :
    0 ≤ relativeEntropySpectral S :=
  klDivergence_nonneg_of_ac S.ρ.spectrum S.σ.spectrum hAC

/-! ## 5. Bridge: measurement outcome KL ≥ 0 -/

/-- **The KL divergence between two measurement outcome distributions
    is non-negative under AC of the input distributions.**  The
    measurement DPI plus Gibbs sandwiches the outcome divergence
    between 0 and the spectral relative entropy of the input pair. -/
theorem measurement_relativeEntropy_nonneg_of_ac {n : ℕ}
    (T : StochasticMatrix (Fin n) β)
    (S : CommonSpectralPair n)
    (hAC : IsAbsolutelyContinuous S.ρ.spectrum S.σ.spectrum) :
    0 ≤ klDivergence (measureSpectral T S.ρ) (measureSpectral T S.σ) := by
  -- The pushforward preserves absolute continuity:
  --   (T·P)_b ≠ 0 ⟹ ∃ a, T(b,a)·P_a ≠ 0
  --             ⟹ ∃ a, T(b,a) ≠ 0 ∧ P_a ≠ 0
  --             ⟹ ∃ a, T(b,a) ≠ 0 ∧ Q_a ≠ 0  (by AC)
  --             ⟹ (T·Q)_b ≠ 0  (positive contribution).
  apply klDivergence_nonneg_of_ac
  intro b hTP_ne
  -- hTP_ne : (T.push S.ρ.spectrum).p b ≠ 0
  --        i.e. ∑ a, T.M b a * S.ρ.spectrum.p a ≠ 0
  -- Show ∑ a, T.M b a * S.σ.spectrum.p a ≠ 0.
  -- Equivalently: not all summands of (T·Q)_b are zero.
  -- From (T·P)_b ≠ 0: some summand T.M b a * P_a is nonzero,
  -- hence T.M b a ≠ 0 ∧ P_a ≠ 0; by AC Q_a ≠ 0; so T.M b a * Q_a ≠ 0;
  -- the corresponding RHS summand is > 0, so the sum is > 0.
  change ∑ a, T.M b a * S.σ.spectrum.p a ≠ 0
  -- Extract a nonzero index from (T·P)_b ≠ 0
  have h_exists : ∃ a, T.M b a * S.ρ.spectrum.p a ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    apply hTP_ne
    change ∑ a, T.M b a * S.ρ.spectrum.p a = 0
    exact Finset.sum_eq_zero (fun a _ => h_all a)
  obtain ⟨a₀, ha₀⟩ := h_exists
  obtain ⟨hT, hP⟩ := mul_ne_zero_iff.mp ha₀
  have hQ : S.σ.spectrum.p a₀ ≠ 0 := hAC a₀ hP
  have h_TQa₀_pos : 0 < T.M b a₀ * S.σ.spectrum.p a₀ :=
    lt_of_le_of_ne
      (mul_nonneg (T.nonneg b a₀) (S.σ.spectrum.nonneg a₀))
      (Ne.symm (mul_ne_zero hT hQ))
  have h_sum_nn : ∀ a ∈ Finset.univ,
      0 ≤ T.M b a * S.σ.spectrum.p a := fun a _ =>
    mul_nonneg (T.nonneg b a) (S.σ.spectrum.nonneg a)
  have h_sum_pos : 0 < ∑ a, T.M b a * S.σ.spectrum.p a :=
    Finset.sum_pos' h_sum_nn ⟨a₀, Finset.mem_univ _, h_TQa₀_pos⟩
  exact ne_of_gt h_sum_pos

end UnifiedTheory.LayerB.GibbsInequality
