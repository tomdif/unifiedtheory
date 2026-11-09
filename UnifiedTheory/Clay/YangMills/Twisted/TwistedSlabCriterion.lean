/- A finite-size criterion for the flux ratio on `ℤ² × T²_{L⊥}`. No spectral input is needed.

Keep the two transverse sides fixed at `L⊥` and double only the two in-plane directions:
`(L, L, L⊥, L⊥) → (2L, L, L⊥, L⊥) → (2L, 2L, L⊥, L⊥)`. Then:

* The in-plane steps are `y' ≤ K y²` (`TwistedFluxRecursion.four_step`), with `K ≤ 2 Kper` (`TwistedThermalExcess`).
* `log Kper` is the split/join interpolation integral `β ∫ ⟨Σ_bnd (P_split − P_joined)⟩ dλ`, over `N` boundary plaquettes
  with `|P| ≤ 1`. So `log Kper ≤ 2βN`, and `N = 6 · (layer size)`: `6 L L⊥²` for the first step and `12 L L⊥²` for the
  second. This is an elementary bound; the identification is by hand.
* Hence `m_k = log(K₁² K₂) ≤ 3 log 2 + 48 β L⊥² L_k`. This grows LINEARLY in `L_k = 2^k L₀` (`q = 2 < 4`), so
  `TwistedSubArea.area_law_growing` applies with `A = 3 log 2` and `B = 48 β L⊥² L₀`.

`slab_criterion`: if one finite box satisfies `y(L₀) < ½ e^{-24 β L⊥² L₀}`, then
`y(2^k L₀) ≤ exp(−4^k δ)` with `δ = −log y(L₀) − log 2 − 24 β L⊥² L₀ > 0`: area-type decay on `ℤ² × T²_{L⊥}`.
Conversely, if `y(L) ~ e^{−σ L²}` with `σ > 0`, the criterion holds for every large `L₀`. So it is a finite-size
criterion.

The transverse sides cannot grow under these bounds: a transverse step costs `β · L² L⊥`, area times `L⊥`, which is
beyond sub-area (`TwistedFluxBasis`). So this does NOT reach `ℝ⁴`. -/
import Mathlib
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSlabCriterion

open UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea

/-- Log form of one doubling: `0 < y`, `0 < M`, `y' ≤ M y⁴` give `4 (−log y) − log M ≤ −log y'`
(for `y' > 0`). -/
theorem log_step {y y' M : ℝ} (hy : 0 < y) (hy' : 0 < y') (hM : 0 < M) (h : y' ≤ M * y ^ 4) :
    4 * (-Real.log y) - Real.log M ≤ -Real.log y' := by
  have := Real.log_le_log hy' h
  rw [Real.log_mul hM.ne' (by positivity), Real.log_pow] at this
  push_cast at this; linarith

/-- The slab criterion, in log variables: with `u (k+1) ≥ 4 u k − m k` and `m k ≤ A + B 2^k`, one gets
`u k ≥ 4^k (u 0 − A/3 − B/2)`. -/
theorem slab_criterion (u m : ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : ∀ j, m j ≤ A + B * 2 ^ j) (h : ∀ k, 4 * u k - m k ≤ u (k + 1)) (k : ℕ) :
    (4 : ℝ) ^ k * (u 0 - (A / 3 + B / 2)) ≤ u k := by
  have := area_law_growing u m hA hB (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) hm h k
  norm_num at this ⊢; linarith

end UnifiedTheory.Clay.YangMills.Twisted.TwistedSlabCriterion
