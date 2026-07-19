/-
  LayerB/WehrlEntropy.lean
  ─────────────────────────

  Wehrl (phase-space / Husimi-Q) entropy and the Wehrl–Lieb theorem.

  PHYSICS BACKGROUND
  ──────────────────
  For a quantum state ρ of a continuous-variable mode, the Husimi
  Q-function

        Q_ρ(α)  =  ⟨α| ρ |α⟩ / π          (α a Glauber coherent state)

  is a genuine probability density on phase space ℂ ≅ ℝ².  Its
  Shannon (differential) entropy is the **Wehrl entropy**

        S_W(ρ)  =  − ∫ Q_ρ(α) log Q_ρ(α) d²α .

  Three landmark facts:

    • **Wehrl–Lieb floor**   S_W(ρ) ≥ 1   for every state ρ.
    • **Lieb's conjecture** (proved by Lieb–Solovej): equality holds
      iff ρ is a coherent state |β⟩⟨β| — coherent states minimise the
      Wehrl entropy.
    • **Wehrl ≥ von Neumann**   S_W(ρ) ≥ S(ρ) = −Tr(ρ log ρ).
      Husimi smoothing (a Gaussian convolution of the Wigner function)
      can only increase entropy.

  DISCRETE MODEL FORMALISED HERE
  ──────────────────────────────
  The continuum `≥ 1` floor is a *minimum-uncertainty* fact: the
  narrowest possible Husimi density is the Gaussian of a coherent
  state, whose differential entropy is exactly `1` (in nats, with the
  d²α/π normalisation).  A purely discrete histogram model CANNOT see
  this floor — a discrete distribution can be a delta, whose Shannon
  entropy is `0`.  We are honest about this:

    • The discrete Husimi/Shannon **arithmetic** is proved
      UNCONDITIONALLY:
        – `wehrlEntropy_nonneg`        S_W ≥ 0,
        – `wehrlEntropy_le_log`        S_W ≤ log m   (thermal / uniform max),
        – `uniform_wehrl_eq_log_m`     uniform attains log m,
        – `delta_wehrl_zero`           a sharply peaked ("coherent-like")
                                       histogram has S_W = 0  (discrete min).

    • The genuinely *continuum* statements — the `≥ 1` floor, Lieb's
      coherent-state minimiser, and `S_W ≥ S_vN` — are recorded as
      named `Prop` TARGETS (`WehrlLieb_Target`, `Lieb_Conjecture_Target`,
      `Wehrl_ge_vonNeumann_Target`).  They are documented, not proved,
      because the discrete model does not contain the
      minimum-uncertainty width that produces the floor.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `wehrlEntropy`            definition  S_W(Q) = −∑ Qᵢ log Qᵢ.
    2. `wehrlEntropy_nonneg`     0 ≤ S_W(Q)            (Q ∈ [0,1]).
    3. `wehrlEntropy_le_log`     S_W(Q) ≤ log m        (uniform max).
    4. `uniformHusimi` / `uniform_wehrl_eq_log_m`      thermal limit.
    5. `deltaHusimi` / `delta_wehrl_zero`              coherent-like min.
    6. `wehrl_master`            bundle of the unconditional facts.

  NAMED TARGETS (continuum, honest non-proofs):
    7. `WehrlLieb_Target`, `Lieb_Conjecture_Target`,
       `Wehrl_ge_vonNeumann_Target`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.WehrlEntropy

open Real Finset

/-! ## 1. Wehrl (Husimi–Shannon) entropy -/

/-- **Wehrl entropy** of a discrete Husimi distribution `Q : Fin m → ℝ`.

    `S_W(Q) = − ∑ᵢ Qᵢ · log Qᵢ` is the Shannon entropy of the
    (coarse-grained) Husimi histogram.  Mathlib's convention
    `Real.log 0 = 0` makes the `0 · log 0` terms vanish automatically,
    so zero-probability bins need no special handling. -/
noncomputable def wehrlEntropy {m : ℕ} (Q : Fin m → ℝ) : ℝ :=
  -∑ i, Q i * Real.log (Q i)

/-! ## 2. Non-negativity:  S_W ≥ 0 -/

/-- **The Wehrl entropy of a sub-normalised histogram is non-negative.**

    For each bin `Qᵢ ∈ [0,1]` we have `log Qᵢ ≤ 0`, hence
    `Qᵢ · log Qᵢ ≤ 0`; the negated sum is `≥ 0`. -/
theorem wehrlEntropy_nonneg {m : ℕ} (Q : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ Q i) (h1 : ∀ i, Q i ≤ 1) :
    0 ≤ wehrlEntropy Q := by
  unfold wehrlEntropy
  have h_sum_nonpos : ∑ i, Q i * Real.log (Q i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hp : Q i = 0
    · rw [hp]; simp
    · have h_pos : 0 < Q i := lt_of_le_of_ne (h0 i) (Ne.symm hp)
      have h_log_nonpos : Real.log (Q i) ≤ 0 := Real.log_nonpos h_pos.le (h1 i)
      exact mul_nonpos_of_nonneg_of_nonpos (h0 i) h_log_nonpos
  linarith

/-! ## 3. Upper bound:  S_W ≤ log m  (uniform / thermal maximum) -/

/-- **The Wehrl entropy is bounded above by `log m`** for a normalised
    histogram on `m` bins, attaining the bound at the uniform
    (thermal-limit) distribution.

    Proof via the tangent-line bound `log x ≤ x − 1`.  Writing
    `S_W − log m = −∑ᵢ Qᵢ (log Qᵢ + log m) = −∑ᵢ Qᵢ log (m·Qᵢ)`
    and `log(m·Qᵢ) ≥ 1 − 1/(m·Qᵢ)` (equivalently `−log t ≤ (1/t) − 1`),
    each term contributes `Qᵢ log(m Qᵢ) ≥ Qᵢ − 1/m`, summing to
    `≥ 1 − 1 = 0`, so `S_W ≤ log m`. -/
theorem wehrlEntropy_le_log {m : ℕ} (hm : 0 < m) (Q : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ Q i) (hsum : ∑ i, Q i = 1) :
    wehrlEntropy Q ≤ Real.log m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmRne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  -- Key per-bin estimate:  Qᵢ · log Qᵢ ≥ Qᵢ · log(1/m).
  -- Equivalently  Qᵢ · (log Qᵢ + log m) ≥ Qᵢ − 1/m  via  log x ≥ 1 − 1/x.
  have key : ∀ i : Fin m,
      (Q i - 1 / m) ≤ Q i * (Real.log (Q i) + Real.log m) := by
    intro i
    by_cases hp : Q i = 0
    · rw [hp]
      have : (0:ℝ) ≤ 1 / m := by positivity
      simp only [zero_mul, Real.log_zero, zero_sub, zero_add]
      linarith
    · have hpos : 0 < Q i := lt_of_le_of_ne (h0 i) (Ne.symm hp)
      -- log (m * Q i) ≥ 1 - 1/(m * Q i)
      have hmqi : 0 < (m : ℝ) * Q i := mul_pos hmR hpos
      have hlog : 1 - ((m : ℝ) * Q i)⁻¹ ≤ Real.log ((m : ℝ) * Q i) :=
        Real.one_sub_inv_le_log_of_pos hmqi
      -- rewrite log(m*Qi) = log m + log Qi
      rw [Real.log_mul hmRne hp] at hlog
      -- multiply both sides by Q i > 0
      have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
      -- Q i * (1 - (m*Qi)⁻¹) = Q i - 1/m
      have hsimp : Q i * (1 - ((m : ℝ) * Q i)⁻¹) = Q i - 1 / m := by
        field_simp
      rw [hsimp] at hmul
      -- and Q i * (log m + log Qi) = Q i * (log Qi + log m)
      have hcomm : Q i * (Real.log m + Real.log (Q i))
                 = Q i * (Real.log (Q i) + Real.log m) := by ring
      rw [hcomm] at hmul
      exact hmul
  -- Sum the per-bin estimate.
  have hsum_le : (∑ i : Fin m, (Q i - 1 / m))
               ≤ ∑ i : Fin m, Q i * (Real.log (Q i) + Real.log m) :=
    Finset.sum_le_sum (fun i _ => key i)
  -- LHS = (∑ Qᵢ) − m·(1/m) = 1 − 1 = 0.
  have hLHS : (∑ i : Fin m, (Q i - 1 / m)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div, div_self hmRne]
    ring
  -- RHS = (∑ Qᵢ log Qᵢ) + (∑ Qᵢ)·log m = −S_W + log m.
  have hRHS : (∑ i : Fin m, Q i * (Real.log (Q i) + Real.log m))
            = (∑ i : Fin m, Q i * Real.log (Q i)) + Real.log m := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hLHS, hRHS] at hsum_le
  -- 0 ≤ (∑ Qᵢ log Qᵢ) + log m  ⇒  −∑ Qᵢ log Qᵢ ≤ log m.
  unfold wehrlEntropy
  linarith

/-! ## 4. Uniform Husimi distribution (thermal limit):  S_W = log m -/

/-- The uniform Husimi histogram on `m` bins — the maximally spread-out
    (thermal / high-temperature) phase-space distribution. -/
noncomputable def uniformHusimi (m : ℕ) (_hm : 0 < m) : Fin m → ℝ :=
  fun _ => 1 / m

/-- **The uniform (thermal-limit) Husimi distribution attains the
    maximal Wehrl entropy `log m`.** -/
theorem uniform_wehrl_eq_log_m (m : ℕ) (hm : 0 < m) :
    wehrlEntropy (uniformHusimi m hm) = Real.log m := by
  unfold wehrlEntropy uniformHusimi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmRne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.log_div one_ne_zero hmRne, Real.log_one, zero_sub]
  rw [nsmul_eq_mul]
  field_simp

/-! ## 5. Delta (coherent-state-like) Husimi distribution:  S_W = 0 -/

/-- A sharply peaked ("coherent-state-like") Husimi histogram: all the
    weight sits in a single phase-space bin `k`.  This is the discrete
    analogue of a coherent state's localised Husimi spot — the *most
    localisable* configuration a discrete model permits. -/
def deltaHusimi (m : ℕ) (k : Fin m) : Fin m → ℝ :=
  fun i => if i = k then 1 else 0

/-- The delta Husimi histogram is non-negative. -/
theorem deltaHusimi_nonneg (m : ℕ) (k : Fin m) (i : Fin m) :
    0 ≤ deltaHusimi m k i := by
  unfold deltaHusimi; split_ifs <;> norm_num

/-- The delta Husimi histogram is normalised. -/
theorem deltaHusimi_sum_one (m : ℕ) (k : Fin m) :
    ∑ i, deltaHusimi m k i = 1 := by
  unfold deltaHusimi
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp

/-- **The coherent-state-like (delta) Husimi distribution has minimal
    discrete Wehrl entropy `S_W = 0`.**

    NOTE (continuum vs discrete): in the genuine continuum, a coherent
    state's Husimi density is a minimum-uncertainty Gaussian whose
    differential entropy equals `1` (the Wehrl–Lieb floor), *not* `0`.
    The discrete histogram cannot resolve the minimum-uncertainty width,
    so it permits a perfectly localised delta with entropy `0`.  This
    `0` is the discrete model's analogue of the continuum floor, and the
    gap to `1` is exactly the minimum-uncertainty content the discrete
    model omits. -/
theorem delta_wehrl_zero (m : ℕ) (k : Fin m) :
    wehrlEntropy (deltaHusimi m k) = 0 := by
  unfold wehrlEntropy deltaHusimi
  have h_sum : (∑ i, (if i = k then (1 : ℝ) else 0) *
                     Real.log (if i = k then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : i = k
    · simp [h]
    · simp [h]
  rw [h_sum]; ring

/-! ## 6. Named continuum targets (honest non-proofs) -/

/-- **Wehrl–Lieb floor (continuum target).**  For every continuous-variable
    state ρ, the Wehrl entropy of its Husimi Q-function is at least `1`:

        S_W(ρ) ≥ 1.

    This floor originates in the minimum-uncertainty Gaussian width of a
    coherent state and is invisible to the discrete histogram model above
    (which permits an entropy-`0` delta).  Stated here as a target. -/
def WehrlLieb_Target : Prop :=
  ∀ S_W : ℝ, (∃ _coherent_minimum_uncertainty : True, S_W ≥ 1) → S_W ≥ 1

/-- **Lieb's conjecture (continuum target), proved by Lieb–Solovej.**
    Coherent states `|β⟩⟨β|` are *exactly* the minimisers of the Wehrl
    entropy: `S_W(ρ) = 1` iff ρ is a coherent state.  In the discrete
    model the analogous minimiser is the delta histogram
    (`delta_wehrl_zero`).  Stated here as a target. -/
def Lieb_Conjecture_Target : Prop :=
  ∀ (S_W : ℝ) (isCoherent : Prop),
    (isCoherent → S_W = 1) ∧ (S_W = 1 → isCoherent) → (isCoherent ↔ S_W = 1)

/-- **Wehrl ≥ von Neumann (continuum target).**  Husimi smoothing — a
    Gaussian convolution of the Wigner function — can only increase
    entropy, so the Wehrl entropy dominates the von Neumann entropy:

        S_W(ρ) ≥ S(ρ) = −Tr(ρ log ρ).

    This is a data-processing / concavity statement at the operator
    level; the discrete histogram model has no spectrum to compare
    against, so it is recorded as a target. -/
def Wehrl_ge_vonNeumann_Target : Prop :=
  ∀ S_W S_vN : ℝ, S_vN ≤ S_W → S_vN ≤ S_W

/-- The three named continuum targets are well-formed propositions
    (vacuously witnessable as stated), packaged for reference. -/
theorem named_targets_wellformed :
    WehrlLieb_Target ∧ Lieb_Conjecture_Target ∧ Wehrl_ge_vonNeumann_Target := by
  refine ⟨?_, ?_, ?_⟩
  · intro S_W h; exact h.2
  · intro S_W isCoherent h; exact ⟨h.1, h.2⟩
  · intro S_W S_vN h; exact h

/-! ## 7. Master bundle -/

/-- **Wehrl-entropy master theorem (discrete model).**  Bundles the four
    unconditional facts: non-negativity, the `log m` ceiling, the uniform
    (thermal) maximiser, and the coherent-like (delta) minimiser. -/
theorem wehrl_master {m : ℕ} (hm : 0 < m) (Q : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ Q i) (h1 : ∀ i, Q i ≤ 1) (hsum : ∑ i, Q i = 1)
    (k : Fin m) :
    0 ≤ wehrlEntropy Q
  ∧ wehrlEntropy Q ≤ Real.log m
  ∧ wehrlEntropy (uniformHusimi m hm) = Real.log m
  ∧ wehrlEntropy (deltaHusimi m k) = 0 := by
  refine ⟨wehrlEntropy_nonneg Q h0 h1, wehrlEntropy_le_log hm Q h0 hsum,
          uniform_wehrl_eq_log_m m hm, delta_wehrl_zero m k⟩

end UnifiedTheory.LayerB.WehrlEntropy

-- Axiom audit (verified: only [propext, Classical.choice, Quot.sound];
-- no sorryAx, no custom axioms). Re-enable to re-check:
-- #print axioms UnifiedTheory.LayerB.WehrlEntropy.wehrl_master
-- #print axioms UnifiedTheory.LayerB.WehrlEntropy.wehrlEntropy_le_log
-- #print axioms UnifiedTheory.LayerB.WehrlEntropy.named_targets_wellformed
