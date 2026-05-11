/-
  LayerB/BornRuleContinuousUniqueness.lean — Born rule unique among
  CONTINUOUS radial observables (closes the polynomial → continuous gap).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — WHAT THIS STRENGTHENS

  `LayerB/BornRuleQuadratic.lean`:
      Born rule unique within the family `(Q² + P²)^n` (n ∈ ℕ).
  `LayerB/BornRulePolynomialUniqueness.lean`:
      Strengthened to ALL finite-degree polynomials in `(Q² + P²)`
      via `Polynomial.eq_zero_of_infinite_isRoot`.

  This file STRENGTHENS again, from polynomials to ALL CONTINUOUS
  radial observables `g(Q² + P²)` with `g : ℝ → ℝ` continuous.
  The Cauchy bridge from the polynomial case (orthogonal additivity
  ⟺ Cauchy on `[0, ∞)`) is reused; the new content is the analytic
  closure step:

      g continuous + g(u + v) = g(u) + g(v) for u, v ≥ 0
      ⟹  g(t) = g(1) · t  for all t ≥ 0.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE FOUR-STEP DENSITY ARGUMENT (standard real analysis)

  1. g(0) = 0                                      (set u = v = 0).
  2. g(n · u) = n · g(u)  for n ∈ ℕ, u ≥ 0          (induction).
  3. g((m/n) · u) = (m/n) · g(u)                    (apply 2 to u/n).
  4. g(r · u) = r · g(u)  for r ≥ 0, u ≥ 0          (rationals dense
        in ℝ + continuity of g).
  5. Set u = 1: g(t) = g(1) · t for t ≥ 0.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  CLOSED in this file:
    * Continuous radial observables `g(Q² + P²)`.
    * The "continuous + Cauchy on [0, ∞) ⟹ linear" step
      (four-step density argument, standard real analysis).

  REMAINING OPEN:
    * Discontinuous (pathological, Hamel-basis-built)
      orthogonally additive radial observables. These exist
      under choice, but require dropping continuity entirely.
    * Full Gleason for ≥ 3-dim Hilbert spaces: a measure-theoretic
      structure theorem requiring projection-lattice machinery,
      a separate multi-week formalization not in scope here.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BornRuleContinuousUniqueness

open Filter Topology

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: CONTINUOUS RADIAL OBSERVABLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A continuous radial observable is a continuous function of the
    squared norm `(Q² + P²)`, packaged as `(Q, P) ↦ g(Q² + P²)`. -/
def IsContinuousRadObs (g : ℝ → ℝ) : Prop := Continuous g

/-- The radial observable on `ℝ²` built from a radial profile `g`. -/
noncomputable def contRadObs (g : ℝ → ℝ) (Q P : ℝ) : ℝ :=
  g (Q ^ 2 + P ^ 2)

/-- **Orthogonal additivity** for the continuous radial observable:
    `obs(a, 0) + obs(0, b) = obs(a, b)` for all real `a, b`. -/
def IsOrthogRadAdditive_continuous (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, contRadObs g a 0 + contRadObs g 0 b = contRadObs g a b

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: CAUCHY BRIDGE
    Same shape as the polynomial case (uses `Real.sq_sqrt` to lift
    from `Q² + P²` parameters to free `u, v ≥ 0`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Orthogonal additivity ⟺ Cauchy's equation for `g` on `[0, ∞)`. -/
theorem orthogRad_iff_cauchy (g : ℝ → ℝ) :
    IsOrthogRadAdditive_continuous g ↔
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) := by
  constructor
  · intro h u v hu hv
    have h' := h (Real.sqrt u) (Real.sqrt v)
    unfold contRadObs at h'
    have h0 : Real.sqrt u ^ 2 + (0 : ℝ) ^ 2 = u := by rw [Real.sq_sqrt hu]; ring
    have h1 : (0 : ℝ) ^ 2 + Real.sqrt v ^ 2 = v := by rw [Real.sq_sqrt hv]; ring
    have h2 : Real.sqrt u ^ 2 + Real.sqrt v ^ 2 = u + v := by
      rw [Real.sq_sqrt hu, Real.sq_sqrt hv]
    rw [h0, h1, h2] at h'
    exact h'
  · intro h a b
    unfold contRadObs
    have hab := h (a^2) (b^2) (sq_nonneg a) (sq_nonneg b)
    have e1 : a^2 + (0:ℝ)^2 = a^2 := by ring
    have e2 : (0:ℝ)^2 + b^2 = b^2 := by ring
    rw [e1, e2]
    exact hab

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: STEP 1 — `g(0) = 0`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 1 of the density argument.** From Cauchy on `[0, ∞)`,
    setting `u = v = 0` yields `g 0 = 0`. -/
theorem cauchy_g_zero (g : ℝ → ℝ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) :
    g 0 = 0 := by
  have h := hC 0 0 le_rfl le_rfl
  -- h : g 0 + g 0 = g (0 + 0)
  have h00 : (0 : ℝ) + 0 = 0 := by ring
  rw [h00] at h
  -- h : g 0 + g 0 = g 0  ⟹  g 0 = 0
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: STEP 2 — `g(n · u) = n · g(u)` for `n : ℕ`, `u ≥ 0`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 2 of the density argument.** By induction on `n : ℕ`,
    Cauchy on `[0, ∞)` gives `g(n · u) = n · g(u)` for `u ≥ 0`. -/
theorem cauchy_nat_mul (g : ℝ → ℝ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    g ((n : ℝ) * u) = (n : ℝ) * g u := by
  induction n with
  | zero =>
    simp [cauchy_g_zero g hC]
  | succ k ih =>
    -- Goal: g ((k+1 : ℕ) * u) = (k+1 : ℕ) * g u
    have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg k) hu
    have hsum : g ((k : ℝ) * u) + g u = g ((k : ℝ) * u + u) := hC _ _ hku hu
    -- (k+1) * u = k * u + u
    have h1 : ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by push_cast; ring
    rw [h1, ← hsum, ih]
    push_cast; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STEP 3a — `g(u / n) = g(u) / n` for `n : ℕ`, `n ≥ 1`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Reciprocal half of Step 3: dividing the input by a positive
    natural divides the output by the same natural. -/
theorem cauchy_div_nat (g : ℝ → ℝ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    g (u / (n : ℝ)) = g u / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hudn : 0 ≤ u / (n : ℝ) := div_nonneg hu (le_of_lt hnpos)
  -- Apply Step 2 to u/n: g(n · (u/n)) = n · g(u/n)
  have h := cauchy_nat_mul g hC n (u / (n : ℝ)) hudn
  -- n * (u/n) = u
  have hcancel : (n : ℝ) * (u / (n : ℝ)) = u := by field_simp
  rw [hcancel] at h
  -- h : g u = n * g (u / n) ⟹ g (u / n) = g u / n
  field_simp
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: STEP 3 — `g((m/n) · u) = (m/n) · g(u)` (nonneg rationals)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 3 of the density argument** (in `m/n` form). For
    `m n : ℕ` with `n ≥ 1`, and `u ≥ 0`,
    `g((m/n) · u) = (m/n) · g(u)`. -/
theorem cauchy_rat_mul_mn (g : ℝ → ℝ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (m n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    g (((m : ℝ) / (n : ℝ)) * u) = ((m : ℝ) / (n : ℝ)) * g u := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  -- (m/n) * u = m * (u / n)
  have hrewrite : ((m : ℝ) / (n : ℝ)) * u = (m : ℝ) * (u / (n : ℝ)) := by
    field_simp
  rw [hrewrite]
  have hudn : 0 ≤ u / (n : ℝ) := div_nonneg hu (le_of_lt hnpos)
  -- Step 2: g(m · (u/n)) = m · g(u/n)
  rw [cauchy_nat_mul g hC m (u / (n : ℝ)) hudn]
  -- Step 3a: g(u/n) = g(u)/n
  rw [cauchy_div_nat g hC n hn u hu]
  field_simp

/-- **Step 3 of the density argument** (in nonneg rational form).
    For `q : ℚ` with `q ≥ 0` and `u ≥ 0`,
    `g(q · u) = q · g(u)`. -/
theorem cauchy_nnrat_mul (g : ℝ → ℝ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (q : ℚ) (hq : 0 ≤ q) (u : ℝ) (hu : 0 ≤ u) :
    g ((q : ℝ) * u) = (q : ℝ) * g u := by
  -- Decompose q = q.num / q.den, with q.num ≥ 0 since q ≥ 0.
  have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  -- q.num.toNat cast back to ℤ equals q.num
  have h_num_cast : ((q.num.toNat : ℤ) : ℝ) = (q.num : ℝ) := by
    have : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum_nn
    exact_mod_cast this
  have h_num_real : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    have := h_num_cast
    push_cast at this ⊢
    exact this
  -- q.den ≥ 1
  have hden_pos : 1 ≤ q.den := q.pos
  -- Apply the m/n form
  have key := cauchy_rat_mul_mn g hC q.num.toNat q.den hden_pos u hu
  -- ((q.num.toNat : ℝ) / (q.den : ℝ)) = (q : ℝ)
  have hq_cast : ((q.num.toNat : ℝ) / (q.den : ℝ)) = (q : ℝ) := by
    rw [h_num_real]
    have hnd : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      have := q.num_div_den
      exact_mod_cast this
    exact hnd
  rw [hq_cast] at key
  exact key

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: STEP 4 — `g(r · u) = r · g(u)` for `r ≥ 0`, `u ≥ 0`
    Density of rationals + continuity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 4 of the density argument.** Continuity of `g` plus the
    rational case (Step 3) gives `g(r · u) = r · g(u)` for `r ≥ 0`,
    `u ≥ 0`. We use a sequence of POSITIVE rationals tending to `r`
    (from above), so the rational case applies. -/
theorem cauchy_real_mul (g : ℝ → ℝ) (hg : Continuous g)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (r : ℝ) (hr : 0 ≤ r) (u : ℝ) (hu : 0 ≤ u) :
    g (r * u) = r * g u := by
  -- Pick a strict-anti rat sequence q_k > r with q_k → r.
  obtain ⟨q, hq_anti, hq_gt, hq_tendsto⟩ := Real.exists_seq_rat_strictAnti_tendsto r
  -- Each cast q_k is > r ≥ 0, so q_k > 0 as a rational.
  have hq_pos : ∀ k, (0 : ℝ) < (q k : ℝ) := fun k => lt_of_le_of_lt hr (hq_gt k)
  have hq_nn_rat : ∀ k, (0 : ℚ) ≤ q k := by
    intro k
    have : (0 : ℝ) ≤ (q k : ℝ) := le_of_lt (hq_pos k)
    exact_mod_cast this
  -- Step 3 at each q k:  g(q_k · u) = q_k · g u
  have hrat : ∀ k, g ((q k : ℝ) * u) = (q k : ℝ) * g u := fun k =>
    cauchy_nnrat_mul g hC (q k) (hq_nn_rat k) u hu
  -- Tendsto (q k * u) → r * u   (multiply by const u)
  have h_arg : Tendsto (fun k => (q k : ℝ) * u) atTop (𝓝 (r * u)) :=
    hq_tendsto.mul_const u
  -- Tendsto g((q k) * u) → g(r * u)   by continuity
  have h_lhs : Tendsto (fun k => g ((q k : ℝ) * u)) atTop (𝓝 (g (r * u))) :=
    (hg.tendsto (r * u)).comp h_arg
  -- Tendsto (q k * g u) → r * g u   (multiply by const g u)
  have h_rhs : Tendsto (fun k => (q k : ℝ) * g u) atTop (𝓝 (r * g u)) :=
    hq_tendsto.mul_const (g u)
  -- The two sequences agree pointwise (by Step 3), so their limits agree.
  have h_eq : (fun k => g ((q k : ℝ) * u)) = (fun k => (q k : ℝ) * g u) :=
    funext hrat
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: STEP 5 — `g(t) = g(1) · t` for `t ≥ 0`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 5 (closure).** Plugging `u = 1` into Step 4: every
    continuous Cauchy-on-`[0,∞)` function is linear on `[0, ∞)`. -/
theorem cauchy_continuous_linear (g : ℝ → ℝ) (hg : Continuous g)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    (t : ℝ) (ht : 0 ≤ t) :
    g t = g 1 * t := by
  have h := cauchy_real_mul g hg hC t ht 1 (by norm_num)
  -- h : g (t * 1) = t * g 1
  have ht1 : t * (1 : ℝ) = t := by ring
  rw [ht1] at h
  -- h : g t = t * g 1
  rw [h]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: BORN RULE FOR CONTINUOUS RADIAL OBSERVABLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MAIN THEOREM: BORN RULE UNIQUENESS OVER CONTINUOUS RADIAL
    OBSERVABLES.** Any continuous, orthogonally additive radial
    observable equals `g(1) · (Q² + P²)`. -/
theorem continuous_born_form (g : ℝ → ℝ) (hg : IsContinuousRadObs g)
    (h : IsOrthogRadAdditive_continuous g) :
    ∀ Q P : ℝ, contRadObs g Q P = g 1 * (Q ^ 2 + P ^ 2) := by
  intro Q P
  unfold contRadObs
  have hC := (orthogRad_iff_cauchy g).mp h
  have hsum_nn : 0 ≤ Q ^ 2 + P ^ 2 := by positivity
  exact cauchy_continuous_linear g hg hC (Q ^ 2 + P ^ 2) hsum_nn

/-- The Born rule profile `g(t) = c · t` IS continuous and IS
    orthogonally additive — confirming the conclusion is reached. -/
theorem born_profile_satisfies (c : ℝ) :
    IsContinuousRadObs (fun t => c * t) ∧
    IsOrthogRadAdditive_continuous (fun t => c * t) := by
  refine ⟨?_, ?_⟩
  · exact continuous_const.mul continuous_id
  · intro a b
    unfold contRadObs
    ring

/-- **Faithful master theorem (continuous version).** Bundles all
    five steps of the density argument and the closure. -/
theorem continuous_born_master (g : ℝ → ℝ) :
    -- (1) Cauchy bridge
    (IsOrthogRadAdditive_continuous g ↔
     ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v))
    -- (2) Step 1: Cauchy ⟹ g 0 = 0
    ∧ ((∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) → g 0 = 0)
    -- (3) Step 2: Cauchy ⟹ g(n · u) = n · g u for n : ℕ, u ≥ 0
    ∧ ((∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) →
        ∀ (n : ℕ) (u : ℝ), 0 ≤ u → g ((n : ℝ) * u) = (n : ℝ) * g u)
    -- (4) Step 3: Cauchy ⟹ g(q · u) = q · g u for q : ℚ, q ≥ 0, u ≥ 0
    ∧ ((∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) →
        ∀ (q : ℚ), 0 ≤ q → ∀ (u : ℝ), 0 ≤ u →
          g ((q : ℝ) * u) = (q : ℝ) * g u)
    -- (5) Step 4: Continuity + Cauchy ⟹ g(r · u) = r · g u for r, u ≥ 0
    ∧ (Continuous g → (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) →
        ∀ (r : ℝ), 0 ≤ r → ∀ (u : ℝ), 0 ≤ u → g (r * u) = r * g u)
    -- (6) THE CLOSURE: g(t) = g(1) · t for t ≥ 0
    ∧ (Continuous g → (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → g u + g v = g (u + v)) →
        ∀ t : ℝ, 0 ≤ t → g t = g 1 * t)
    -- (7) THE BORN-RULE FORM
    ∧ (IsContinuousRadObs g → IsOrthogRadAdditive_continuous g →
        ∀ Q P : ℝ, contRadObs g Q P = g 1 * (Q ^ 2 + P ^ 2)) :=
  ⟨orthogRad_iff_cauchy g,
   cauchy_g_zero g,
   fun hC n u hu => cauchy_nat_mul g hC n u hu,
   fun hC q hq u hu => cauchy_nnrat_mul g hC q hq u hu,
   fun hg hC r hr u hu => cauchy_real_mul g hg hC r hr u hu,
   fun hg hC t ht => cauchy_continuous_linear g hg hC t ht,
   fun hg h => continuous_born_form g hg h⟩

end UnifiedTheory.LayerB.BornRuleContinuousUniqueness
