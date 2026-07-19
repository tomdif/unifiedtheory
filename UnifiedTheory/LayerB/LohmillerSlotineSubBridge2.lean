/-
  LayerB/LohmillerSlotineSubBridge2.lean — Sub-bridge 2 of continuumLimitOfKP

  HAUPTVERMUTUNG METRIC  →  LAPLACIAN CONTROL.

  Following the three-sub-bridge plan from
  `LohmillerSlotineContinuumLimit.lean`:

    "For a sequence of causal-set/Hauptvermutung approximants with the
     right regularity assumptions, the discrete operator appearing in
     K/P converges on smooth test functions to the metric Laplacian
     of the emergent manifold."

  Concrete plan executed here:
    • assumption-heavy on purpose,
    • weak / test-function form,
    • chartwise locality (single chart at a time),
    • first true milestone:  uniform-on-compacts ⟹ pointwise (weak chartwise).

  Then a CONCRETE TARGET:  the 1D centered finite-difference Laplacian
  D_h[φ](x) := (φ(x+h) + φ(x-h) - 2 φ(x))/h²  is the simplest meaningful
  discrete Laplacian.  Its convergence to ∂_x²[φ](x) for smooth φ is the
  standard finite-difference result.  Stated here as the first
  non-trivial concrete convergence sought; the proof requires Mathlib
  Taylor / L'Hôpital machinery and is the next-session target.

  Zero sorry.  Zero custom axioms (beyond the standard `propext`,
  `Classical.choice`, `Quot.sound` set).
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineSubBridge2

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — ABSTRACT FRAMEWORK
    ════════════════════════════════════════════════════════════════════════ -/

/-- A family of discrete Laplacian-type operators indexed by ℕ (the
    sprinkling-density / lattice-scale parameter).  Each `op n` is
    a function `(X → ℝ) → (X → ℝ)` mapping a scalar field to its
    discrete Laplacian at scale n. -/
structure DiscreteLaplacianFamily (X : Type*) where
  op : ℕ → (X → ℝ) → (X → ℝ)

/-- An abstract metric Laplace-Beltrami operator.  No regularity
    encoded at this level — supply as needed in convergence statements. -/
structure MetricLaplacian (X : Type*) where
  Δ : (X → ℝ) → (X → ℝ)

/-- A test function on X.  Smoothness/support assumptions are kept
    abstract at this layer — the convergence theorems below take
    them as hypotheses. -/
structure TestFunction (X : Type*) where
  φ : X → ℝ

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — CONVERGENCE NOTIONS
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Weak chartwise (pointwise) convergence**:

    For every test function φ and every point p in the chart,
    `D.op n φ p → M.Δ φ p` as n → ∞.

    Weakest natural convergence notion: pointwise on test functions
    within a single chart. -/
def WeakChartwiseConvergence {X : Type*}
    (D : DiscreteLaplacianFamily X) (M : MetricLaplacian X)
    (chart : Set X) : Prop :=
  ∀ (φ : TestFunction X), ∀ p ∈ chart,
    Filter.Tendsto (fun n => D.op n φ.φ p) Filter.atTop
      (nhds (M.Δ φ.φ p))

/-- **Uniform-on-compacts convergence**:

    For every test function φ and every compact subset K ⊆ chart,
    `sup_{p ∈ K} |D.op n φ p − M.Δ φ p| → 0` as n → ∞.

    Strictly stronger than pointwise. -/
def UniformOnCompactsConvergence {X : Type*} [TopologicalSpace X]
    (D : DiscreteLaplacianFamily X) (M : MetricLaplacian X)
    (chart : Set X) : Prop :=
  ∀ (φ : TestFunction X), ∀ K : Set X, IsCompact K → K ⊆ chart →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ p ∈ K,
      |D.op n φ.φ p - M.Δ φ.φ p| < ε

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — FIRST REAL THEOREM: UNIFORM-ON-COMPACTS ⟹ WEAK CHARTWISE
    ════════════════════════════════════════════════════════════════════════ -/

/-- **THEOREM (first real bridge result)**:

    Uniform-on-compacts convergence on a chart implies the
    pointwise / weak chartwise convergence on that chart.

    Proof: for any single point p ∈ chart, take K = {p} (singleton
    is compact); the uniform-on-K bound at p collapses to the pointwise
    bound.  This is the basic relationship between the stronger and
    weaker convergence notions in the sub-bridge 2 hierarchy. -/
theorem uniformOnCompacts_implies_weakChartwise
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (D : DiscreteLaplacianFamily X) (M : MetricLaplacian X)
    (chart : Set X)
    (h : UniformOnCompactsConvergence D M chart) :
    WeakChartwiseConvergence D M chart := by
  intro φ p hp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h φ {p} (isCompact_singleton)
    (Set.singleton_subset_iff.mpr hp) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hbd : |D.op n φ.φ p - M.Δ φ.φ p| < ε := hN n hn p rfl
  rwa [Real.dist_eq]

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — CONCRETE 1D FINITE-DIFFERENCE LAPLACIAN

    The simplest meaningful discrete Laplacian: centered second
    difference on a 1D uniform lattice.  Stated as the FIRST CONCRETE
    CONVERGENCE TARGET for sub-bridge 2.
    ════════════════════════════════════════════════════════════════════════ -/

/-- The 1D centered finite-difference Laplacian operator at scale h:
        D_h[φ](x) := (φ(x+h) + φ(x-h) - 2·φ(x)) / h².

    For smooth φ, by Taylor expansion this equals  φ''(x) + O(h²)  as
    h → 0.  This file states the convergence but defers the proof
    (which requires Mathlib's Taylor or L'Hôpital machinery). -/
noncomputable def fdLaplacian1D (h : ℝ) : (ℝ → ℝ) → (ℝ → ℝ) :=
  fun φ x => (φ (x + h) + φ (x - h) - 2 * φ x) / h ^ 2

/-- The 1D continuum metric Laplacian (flat 1D metric):  Δ_g = ∂_x². -/
noncomputable def laplacian1D : (ℝ → ℝ) → (ℝ → ℝ) :=
  fun φ => deriv (deriv φ)

/-- Bundle the centered finite-difference operator family at scales
    `h n` (with `h n → 0`) as a `DiscreteLaplacianFamily ℝ`. -/
noncomputable def fdLaplacian1DFamily (h : ℕ → ℝ) : DiscreteLaplacianFamily ℝ where
  op := fun n φ x => fdLaplacian1D (h n) φ x

/-- The 1D metric Laplacian, bundled. -/
noncomputable def metricLaplacian1D : MetricLaplacian ℝ where
  Δ := laplacian1D

/-- **CONCRETE CONVERGENCE TARGET** (stated, proof deferred).

    For sufficiently smooth φ at x, the centered finite-difference
    Laplacian on a positive sequence `h n → 0` converges to the
    second derivative `φ''(x)`:

        lim_{n→∞} (φ(x+hₙ) + φ(x−hₙ) − 2·φ(x)) / hₙ² = φ''(x).

    This is the standard finite-difference result.  Proof requires
    Mathlib Taylor or L'Hôpital wiring;  pre-registered here as the
    first non-trivial concrete convergence target for sub-bridge 2. -/
def FiniteDifferenceLaplacian1D_ConvergesAt (φ : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ (h_seq : ℕ → ℝ),
    (∀ n, 0 < h_seq n) →
    Filter.Tendsto h_seq Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => fdLaplacian1D (h_seq n) φ x)
      Filter.atTop (nhds (laplacian1D φ x))

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.5 — FIRST CONCRETE WITNESS: QUADRATIC POLYNOMIALS

    The centered finite-difference Laplacian is EXACT (no error term)
    on quadratic polynomials  φ(y) = a y² + b y + c.  Both
    `fdLaplacian1D h φ x` and `laplacian1D φ x` evaluate to `2a` for
    all `h ≠ 0` and all `x`.  This gives a concrete first instance of
    `FiniteDifferenceLaplacian1D_ConvergesAt`: convergence is trivial
    because the two operators coincide pointwise.

    For higher-degree polynomials there is a non-zero `O(h²)` error
    and convergence requires limit-taking;  for general `ContDiff ℝ 2`
    test functions Taylor-with-Lagrange-remainder closes the
    convergence.  Both are deferred future targets.
    ════════════════════════════════════════════════════════════════════════ -/

/-- The centered finite-difference Laplacian of a quadratic polynomial
    equals `2a` for any `h ≠ 0`.  Algebraic identity: the discrete
    operator is EXACT on quadratics. -/
theorem fdLaplacian1D_quadratic (a b c h : ℝ) (h_ne : h ≠ 0) (x : ℝ) :
    fdLaplacian1D h (fun y => a * y ^ 2 + b * y + c) x = 2 * a := by
  unfold fdLaplacian1D
  have h2_ne : h ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  field_simp
  ring

/-- The first derivative of a quadratic:
        d/dy (a y² + b y + c) = 2 a y + b. -/
theorem deriv_quadratic (a b c : ℝ) :
    deriv (fun y : ℝ => a * y ^ 2 + b * y + c) = fun y => 2 * a * y + b := by
  ext y
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    have h := hasDerivAt_pow 2 y
    convert h using 1
    push_cast
    ring
  have h1 : HasDerivAt (fun z : ℝ => a * z ^ 2) (2 * a * y) y := by
    have := hsq.const_mul a
    convert this using 1
    ring
  have h2 : HasDerivAt (fun z : ℝ => b * z) b y := by
    have := (hasDerivAt_id y).const_mul b
    convert this using 1
    ring
  have h3 : HasDerivAt (fun z : ℝ => a * z ^ 2 + b * z + c) (2 * a * y + b) y :=
    (h1.add h2).add_const c
  exact h3.deriv

/-- The continuum Laplacian (= second derivative) of a quadratic
    polynomial is the constant `2a`. -/
theorem laplacian1D_quadratic (a b c : ℝ) (x : ℝ) :
    laplacian1D (fun y => a * y ^ 2 + b * y + c) x = 2 * a := by
  change deriv (deriv (fun y : ℝ => a * y ^ 2 + b * y + c)) x = 2 * a
  rw [deriv_quadratic]
  -- Goal: deriv (fun y => 2 * a * y + b) x = 2 * a
  have h1 : HasDerivAt (fun y : ℝ => 2 * a * y) (2 * a) x := by
    have := (hasDerivAt_id x).const_mul (2 * a)
    convert this using 1
    ring
  exact (h1.add_const b).deriv

/-- **CONCRETE WITNESS**: discrete and continuum Laplacian agree on
    quadratic polynomials, exactly (not just in the limit). -/
theorem fdLaplacian1D_eq_laplacian1D_quadratic
    (a b c h : ℝ) (h_ne : h ≠ 0) (x : ℝ) :
    fdLaplacian1D h (fun y => a * y ^ 2 + b * y + c) x
      = laplacian1D (fun y => a * y ^ 2 + b * y + c) x := by
  rw [fdLaplacian1D_quadratic a b c h h_ne x, laplacian1D_quadratic a b c x]

/-- **`FiniteDifferenceLaplacian1D_ConvergesAt` holds for quadratic
    polynomials** — the first concrete instance of the convergence
    target.

    Proof: for quadratics the centered fd Laplacian equals the
    continuum Laplacian for EVERY positive h, so convergence is
    trivial (constant sequence to the same constant). -/
theorem fdLaplacian1D_converges_quadratic (a b c : ℝ) (x : ℝ) :
    FiniteDifferenceLaplacian1D_ConvergesAt
      (fun y => a * y ^ 2 + b * y + c) x := by
  intro h_seq h_pos _
  rw [laplacian1D_quadratic]
  -- Goal: Tendsto (fun n => fdLaplacian1D (h_seq n) (...) x) atTop (𝓝 (2 * a))
  have hconst : ∀ n,
      fdLaplacian1D (h_seq n) (fun y => a * y ^ 2 + b * y + c) x = 2 * a := by
    intro n
    exact fdLaplacian1D_quadratic a b c (h_seq n) (ne_of_gt (h_pos n)) x
  have heq : (fun n => fdLaplacian1D (h_seq n)
              (fun y => a * y ^ 2 + b * y + c) x) = (fun _ => 2 * a) := by
    funext n; exact hconst n
  rw [heq]
  exact tendsto_const_nhds

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.6 — SECOND CONCRETE WITNESS: QUARTIC POLYNOMIALS (NON-EXACT)

    For quadratics the discrete operator was EXACT — no error term.
    For quartic polynomials there IS an O(h²) error term:

        fdLaplacian1D h (a y⁴) x = 12 a x² + 2 a h²
        laplacian1D (a y⁴) x = 12 a x²

    so the difference  fdLaplacian1D − laplacian1D = 2 a h²  vanishes
    only in the limit h → 0.  This is the first non-trivial test of
    the `FiniteDifferenceLaplacian1D_ConvergesAt` machinery, exercising
    `Filter.Tendsto.add` and `(h_seq n)^2 → 0`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- The centered finite-difference Laplacian of a quartic polynomial:
        fdLaplacian1D h (a y⁴) x = 12 a x² + 2 a h². -/
theorem fdLaplacian1D_quartic (a x h : ℝ) (h_ne : h ≠ 0) :
    fdLaplacian1D h (fun y => a * y ^ 4) x = 12 * a * x ^ 2 + 2 * a * h ^ 2 := by
  unfold fdLaplacian1D
  have h2_ne : h ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  field_simp
  ring

/-- The first derivative of a y⁴:  d/dy (a y⁴) = 4 a y³. -/
theorem deriv_quartic (a : ℝ) :
    deriv (fun y : ℝ => a * y ^ 4) = fun y => 4 * a * y ^ 3 := by
  ext y
  have hp : HasDerivAt (fun z : ℝ => z ^ 4) (4 * y ^ 3) y := by
    exact hasDerivAt_pow 4 y
  have h1 : HasDerivAt (fun z : ℝ => a * z ^ 4) (4 * a * y ^ 3) y := by
    have := hp.const_mul a
    convert this using 1
    ring
  exact h1.deriv

/-- The first derivative of 4 a y³:  d/dy (4 a y³) = 12 a y².
    (Used as the second-derivative step for `laplacian1D (a y⁴)`.) -/
theorem deriv_4ay3 (a : ℝ) :
    deriv (fun y : ℝ => 4 * a * y ^ 3) = fun y => 12 * a * y ^ 2 := by
  ext y
  have hp : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y := by
    exact hasDerivAt_pow 3 y
  have h1 : HasDerivAt (fun z : ℝ => 4 * a * z ^ 3) (12 * a * y ^ 2) y := by
    have := hp.const_mul (4 * a)
    convert this using 1
    ring
  exact h1.deriv

/-- The continuum Laplacian (= second derivative) of a y⁴ at x is 12 a x². -/
theorem laplacian1D_quartic (a x : ℝ) :
    laplacian1D (fun y => a * y ^ 4) x = 12 * a * x ^ 2 := by
  change deriv (deriv (fun y : ℝ => a * y ^ 4)) x = 12 * a * x ^ 2
  rw [deriv_quartic, deriv_4ay3]

/-- **CONCRETE WITNESS (with non-zero h² error term)**:
    `FiniteDifferenceLaplacian1D_ConvergesAt` holds for quartics
    `φ(y) = a y⁴`.

    Unlike the quadratic case, this convergence is non-trivial:
    `fdLaplacian1D` deviates from `laplacian1D` by the term  `2 a h²`,
    which only vanishes in the h → 0 limit.  Closes the first
    convergence instance involving an actual limit-taking step. -/
theorem fdLaplacian1D_converges_quartic (a x : ℝ) :
    FiniteDifferenceLaplacian1D_ConvergesAt (fun y => a * y ^ 4) x := by
  intro h_seq h_pos h_tendsto
  rw [laplacian1D_quartic]
  -- Reduce the sequence to the explicit form  12 a x² + 2 a (h_seq n)²
  have heq : (fun n => fdLaplacian1D (h_seq n) (fun y => a * y ^ 4) x)
             = (fun n => 12 * a * x ^ 2 + 2 * a * (h_seq n) ^ 2) := by
    funext n
    exact fdLaplacian1D_quartic a x (h_seq n) (ne_of_gt (h_pos n))
  rw [heq]
  -- (h_seq n)² → 0  via  Filter.Tendsto.pow
  have h_pow : Filter.Tendsto (fun n => (h_seq n) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using h_tendsto.pow 2
  -- 2 a (h_seq n)² → 0
  have h_scaled : Filter.Tendsto (fun n => 2 * a * (h_seq n) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using h_pow.const_mul (2 * a)
  -- 12 a x² + 2 a (h_seq n)² → 12 a x² + 0 = 12 a x²
  simpa using (tendsto_const_nhds (x := 12 * a * x ^ 2)).add h_scaled

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.7 — THIRD CONCRETE WITNESS: CUBIC POLYNOMIALS (exact, odd-degree)

    Cubics follow the same odd-degree-cancellation pattern as the linear
    case:  `(x+h)^3 + (x-h)^3 - 2 x^3 = 6 x h^2`  (the h^3 terms cancel),
    so  `fdLaplacian1D = 6 a x = laplacian1D`  exactly.  Confirms the
    polynomial heuristic:  degrees ≤ 3 are exact, degree ≥ 4 have
    non-zero O(h²) error.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Centered fd Laplacian of a cubic polynomial:  `6 a x` exact. -/
theorem fdLaplacian1D_cubic (a x h : ℝ) (h_ne : h ≠ 0) :
    fdLaplacian1D h (fun y => a * y ^ 3) x = 6 * a * x := by
  unfold fdLaplacian1D
  have h2_ne : h ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  field_simp
  ring

/-- First derivative:  `d/dy (a y³) = 3 a y²`. -/
theorem deriv_cubic (a : ℝ) :
    deriv (fun y : ℝ => a * y ^ 3) = fun y => 3 * a * y ^ 2 := by
  ext y
  have hp : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y :=
    hasDerivAt_pow 3 y
  have h1 : HasDerivAt (fun z : ℝ => a * z ^ 3) (3 * a * y ^ 2) y := by
    have := hp.const_mul a
    convert this using 1
    ring
  exact h1.deriv

/-- Second derivative step:  `d/dy (3 a y²) = 6 a y`. -/
theorem deriv_3ay2 (a : ℝ) :
    deriv (fun y : ℝ => 3 * a * y ^ 2) = fun y => 6 * a * y := by
  ext y
  have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    have h := hasDerivAt_pow 2 y
    convert h using 1
    push_cast; ring
  have h1 : HasDerivAt (fun z : ℝ => 3 * a * z ^ 2) (6 * a * y) y := by
    have := hp.const_mul (3 * a)
    convert this using 1
    ring
  exact h1.deriv

/-- Continuum Laplacian:  `laplacian1D (a y³) x = 6 a x`. -/
theorem laplacian1D_cubic (a x : ℝ) :
    laplacian1D (fun y => a * y ^ 3) x = 6 * a * x := by
  change deriv (deriv (fun y : ℝ => a * y ^ 3)) x = 6 * a * x
  rw [deriv_cubic, deriv_3ay2]

/-- Discrete equals continuum for cubics (exact). -/
theorem fdLaplacian1D_eq_laplacian1D_cubic
    (a x h : ℝ) (h_ne : h ≠ 0) :
    fdLaplacian1D h (fun y => a * y ^ 3) x =
      laplacian1D (fun y => a * y ^ 3) x := by
  rw [fdLaplacian1D_cubic a x h h_ne, laplacian1D_cubic a x]

/-- Convergence holds trivially for cubics. -/
theorem fdLaplacian1D_converges_cubic (a x : ℝ) :
    FiniteDifferenceLaplacian1D_ConvergesAt (fun y => a * y ^ 3) x := by
  intro h_seq h_pos _
  rw [laplacian1D_cubic]
  have hconst : ∀ n,
      fdLaplacian1D (h_seq n) (fun y => a * y ^ 3) x = 6 * a * x := fun n =>
    fdLaplacian1D_cubic a x (h_seq n) (ne_of_gt (h_pos n))
  have heq : (fun n => fdLaplacian1D (h_seq n) (fun y => a * y ^ 3) x)
              = (fun _ => 6 * a * x) := funext hconst
  rw [heq]
  exact tendsto_const_nhds

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.8 — WATERSHED THEOREM STATEMENT

    The smooth-function convergence theorem (statement only):  for any
    `C³` test function `φ` on ℝ, the centered finite-difference
    Laplacian converges to the second derivative at every point.

    Proof would proceed via Mathlib's `taylor_mean_remainder_lagrange`:
      • Apply Taylor with n = 2 to φ on `[x, x+h]` → ξ_+ ∈ (x, x+h),
        f(x+h) = f(x) + f'(x)h + f''(x)h²/2 + f'''(ξ_+) h³/6.
      • Apply Taylor with n = 2 to g(s) := φ(x − s) on `[0, h]` →
        ξ_- ∈ (x−h, x), with similar expansion for f(x−h).
      • Sum:  centered fd − φ''(x) = (φ'''(ξ_+) − φ'''(ξ_-)) h / 6.
      • As h → 0:  ξ_± → x, so by continuity of φ''' the error → 0.

    This is THE concrete next-session target: replace this `Prop` by
    a proved theorem.  Once it lands, sub-bridge 2's chartwise core is
    closed for all C³ test functions in 1D, and the program turns to
    multidimensional flat (coordinate-wise sum) then curved-chart
    (geometric transport) — both bookkeeping rather than fresh analysis.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **`SmoothConvergenceTheorem_1D`** — the watershed proposition.

    For every `C³` real-valued function `φ` and every point `x`, the
    centered finite-difference Laplacian converges to the second
    derivative at `x`.  Stated; proof deferred to the next session.

    The proof uses `Real.taylor_mean_remainder_lagrange` twice
    (Mathlib4 lemma in `Mathlib/Analysis/Calculus/Taylor.lean`):

    Step 1: Apply Taylor with `n = 2` to φ on `Icc x (x + h)`.
      ContDiff ℝ 3 φ gives the hypotheses; result yields ξ_+ ∈ (x, x+h)
      with
          φ(x+h) − (φ(x) + φ'(x) h + (φ''(x)/2) h²) = φ'''(ξ_+) · h³ / 6.

    Step 2: Apply Taylor with `n = 2` to the substitution `g(s) := φ(x − s)`
      on `Icc 0 h`.  `g` is ContDiff ℝ 3 since φ is and `s ↦ x − s` is
      smooth.  Result yields ξ_- ∈ (0, h) with
          g(h) − (g(0) + g'(0) h + (g''(0)/2) h²) = g'''(ξ_-) · h³ / 6.
      Since g(h) = φ(x−h), g'(0) = −φ'(x), g''(0) = φ''(x),
      g'''(ξ_-) = −φ'''(x − ξ_-):
          φ(x−h) − (φ(x) − φ'(x) h + (φ''(x)/2) h²) = −φ'''(x−ξ_-)·h³/6.

    Step 3: Sum:
      φ(x+h) + φ(x−h) − 2 φ(x) − φ''(x) h² =
          (φ'''(ξ_+) − φ'''(x − ξ_-)) · h³ / 6.

    Step 4: Divide by h²:
      fdLaplacian1D h φ x − φ''(x) =
          (φ'''(ξ_+) − φ'''(x − ξ_-)) · h / 6.

    Step 5: Take h → 0+.  Since ξ_+ ∈ (x, x+h) and (x − ξ_-) ∈ (x−h, x),
      both → x.  By continuity of φ''' (from `ContDiff.continuous_iteratedDeriv'`),
      the bracket → 0.  Multiplied by h → 0, the whole error → 0.

    Therefore  fdLaplacian1D h φ x → φ''(x) = laplacian1D φ x.

    Required Mathlib lemmas (already located):
      • `Real.taylor_mean_remainder_lagrange` (Taylor.lean)
      • `ContDiff.continuous_iteratedDeriv'` (IteratedDeriv/Defs.lean)
      • `taylorWithinEval` unfolding via `taylor_within_apply`
      • `ContDiff.comp` (for the g(s) := φ(x − s) substitution). -/
def SmoothConvergenceTheorem_1D : Prop :=
  ∀ (φ : ℝ → ℝ), ContDiff ℝ 3 φ →
    ∀ (x : ℝ), FiniteDifferenceLaplacian1D_ConvergesAt φ x

/-- The watershed theorem decomposes into a single CORE LEMMA: the
    Taylor-bound formula for the centered fd Laplacian.  Once this
    lemma is closed, convergence follows by the elementary limit
    argument (Filter.Tendsto on `h → 0+`). -/
def TaylorBound_CenteredFD (φ : ℝ → ℝ) (x : ℝ) : Prop :=
  ContDiff ℝ 3 φ →
  ∀ (h : ℝ), 0 < h →
  ∃ ξ_plus ∈ Set.Ioo x (x + h),
  ∃ ξ_minus ∈ Set.Ioo (x - h) x,
    fdLaplacian1D h φ x - laplacian1D φ x =
      h * (iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus) / 6

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.9 — FIRST CONCRETE  `TaylorBound_CenteredFD`  INSTANCE

    Prove `TaylorBound_CenteredFD` for the specific monomial  `y ↦ y^4`.
    Demonstrates the proof template: compute `iteratedDeriv 3` explicitly,
    exhibit witnesses ξ_+ = x + h/4, ξ_- = x - h/4 satisfying the Taylor
    bound formula.

    The verification is purely algebraic:
        fdLaplacian1D h (y^4) x − laplacian1D (y^4) x
          = (12 x² + 2 h²) − 12 x²  =  2 h²
        h · (24 · (x + h/4) − 24 · (x − h/4)) / 6
          = h · 24 · (h/2) / 6  =  2 h².
    ════════════════════════════════════════════════════════════════════════ -/

/-- The 3rd iterated derivative of  `y ↦ y^4`  is  `y ↦ 24·y`. -/
theorem iteratedDeriv_three_pow4 :
    iteratedDeriv 3 (fun y : ℝ => y ^ 4) = fun y => 24 * y := by
  have step1 : deriv (fun y : ℝ => y ^ 4) = fun y => 4 * y ^ 3 := by
    ext z; exact (hasDerivAt_pow 4 z).deriv
  have step2 : deriv (fun y : ℝ => 4 * y ^ 3) = fun y => 12 * y ^ 2 := by
    ext z
    have hp : HasDerivAt (fun y : ℝ => y ^ 3) (3 * z ^ 2) z := hasDerivAt_pow 3 z
    have h : HasDerivAt (fun y : ℝ => 4 * y ^ 3) (12 * z ^ 2) z := by
      have := hp.const_mul 4
      convert this using 1; ring
    exact h.deriv
  have step3 : deriv (fun y : ℝ => 12 * y ^ 2) = fun y => 24 * y := by
    ext z
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := hasDerivAt_pow 2 z
      convert h using 1; push_cast; ring
    have h : HasDerivAt (fun y : ℝ => 12 * y ^ 2) (24 * z) z := by
      have := hp.const_mul 12
      convert this using 1; ring
    exact h.deriv
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero, step1, step2, step3]

/-- fd Laplacian of  `y ↦ y^4`  at scale h, at x:  `12 x² + 2 h²`. -/
theorem fdLaplacian1D_pow4 (x h : ℝ) (h_ne : h ≠ 0) :
    fdLaplacian1D h (fun y => y ^ 4) x = 12 * x ^ 2 + 2 * h ^ 2 := by
  unfold fdLaplacian1D
  have h2_ne : h ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  field_simp
  ring

/-- Continuum Laplacian of  `y ↦ y^4`  at x:  `12 x²`. -/
theorem laplacian1D_pow4 (x : ℝ) :
    laplacian1D (fun y => y ^ 4) x = 12 * x ^ 2 := by
  change deriv (deriv (fun y : ℝ => y ^ 4)) x = 12 * x ^ 2
  have step1 : deriv (fun y : ℝ => y ^ 4) = fun y => 4 * y ^ 3 := by
    ext z; exact (hasDerivAt_pow 4 z).deriv
  rw [step1]
  have hp : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := hasDerivAt_pow 3 x
  have h : HasDerivAt (fun y : ℝ => 4 * y ^ 3) (12 * x ^ 2) x := by
    have := hp.const_mul 4
    convert this using 1; ring
  exact h.deriv

/-- **First concrete instance of `TaylorBound_CenteredFD`**.

    For `φ(y) = y^4` and any h > 0, the bound formula holds with
    explicit witnesses  ξ_+ = x + h/4  and  ξ_- = x - h/4. -/
theorem TaylorBound_CenteredFD_pow4 (x : ℝ) :
    TaylorBound_CenteredFD (fun y => y ^ 4) x := by
  intro _h_smooth h h_pos
  refine ⟨x + h / 4, ⟨by linarith, by linarith⟩,
          x - h / 4, ⟨by linarith, by linarith⟩, ?_⟩
  rw [fdLaplacian1D_pow4 x h (ne_of_gt h_pos), laplacian1D_pow4,
      iteratedDeriv_three_pow4]
  ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.10 — `BoundedConvergenceForm`  AND  THEOREM B

    Cleaner convergence-usable form of the Taylor bound:
        ∃ δ > 0,  ∃ C ≥ 0,  ∀ h ∈ (0, δ),
            |fdLaplacian1D h φ x − laplacian1D φ x| ≤ C · h.

    Theorem B (the user's "easier remaining theorem"):
        `BoundedConvergenceForm φ x  ⟹  FiniteDifferenceLaplacian1D_ConvergesAt φ x`

    Standard ε-δ argument:  given ε > 0, pick N so that h_seq n is
    simultaneously less than δ (so the bound applies) and less than
    ε / (C + 1) (so C · h_seq n < ε).  Then `|fd − lap| ≤ C · h_seq n < ε`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Convergence-usable form of the Taylor bound.**

    There exists a positive `δ` and nonneg `C` such that for every
    `h ∈ (0, δ)`, the centered fd Laplacian deviates from the second
    derivative by at most `C · h`. -/
def BoundedConvergenceForm (φ : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h < δ →
    |fdLaplacian1D h φ x - laplacian1D φ x| ≤ C * h

/-- **THEOREM B**: `BoundedConvergenceForm` implies pointwise convergence.

    The fastest path from a Taylor-style bound to the actual
    `FiniteDifferenceLaplacian1D_ConvergesAt` statement.  Once SB2 has
    the bound for general C³ functions, this theorem hands back full
    convergence for free. -/
theorem convergence_from_BoundedConvergenceForm
    (φ : ℝ → ℝ) (x : ℝ) (h_bound : BoundedConvergenceForm φ x) :
    FiniteDifferenceLaplacian1D_ConvergesAt φ x := by
  intro h_seq h_pos h_tendsto
  obtain ⟨δ, hδ_pos, C, hC_nn, hC⟩ := h_bound
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at h_tendsto
  -- Find N₁: h_seq n < δ for n ≥ N₁
  obtain ⟨N₁, hN₁⟩ := h_tendsto δ hδ_pos
  -- Find N₂: h_seq n < ε / (C + 1) for n ≥ N₂
  have hCp1_pos : (0 : ℝ) < C + 1 := by linarith
  have hε_div_pos : (0 : ℝ) < ε / (C + 1) := div_pos hε hCp1_pos
  obtain ⟨N₂, hN₂⟩ := h_tendsto (ε / (C + 1)) hε_div_pos
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have habs : |h_seq n - 0| = h_seq n := by
    rw [sub_zero]; exact abs_of_pos (h_pos n)
  have hh_lt_δ : h_seq n < δ := by
    have h := hN₁ n hn₁
    rw [Real.dist_eq, habs] at h
    exact h
  have hh_lt_eps_C : h_seq n < ε / (C + 1) := by
    have h := hN₂ n hn₂
    rw [Real.dist_eq, habs] at h
    exact h
  have hbound := hC (h_seq n) (h_pos n) hh_lt_δ
  -- |fdLaplacian1D - laplacian1D| ≤ C * h_seq n < ε
  rw [Real.dist_eq]
  calc |fdLaplacian1D (h_seq n) φ x - laplacian1D φ x|
      ≤ C * h_seq n := hbound
    _ ≤ C * (ε / (C + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hh_lt_eps_C) hC_nn
    _ < ε := by
        rw [show C * (ε / (C + 1)) = (C * ε) / (C + 1) from by ring]
        rw [div_lt_iff₀ hCp1_pos]
        nlinarith

/-- **Specialization of TaylorBound to a quartic.**  The quartic
    Taylor-bound instance from Part 4.9 supplies the `BoundedConvergenceForm`
    for `y ↦ y^4` directly with `δ = 1`, `C = 2`. -/
theorem BoundedConvergenceForm_pow4 (x : ℝ) :
    BoundedConvergenceForm (fun y => y ^ 4) x := by
  refine ⟨1, by norm_num, 2, by norm_num, fun h h_pos h_lt => ?_⟩
  rw [fdLaplacian1D_pow4 x h (ne_of_gt h_pos), laplacian1D_pow4]
  -- |12 x^2 + 2 h^2 - 12 x^2| = 2 h^2.  Need 2 h^2 ≤ 2 h, i.e., h ≤ 1.
  rw [show (12 * x ^ 2 + 2 * h ^ 2 - 12 * x ^ 2) = 2 * h ^ 2 from by ring]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [h_lt, h_pos.le, sq_nonneg h]

/-- **Quartic convergence via the B theorem**, alternative to the
    direct proof in Part 4.6.  Demonstrates the full chain:
    `BoundedConvergenceForm` → `FiniteDifferenceLaplacian1D_ConvergesAt`. -/
theorem fdLaplacian1D_converges_pow4_via_BoundedConvergenceForm (x : ℝ) :
    FiniteDifferenceLaplacian1D_ConvergesAt (fun y => y ^ 4) x :=
  convergence_from_BoundedConvergenceForm _ _ (BoundedConvergenceForm_pow4 x)

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.11 — BRIDGE  `TaylorBound`  →  `BoundedConvergenceForm`
                                    (under `ContDiff ℝ 3`)

    From the existential Taylor bound (with explicit witnesses ξ_+, ξ_-)
    and continuity of `iteratedDeriv 3 φ` (from `ContDiff ℝ 3`), extract:
      • δ = 1 (the neighborhood radius)
      • C = M / 3, where M = max |φ'''(y)| over y ∈ [x-1, x+1]
    Then the bound |fd − lap| ≤ C · h holds for h ∈ (0, 1).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Bridge**: `TaylorBound_CenteredFD φ x`  ⟹  `BoundedConvergenceForm φ x`
    (given `ContDiff ℝ 3 φ` for continuity of the third derivative).

    The bound uses
        C := (max |φ'''| over [x − 1, x + 1]) / 3,
        δ := 1.
    For h ∈ (0, 1), both Taylor witnesses ξ_+ ∈ (x, x+h) and
    ξ_- ∈ (x−h, x) lie in [x−1, x+1], where |φ'''| ≤ M, so
        |fd − lap| = |h · (φ'''(ξ_+) − φ'''(ξ_-)) / 6|
                   ≤ h · 2M / 6  =  M h / 3
                   =  C · h. -/
theorem BoundedConvergenceForm_from_TaylorBound
    (φ : ℝ → ℝ) (x : ℝ) (h_smooth : ContDiff ℝ 3 φ)
    (h_taylor : TaylorBound_CenteredFD φ x) :
    BoundedConvergenceForm φ x := by
  have h_t := h_taylor h_smooth
  have h_cont : Continuous (iteratedDeriv 3 φ) :=
    h_smooth.continuous_iteratedDeriv' 3
  have h_cont_abs : Continuous (fun y => |iteratedDeriv 3 φ y|) := h_cont.abs
  have h_compact : IsCompact (Set.Icc (x - 1) (x + 1)) := isCompact_Icc
  have h_nonempty : (Set.Icc (x - 1) (x + 1)).Nonempty :=
    ⟨x, by constructor <;> linarith⟩
  obtain ⟨a, _ha_in, ha_max⟩ :=
    h_compact.exists_isMaxOn h_nonempty h_cont_abs.continuousOn
  set M := |iteratedDeriv 3 φ a| with hM_def
  have hM_nn : 0 ≤ M := abs_nonneg _
  refine ⟨1, by norm_num, M / 3, by positivity, ?_⟩
  intro h h_pos h_lt
  obtain ⟨ξ_plus, hξ_plus_in, ξ_minus, hξ_minus_in, h_eq⟩ := h_t h h_pos
  -- ξ_+ ∈ (x, x+h) ⊆ [x-1, x+1]   since h < 1
  have hξ_plus_in_K : ξ_plus ∈ Set.Icc (x - 1) (x + 1) := by
    rw [Set.mem_Ioo] at hξ_plus_in
    refine ⟨?_, ?_⟩ <;> linarith
  -- ξ_- ∈ (x-h, x) ⊆ [x-1, x+1]
  have hξ_minus_in_K : ξ_minus ∈ Set.Icc (x - 1) (x + 1) := by
    rw [Set.mem_Ioo] at hξ_minus_in
    refine ⟨?_, ?_⟩ <;> linarith
  -- Apply the max bound
  have h_plus_bd : |iteratedDeriv 3 φ ξ_plus| ≤ M := ha_max hξ_plus_in_K
  have h_minus_bd : |iteratedDeriv 3 φ ξ_minus| ≤ M := ha_max hξ_minus_in_K
  -- Triangle inequality on the difference
  have h_diff_bd :
      |iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus| ≤ 2 * M := by
    have htri : |iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus| ≤
                |iteratedDeriv 3 φ ξ_plus| + |iteratedDeriv 3 φ ξ_minus| :=
      abs_sub _ _
    linarith
  -- Substitute h_eq and bound
  rw [h_eq]
  have h6_pos : (0 : ℝ) < 6 := by norm_num
  rw [show (h * (iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus) / 6) =
         (h * (iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus)) / 6
         from by ring]
  rw [abs_div, abs_of_pos h6_pos, abs_mul, abs_of_pos h_pos]
  -- Goal:  h * |φ'''(ξ_+) − φ'''(ξ_-)| / 6 ≤ M / 3 * h
  rw [div_le_iff₀ h6_pos]
  -- Goal:  h * |φ'''(ξ_+) − φ'''(ξ_-)| ≤ M / 3 * h * 6
  have h_mul_bd :
      h * |iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus| ≤ h * (2 * M) :=
    mul_le_mul_of_nonneg_left h_diff_bd h_pos.le
  nlinarith [h_mul_bd, hM_nn, h_pos.le]

/-- **The Step-A target** (statement-form), reduced under the bridge:
    if `TaylorBound_CenteredFD φ x` holds for a `C³` function, then
    `FiniteDifferenceLaplacian1D_ConvergesAt φ x` holds.

    Composition of `BoundedConvergenceForm_from_TaylorBound` and the
    `convergence_from_BoundedConvergenceForm` theorem (Part 4.10). -/
theorem convergence_from_TaylorBound_and_contDiff3
    (φ : ℝ → ℝ) (x : ℝ) (h_smooth : ContDiff ℝ 3 φ)
    (h_taylor : TaylorBound_CenteredFD φ x) :
    FiniteDifferenceLaplacian1D_ConvergesAt φ x :=
  convergence_from_BoundedConvergenceForm φ x
    (BoundedConvergenceForm_from_TaylorBound φ x h_smooth h_taylor)

/-- **Watershed theorem CONDITIONAL on theorem A**.

    If `TaylorBound_CenteredFD` holds for every C³ function (theorem A),
    then the smooth-function convergence theorem `SmoothConvergenceTheorem_1D`
    follows immediately by composition.

    Once theorem A is proved (using `Real.taylor_mean_remainder_lagrange` twice),
    this becomes the final closure of the SB2 chartwise core. -/
theorem SmoothConvergenceTheorem_1D_from_TaylorBound
    (hA : ∀ (φ : ℝ → ℝ), ContDiff ℝ 3 φ → ∀ (x : ℝ), TaylorBound_CenteredFD φ x) :
    SmoothConvergenceTheorem_1D :=
  fun φ h_smooth x =>
    convergence_from_TaylorBound_and_contDiff3 φ x h_smooth (hA φ h_smooth x)

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.12 — REFLECTION HELPERS  (toward theorem A)

    Per the proof plan for `TaylorBound_CenteredFD_of_contDiff3` (theorem A):
    introduce  `reflectedAt x φ := fun s => φ(x − s)`  and prove the chain
    rule for its iterated derivatives.  This is the sign-tracking machinery
    needed for the "left-hand" Taylor expansion of φ at x going in the
    direction of x − h.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Reflection of `φ` about `x`:  `s ↦ φ(x − s)`. -/
def reflectedAt (x : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun s => φ (x - s)

/-- `s ↦ x − s` is `C^n` for any `n`. -/
theorem contDiff_const_sub_id {n : ℕ∞} (x : ℝ) :
    ContDiff ℝ n (fun s : ℝ => x - s) :=
  contDiff_const.sub contDiff_id

/-- `reflectedAt x φ` is `C^n` whenever `φ` is. -/
theorem contDiff_reflectedAt {φ : ℝ → ℝ} (x : ℝ) {n : ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (reflectedAt x φ) :=
  hφ.comp (contDiff_const_sub_id x)

/-- HasDerivAt for `reflectedAt x φ` at `s`:  derivative is `−deriv φ (x − s)`. -/
theorem hasDerivAt_reflectedAt {φ : ℝ → ℝ} {x s : ℝ}
    (hφ : DifferentiableAt ℝ φ (x - s)) :
    HasDerivAt (reflectedAt x φ) (-deriv φ (x - s)) s := by
  have h_sub : HasDerivAt (fun t : ℝ => x - t) (-1 : ℝ) s := by
    have := (hasDerivAt_const s x).sub (hasDerivAt_id s)
    simpa using this
  have h_at : HasDerivAt φ (deriv φ (x - s)) (x - s) := hφ.hasDerivAt
  have hcomp := h_at.comp s h_sub
  -- hcomp : HasDerivAt (fun t => φ (x - t)) (deriv φ (x - s) * (-1)) s
  unfold reflectedAt
  convert hcomp using 1
  ring

/-- Function-level identity:  `deriv (reflectedAt x φ) = fun s => -deriv φ (x − s)`. -/
theorem deriv_reflectedAt_eq {φ : ℝ → ℝ} (x : ℝ) (hφ : Differentiable ℝ φ) :
    deriv (reflectedAt x φ) = fun s => -deriv φ (x - s) := by
  ext s
  exact (hasDerivAt_reflectedAt (hφ (x - s))).deriv

/-- Pointwise:  `deriv (deriv (reflectedAt x φ)) s = deriv (deriv φ) (x − s)`.
    (Sign flip at first derivative, sign cancels at second.) -/
theorem hasDerivAt_deriv_reflectedAt {φ : ℝ → ℝ} {x s : ℝ}
    (hφ : ContDiff ℝ 2 φ) :
    HasDerivAt (deriv (reflectedAt x φ)) (deriv (deriv φ) (x - s)) s := by
  have hφ_diff : Differentiable ℝ φ :=
    hφ.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hd_diff_iter : Differentiable ℝ (iteratedDeriv 1 φ) :=
    hφ.differentiable_iteratedDeriv 1 (by norm_num : (1 : WithTop ℕ∞) < 2)
  have hd_diff : Differentiable ℝ (deriv φ) := by
    have heq : iteratedDeriv 1 φ = deriv φ := by
      funext y
      rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [heq] at hd_diff_iter
    exact hd_diff_iter
  rw [deriv_reflectedAt_eq x hφ_diff]
  -- Goal:  HasDerivAt (fun s => -deriv φ (x - s)) (deriv (deriv φ) (x - s)) s
  have h_ref : HasDerivAt (reflectedAt x (deriv φ))
      (-deriv (deriv φ) (x - s)) s :=
    hasDerivAt_reflectedAt (hd_diff (x - s))
  have h_neg := h_ref.neg
  simp only [neg_neg] at h_neg
  exact h_neg

/-- Function-level: `deriv (deriv (reflectedAt x φ)) = fun s => deriv (deriv φ) (x − s)`. -/
theorem deriv2_reflectedAt_eq {φ : ℝ → ℝ} (x : ℝ) (hφ : ContDiff ℝ 2 φ) :
    deriv (deriv (reflectedAt x φ)) = fun s => deriv (deriv φ) (x - s) := by
  ext s
  exact (hasDerivAt_deriv_reflectedAt hφ).deriv

/-- Pointwise:  third derivative of `reflectedAt x φ` at `s` equals
    `-iteratedDeriv 3 φ (x − s)`  (sign flip again at third level). -/
theorem hasDerivAt_deriv2_reflectedAt {φ : ℝ → ℝ} {x s : ℝ}
    (hφ : ContDiff ℝ 3 φ) :
    HasDerivAt (deriv (deriv (reflectedAt x φ)))
      (-iteratedDeriv 3 φ (x - s)) s := by
  have hφ2 : ContDiff ℝ 2 φ :=
    hφ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hd2_diff_iter : Differentiable ℝ (iteratedDeriv 2 φ) :=
    hφ.differentiable_iteratedDeriv 2 (by norm_num : (2 : WithTop ℕ∞) < 3)
  have heq2 : iteratedDeriv 2 φ = deriv (deriv φ) := by
    funext y
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  have hd2_diff : Differentiable ℝ (deriv (deriv φ)) := heq2 ▸ hd2_diff_iter
  rw [deriv2_reflectedAt_eq x hφ2]
  -- Goal: HasDerivAt (fun s => deriv (deriv φ) (x - s)) (-iteratedDeriv 3 φ (x - s)) s
  have h_ref : HasDerivAt (reflectedAt x (deriv (deriv φ)))
      (-deriv (deriv (deriv φ)) (x - s)) s :=
    hasDerivAt_reflectedAt (hd2_diff (x - s))
  have heq3 : iteratedDeriv 3 φ = deriv (deriv (deriv φ)) := by
    funext y
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq3]
  -- h_ref : HasDerivAt (reflectedAt x (deriv (deriv φ))) (-deriv (deriv (deriv φ)) (x - s)) s
  -- Goal:  HasDerivAt (fun s => deriv (deriv φ) (x - s)) (-deriv (deriv (deriv φ)) (x - s)) s
  exact h_ref

/-- Function-level: `iteratedDeriv 3 (reflectedAt x φ) = fun s => -iteratedDeriv 3 φ (x − s)`. -/
theorem iteratedDeriv_three_reflectedAt_eq {φ : ℝ → ℝ} (x : ℝ) (hφ : ContDiff ℝ 3 φ) :
    iteratedDeriv 3 (reflectedAt x φ) = fun s => -iteratedDeriv 3 φ (x - s) := by
  funext s
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  exact (hasDerivAt_deriv2_reflectedAt hφ).deriv

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.13 — TAYLOR EXPANSIONS  (final pieces of theorem A)

    Right- and left-hand 2nd-order Taylor expansions using:
      • `Real.taylor_mean_remainder_lagrange_iteratedDeriv` (Mathlib's
        Lagrange form, gives the remainder in terms of `iteratedDeriv`).
      • `taylor_within_apply (E := ℝ)` (explicit type annotation avoids
        `NormedSpace` typeclass elaboration stall).
      • `iteratedDerivWithin_eq_iteratedDeriv` (within → global at basepoint).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Right-hand Taylor expansion (order 2)** at x for h > 0. -/
theorem taylor_right_second_order {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Ioo x (x + h),
      φ (x + h) = φ x + h * deriv φ x + (h ^ 2 / 2) * iteratedDeriv 2 φ x
                + (h ^ 3 / 6) * iteratedDeriv 3 φ ξ := by
  have hx_lt : x < x + h := by linarith
  -- Apply Mathlib's Lagrange remainder with iteratedDeriv
  have h_cdo : ContDiffOn ℝ ((2 : ℕ) + 1 : ℕ∞) φ (Set.Icc x (x + h)) := by
    have h_eq : ((2 : ℕ) + 1 : ℕ∞) = 3 := by norm_num
    rw [h_eq]; exact hφ.contDiffOn
  obtain ⟨ξ, hξ_in, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hx_lt h_cdo
  refine ⟨ξ, hξ_in, ?_⟩
  -- Set up within → global conversion at basepoint
  have hUDO : UniqueDiffOn ℝ (Set.Icc x (x + h)) := uniqueDiffOn_Icc hx_lt
  have hxmem : x ∈ Set.Icc x (x + h) := ⟨le_refl _, by linarith⟩
  have hcd0 : ContDiffAt ℝ 0 φ x := hφ.contDiffAt.of_le (by norm_num)
  have hcd1 : ContDiffAt ℝ 1 φ x := hφ.contDiffAt.of_le (by norm_num)
  have hcd2 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt.of_le (by norm_num)
  have hID0 : iteratedDerivWithin 0 φ (Set.Icc x (x + h)) x = iteratedDeriv 0 φ x :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hcd0 hxmem
  have hID1 : iteratedDerivWithin 1 φ (Set.Icc x (x + h)) x = iteratedDeriv 1 φ x :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hcd1 hxmem
  have hID2 : iteratedDerivWithin 2 φ (Set.Icc x (x + h)) x = iteratedDeriv 2 φ x :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hcd2 hxmem
  have hiD1 : iteratedDeriv 1 φ x = deriv φ x := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  -- Expand the Taylor polynomial via taylor_within_apply with explicit (E := ℝ)
  have h_apply : taylorWithinEval φ 2 (Set.Icc x (x + h)) x (x + h) =
                 ∑ k ∈ Finset.range 3,
                   ((k.factorial : ℝ)⁻¹ * (x + h - x) ^ k) •
                     iteratedDerivWithin k φ (Set.Icc x (x + h)) x :=
    taylor_within_apply (E := ℝ) φ 2 (Set.Icc x (x + h)) x (x + h)
  rw [h_apply] at hTaylor
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             pow_zero, pow_one, smul_eq_mul, mul_one,
             hID0, hID1, hID2, iteratedDeriv_zero, hiD1] at hTaylor
  -- Simplify (x + h - x) → h and the factorial denominators
  have hsub : x + h - x = h := by ring
  rw [hsub] at hTaylor
  -- The factorial coefficients: 0! = 1, 1! = 1, 2! = 2, 3! = 6
  simp only [show ((0 : ℕ).factorial : ℝ) = 1 from by norm_num,
             show ((1 : ℕ).factorial : ℝ) = 1 from by norm_num,
             show ((2 : ℕ).factorial : ℝ) = 2 from by norm_num,
             show (((2 : ℕ) + 1).factorial : ℝ) = 6 from by norm_num,
             inv_one, one_mul] at hTaylor
  linarith [hTaylor]

/-- **Left-hand Taylor expansion (order 2)** at x for h > 0.
    Uses the reflection chain (Part 4.12) on `g := reflectedAt x φ`. -/
theorem taylor_left_second_order {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Ioo (x - h) x,
      φ (x - h) = φ x - h * deriv φ x + (h ^ 2 / 2) * iteratedDeriv 2 φ x
                - (h ^ 3 / 6) * iteratedDeriv 3 φ ξ := by
  -- Apply Mathlib's Taylor lemma to g := reflectedAt x φ on Icc 0 h
  have hg_smooth : ContDiff ℝ 3 (reflectedAt x φ) := contDiff_reflectedAt x hφ
  have h_cdo : ContDiffOn ℝ ((2 : ℕ) + 1 : ℕ∞) (reflectedAt x φ) (Set.Icc 0 h) := by
    have h_eq : ((2 : ℕ) + 1 : ℕ∞) = 3 := by norm_num
    rw [h_eq]; exact hg_smooth.contDiffOn
  obtain ⟨η, hη_in, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hh h_cdo
  -- Witness ξ := x - η
  refine ⟨x - η, ?_, ?_⟩
  · rw [Set.mem_Ioo] at hη_in
    refine ⟨?_, ?_⟩ <;> linarith
  -- Within → global at basepoint 0
  have hUDO : UniqueDiffOn ℝ (Set.Icc (0:ℝ) h) := uniqueDiffOn_Icc hh
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) h := ⟨le_refl _, by linarith⟩
  have hg_cdAt : ContDiffAt ℝ 3 (reflectedAt x φ) 0 := hg_smooth.contDiffAt
  have hg_cd0 : ContDiffAt ℝ 0 (reflectedAt x φ) 0 := hg_cdAt.of_le (by norm_num)
  have hg_cd1 : ContDiffAt ℝ 1 (reflectedAt x φ) 0 := hg_cdAt.of_le (by norm_num)
  have hg_cd2 : ContDiffAt ℝ 2 (reflectedAt x φ) 0 := hg_cdAt.of_le (by norm_num)
  have hID0 : iteratedDerivWithin 0 (reflectedAt x φ) (Set.Icc 0 h) 0 =
              iteratedDeriv 0 (reflectedAt x φ) 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hg_cd0 h0mem
  have hID1 : iteratedDerivWithin 1 (reflectedAt x φ) (Set.Icc 0 h) 0 =
              iteratedDeriv 1 (reflectedAt x φ) 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hg_cd1 h0mem
  have hID2 : iteratedDerivWithin 2 (reflectedAt x φ) (Set.Icc 0 h) 0 =
              iteratedDeriv 2 (reflectedAt x φ) 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO hg_cd2 h0mem
  -- Compute iteratedDeriv 0, 1, 2 of reflectedAt at 0
  have hgID0 : iteratedDeriv 0 (reflectedAt x φ) 0 = φ x := by
    change reflectedAt x φ 0 = φ x
    simp [reflectedAt]
  have hφ_diff : Differentiable ℝ φ :=
    hφ.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgID1 : iteratedDeriv 1 (reflectedAt x φ) 0 = -deriv φ x := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero,
        deriv_reflectedAt_eq x hφ_diff]
    simp
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have h_iter2_eq : ∀ f : ℝ → ℝ, iteratedDeriv 2 f = deriv (deriv f) := by
    intro f; funext s
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  have hgID2 : iteratedDeriv 2 (reflectedAt x φ) 0 = iteratedDeriv 2 φ x := by
    rw [h_iter2_eq, h_iter2_eq, deriv2_reflectedAt_eq x hφ2]
    simp
  -- Remainder via the reflection lemma:
  --   iteratedDeriv 3 (reflectedAt x φ) η = -iteratedDeriv 3 φ (x - η)
  have hgID3 : iteratedDeriv 3 (reflectedAt x φ) η = -iteratedDeriv 3 φ (x - η) := by
    rw [iteratedDeriv_three_reflectedAt_eq x hφ]
  -- Expand the Taylor polynomial
  have h_apply : taylorWithinEval (reflectedAt x φ) 2 (Set.Icc 0 h) 0 h =
                 ∑ k ∈ Finset.range 3,
                   ((k.factorial : ℝ)⁻¹ * (h - 0) ^ k) •
                     iteratedDerivWithin k (reflectedAt x φ) (Set.Icc 0 h) 0 :=
    taylor_within_apply (E := ℝ) (reflectedAt x φ) 2 (Set.Icc 0 h) 0 h
  rw [h_apply] at hTaylor
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             pow_zero, pow_one, smul_eq_mul, mul_one,
             hID0, hID1, hID2, hgID0, hgID1, hgID2, sub_zero,
             show reflectedAt x φ h = φ (x - h) from rfl] at hTaylor
  rw [hgID3] at hTaylor
  simp only [show ((0 : ℕ).factorial : ℝ) = 1 from by norm_num,
             show ((1 : ℕ).factorial : ℝ) = 1 from by norm_num,
             show ((2 : ℕ).factorial : ℝ) = 2 from by norm_num,
             show (((2 : ℕ) + 1).factorial : ℝ) = 6 from by norm_num,
             inv_one, one_mul] at hTaylor
  linarith [hTaylor]

/-- **Centered finite-difference exact remainder** — combines right- and
    left-hand 2nd-order Taylor expansions. -/
theorem centered_fd_exact_remainder {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x h : ℝ} (hh : 0 < h) :
    ∃ ξ_plus ∈ Set.Ioo x (x + h), ∃ ξ_minus ∈ Set.Ioo (x - h) x,
      fdLaplacian1D h φ x - laplacian1D φ x =
        h * (iteratedDeriv 3 φ ξ_plus - iteratedDeriv 3 φ ξ_minus) / 6 := by
  obtain ⟨ξ_plus, hξ_plus_in, hRight⟩ := taylor_right_second_order hφ hh
  obtain ⟨ξ_minus, hξ_minus_in, hLeft⟩ := taylor_left_second_order hφ hh
  refine ⟨ξ_plus, hξ_plus_in, ξ_minus, hξ_minus_in, ?_⟩
  unfold fdLaplacian1D laplacian1D
  have hlap_eq : deriv (deriv φ) x = iteratedDeriv 2 φ x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hlap_eq, hRight, hLeft]
  have hh2_ne : h ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hh)
  field_simp
  ring

/-- **THEOREM A: `TaylorBound_CenteredFD_of_contDiff3`** —
    the watershed analytic step.  Closes the SB2 chartwise core. -/
theorem TaylorBound_CenteredFD_of_contDiff3 {φ : ℝ → ℝ} (x : ℝ) :
    TaylorBound_CenteredFD φ x := by
  intro h_smooth h h_pos
  exact centered_fd_exact_remainder h_smooth h_pos

/-- **`SmoothConvergenceTheorem_1D_proved`** — the watershed theorem,
    now a real proved theorem (not just a `Prop` statement).

    For every `C³` real-valued function `φ` and every point `x`, the
    centered finite-difference Laplacian converges to the second
    derivative at `x` as the step size shrinks to zero.

    The full chain: theorem A (this file, just proved)
      ⟹ `BoundedConvergenceForm_from_TaylorBound`
      ⟹ `convergence_from_BoundedConvergenceForm`
      ⟹ `SmoothConvergenceTheorem_1D`. -/
theorem SmoothConvergenceTheorem_1D_proved : SmoothConvergenceTheorem_1D :=
  SmoothConvergenceTheorem_1D_from_TaylorBound
    (fun _ _ x => TaylorBound_CenteredFD_of_contDiff3 x)

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.14 — MULTI-DIMENSIONAL FLAT LAPLACIAN

    Extension of the 1D watershed theorem to ℝⁿ by coordinatewise sum.
    Bookkeeping rather than fresh analysis — each coordinate slice is C³
    (via `contDiff_pi` + the affine structure of `Function.update`), so
    `SmoothConvergenceTheorem_1D_proved` applies in each coordinate.
    Sum via `tendsto_finset_sum`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- The n-dim centered finite-difference Laplacian:  coordinatewise sum
    of 1D centered fd Laplacians on each coordinate slice. -/
noncomputable def fdLaplacianND {n : ℕ} (h : ℝ) (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fdLaplacian1D h (fun t => φ (Function.update x i t)) (x i)

/-- The n-dim continuum Laplacian:  coordinatewise sum of 1D Laplacians
    along each coordinate axis. -/
noncomputable def laplacianND {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, laplacian1D (fun t => φ (Function.update x i t)) (x i)

/-- ContDiff of the coordinate slice:  `(fun t => φ (Function.update x i t))`
    inherits the smoothness of φ.  Proof via `contDiff_pi`:  each
    component of `t ↦ Function.update x i t` is affine in t. -/
theorem contDiff_slice {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 3 φ)
    (x : Fin n → ℝ) (i : Fin n) :
    ContDiff ℝ 3 (fun t : ℝ => φ (Function.update x i t)) := by
  apply hφ.comp
  refine contDiff_pi.mpr (fun j => ?_)
  rcases eq_or_ne j i with hji | hji
  · -- j = i case:  the slice is the identity
    have h_id : (fun t : ℝ => Function.update x i t j) = fun t => t := by
      funext t
      rw [hji]
      exact Function.update_self i t x
    rw [h_id]
    exact contDiff_id
  · -- j ≠ i case:  the slice is the constant `x j`
    have h_const : (fun t : ℝ => Function.update x i t j) = fun _ => x j := by
      funext t
      exact Function.update_of_ne hji t x
    rw [h_const]
    exact contDiff_const

/-- **N-dim flat convergence theorem**: for any `C³` test function φ on
    `Fin n → ℝ`, the centered finite-difference n-dim Laplacian converges
    to the continuum Laplacian as h → 0.

    Extension of `SmoothConvergenceTheorem_1D_proved` to arbitrary finite
    dimension. -/
theorem fdLaplacianND_converges {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x : Fin n → ℝ)
    (h_seq : ℕ → ℝ) (h_pos : ∀ k, 0 < h_seq k)
    (h_tendsto : Filter.Tendsto h_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => fdLaplacianND (h_seq k) φ x) Filter.atTop
                   (nhds (laplacianND φ x)) := by
  unfold fdLaplacianND laplacianND
  exact tendsto_finset_sum _ fun i _ =>
    SmoothConvergenceTheorem_1D_proved _
      (contDiff_slice φ hφ x i) (x i) h_seq h_pos h_tendsto

/-! ════════════════════════════════════════════════════════════════════════
    PART 4.15 — SubBridge2 REALIZATION (existential discharge)

    With the multi-dim flat Laplacian convergence proved (Part 4.14), the
    `SubBridge2_HauptvermutungLaplacianControl` proposition of
    `LohmillerSlotineContinuumLimit` is trivially realizable:  for any
    prescribed `lap` value at a point, construct a `CurvedWaveData`
    bundling the smooth wave field's snapshot with that lap value.

    This discharges the EXISTENTIAL form of sub-bridge 2 — the genuine
    analytic content (constraining `lap` to equal the metric Laplacian
    Δ_g r computed from an actual chart-emergent metric g) remains
    the next-session frontier.
    ════════════════════════════════════════════════════════════════════════ -/

open UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit in
/-- **SubBridge2 existential discharge**:  for any smooth wave field,
    spacetime point, and prescribed Laplacian value, the SubBridge2
    proposition holds — witnessed by constructing the `CurvedWaveData`
    that bundles the wave-field snapshot with the prescribed lap. -/
theorem SubBridge2_realizable
    (sw : LohmillerSlotineCalculus.SmoothWaveField) (x t : ℝ) (lap : ℝ) :
    SubBridge2_HauptvermutungLaplacianControl sw x t lap :=
  ⟨{ toWaveData := LohmillerSlotineCalculus.WaveData.atPoint sw x t
     metricLaplacianR := lap }, rfl, rfl⟩

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — CONNECTION TO  LohmillerSlotineContinuumLimit.SubBridge2

    The continuum-limit scaffolding states sub-bridge 2 in the form
    "there exists a CurvedWaveData whose metric Laplacian equals a
    prescribed scalar."  The abstract framework here is the natural
    place to PRODUCE that scalar:  the limit of a discrete Laplacian
    family acting on the dressing magnitude r = √(Q² + P²).
    ════════════════════════════════════════════════════════════════════════ -/

/-- The abstract sub-bridge 2 in `LohmillerSlotineContinuumLimit` is
    EQUIVALENT to existence of a `CurvedWaveData` realizing the
    prescribed Laplacian value at a point.  The Weak/Uniform
    convergence framework above is the natural place to PRODUCE this
    Laplacian value from a discrete sequence acting on the dressing
    magnitude.  Stated structurally here. -/
def realizesSubBridge2 {X : Type*}
    (_ : DiscreteLaplacianFamily X) (_ : MetricLaplacian X)
    (_ : Set X) : Prop :=
  True   -- placeholder — actual realization requires the discrete K/P
         -- sequence to be wired through DiscreteAmplitudeSequence and
         -- back through Δ;  sub-bridge 1 and 2 plug in together.

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — STATUS

    The first real theorem of sub-bridge 2 is closed:
      `uniformOnCompacts_implies_weakChartwise`
    (uniform-on-compacts convergence on a chart implies pointwise
    weak chartwise convergence on the same chart).

    The first concrete CONVERGENCE TARGET is stated but proof deferred:
      `FiniteDifferenceLaplacian1D_ConvergesAt`
    (1D centered finite-difference Laplacian → second derivative).

    Next session targets, in order:
      (i)   Prove `FiniteDifferenceLaplacian1D_ConvergesAt` for ContDiff 2 φ
            using Mathlib Taylor remainder.
      (ii)  Lift to multi-dimensional uniform lattice (still flat metric).
      (iii) Move to curved metric via local chart + bounded geometry.
      (iv)  Patch globally via partition of unity.

    Each is a stand-alone milestone, in increasing order of analytic
    difficulty.
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotineSubBridge2
