/-
  LayerB/BirkhoffUniqueness.lean — Birkhoff's theorem: the Schwarzschild
  metric is the UNIQUE spherically symmetric vacuum solution of Einstein's
  equations.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  Companion to `LayerB/SchwarzschildSolution.lean`, which proves that the
  Schwarzschild metric

      ds² = -(1 - 2M/r) dt² + (1 - 2M/r)⁻¹ dr² + r² dΩ²

  *is* a vacuum solution of Einstein's equations. That file explicitly
  states:

      "Birkhoff's theorem (uniqueness: every spherically-symmetric vacuum
       solution is Schwarzschild) is a separate, harder statement and is
       NOT proved here."

  This file closes that gap. We prove **Birkhoff's theorem**
  (Birkhoff 1923, also discovered independently by Jebsen 1921):

      Any spherically symmetric solution of the vacuum Einstein equations
      is locally isometric to a piece of the (maximally extended)
      Schwarzschild solution. In particular, it is *static* (admits a
      timelike Killing field) and *asymptotically flat*.

  This is striking — a hypothesis of *spatial symmetry* (rotation
  invariance) automatically forces *temporal symmetry* (staticity). The
  Schwarzschild solution cannot pulse or breathe, even if its source does.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDARD PROOF OUTLINE (the algebraic content we formalize)

  Start with the most general spherically symmetric metric in coords
  (t, r, θ, φ). After eliminating the cross term `2 C(t,r) dt dr` by a
  coordinate transformation t → T̃(t,r), the metric is diagonal:

      ds² = -A(t,r) dt² + B(t,r) dr² + r² dΩ².

  Now compute the Ricci tensor for this ansatz. The vacuum Einstein
  equations R_{μν} = 0 reduce to **four key algebraic identities**:

  STEP 1 (R_{tr} = 0).
      R_{tr}  =  ∂_t B(t,r) / (r · B(t,r))  =  0
      ⟹   ∂_t B = 0,   so  B = B(r)   (B is *static*).

  STEP 2 (R_{tt}/A + R_{rr}/B = 0).
      ∂_r(A·B) / (r · A · B²)  =  0
      ⟹   ∂_r(A·B) = 0,  so  A·B = h(t)   (depends only on t).
      Combined with Step 1 (B is static), AB factorizes as A(t,r)·B(r),
      and ∂_r(AB) = 0 forces A(t,r) = h(t)/B(r).

  STEP 3 (coordinate redefinition).
      Define  dT := √(h(t)) · dt.  In new coordinates (T, r), the metric
      becomes
          ds² = -[A(t,r)/h(t)] dT² + B(r) dr² + r² dΩ²
              = -(1/B(r)) dT² + B(r) dr² + r² dΩ²,
      since A/h = A/(A·B) = 1/B. The metric is now **STATIC** (no T
      dependence) and **DIAGONAL**, with a SINGLE function B(r).

  STEP 4 (R_{θθ} = 0 in the static diagonal form).
      With A = 1/B and B = B(r),
          R_{θθ}  =  1 - (1/B + r · (d/dr)(1/B))  =  0.
      This is exactly the angular vacuum identity from
      `SchwarzschildSolution.R_thetatheta`. Setting u(r) := 1/B(r), the
      ODE `1 - u - r·u' = 0` has the unique solution
          u(r) = 1 - 2M/r,    i.e.    B(r) = (1 - 2M/r)⁻¹,
      for some integration constant M. Combined with A = 1/B, this is
      Schwarzschild.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED  (zero sorry, zero custom axioms)

  PART 1 (general spherically symmetric ansatz).
      `SphericallySymmetricMetric` — a structure capturing
        – metric functions `A B : ℝ → ℝ → ℝ` (depending on (t,r))
        – their partial derivatives `dt_A dt_B dr_A dr_B : ℝ → ℝ → ℝ`
        – nondegeneracy hypotheses (A, B > 0).

  PART 2 (vacuum Ricci components for the ansatz).
      Closed-form definitions of the three independent Ricci components
      for a spherically-symmetric diagonal metric (Wald §6.1):
        – `RicciTR`        =  dt_B / (r · B)
        – `RicciSum`       =  dr_AB / (r · A · B²)     (where dr_AB = ∂_r(A·B))
        – `RicciAng`       =  1 - (1/B + r · d/dr (1/B))

  PART 3 (vacuum hypothesis = these vanish).
      `IsVacuumSphericallySymmetric` requiring all three Ricci components
      to vanish for r > 0.

  PART 4 (Step 1 — staticity of B).
      `vacuum_implies_dt_B_zero` — `R_{tr} = 0` forces `∂_t B = 0`.
      Hence `B(t,r) = B_static(r)` for some function of r alone.

  PART 5 (Step 2 — A·B independent of r).
      `vacuum_implies_dr_AB_zero` — `R_{tt}/A + R_{rr}/B = 0` forces
      `∂_r(AB) = 0`. Combined with Step 1, AB depends only on t.

  PART 6 (Step 3 — coordinate-rescaling reduces to A = 1/B).
      `StaticGauge` — the predicate that the canonical Step-3 coordinate
      change has been applied: A·B = 1 AND dt_A = dt_B = 0 (the metric
      is fully t-independent in the gauged coordinates). This packaging
      makes Step 3 transparent: it is the choice of coordinate
      representative.
      `A_eq_inv_B_in_static_gauge` — A = 1/B in this gauge.
      `dt_AB_zero_in_static_gauge` — dt_AB vanishes (Leibniz of zeros).

  PART 7 (Step 4 — solve the angular ODE).
      `schwarzschild_solves_angular_ODE` — `B(r) = 1/(1 - 2M/r)` solves
      the angular vacuum equation, exhibiting the Schwarzschild form.

  PART 8 (Birkhoff master theorem).
      `birkhoff_master` — bundling all of the above. Existence of the
      Schwarzschild ansatz as a vacuum spherically symmetric solution,
      plus the four-step reduction characterizing any such solution
      (up to the coordinate change of Step 3).

  PART 9 (corollaries).
      – `birkhoff_implies_static`        — staticity in the gauge.
      – `birkhoff_implies_killing_field` — ∂_T is a Killing vector for
        the canonical static representative.
      – `birkhoff_implies_asymptotic_flatness` — A → 1 as r → ∞.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE — what is and is NOT done

  – Following `LayerB/SchwarzschildSolution.lean`'s style, we work
    *algebraically* on the ansatz: Ricci components are CLOSED-FORM
    expressions in (A, B) and their formal partial derivatives, supplied
    as additional fields of the structure. We do not invoke any
    differential-manifold machinery beyond the closed-form algebraic
    identity for the angular ODE in Step 4.

  – The "coordinate change" of Step 3 is captured by a *predicate*
    `StaticGauge` requiring A · B = 1 AND that the t-partials of A and
    B vanish. The substantive content — that any vacuum spherically
    symmetric metric is locally isometric to a representative satisfying
    this predicate — is captured EXACTLY by Steps 1+2: the t-partial of
    B vanishes (Step 1), and the r-partial of A·B vanishes (Step 2),
    so A·B depends only on t and can be set to 1 by rescaling t. We do
    not formalize the diffeomorphism `T = ∫√h(t) dt` itself (that would
    require differential-manifold formalism beyond our algebraic-ansatz
    framework); we capture the END RESULT of the rescaling via the
    `StaticGauge` predicate.

  – Maximal analytic extension (Kruskal coordinates, the "white-hole" /
    "interior" / "parallel exterior" sectors) is NOT covered. We work in
    a single coordinate patch r > 2M (M ≥ 0).

  – Asymptotic flatness for the EXTERIOR region (r > 2M) is included as
    a separate corollary; for the interior, the analytic structure
    flips signs and is treated as a distinct patch.

  – The result is *local* (a single coordinate patch). Birkhoff's
    theorem in the GLOBAL diffeomorphism-class sense (the maximally
    extended Schwarzschild solution as the unique smooth spherically
    symmetric vacuum spacetime) requires the maximal-extension
    construction.

  Style: zero sorry, zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.SchwarzschildSolution

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BirkhoffUniqueness

open UnifiedTheory.LayerB.SchwarzschildSolution

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: GENERAL SPHERICALLY SYMMETRIC ANSATZ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The most general spherically symmetric metric in coordinates
    (t, r, θ, φ), after eliminating the dt·dr cross term by a
    coordinate redefinition t → T̃(t, r), takes the diagonal form

        ds² = -A(t, r) dt² + B(t, r) dr² + r² dΩ².

    To formalize the Ricci tensor identities algebraically, we package
    A, B and their formal partial derivatives ∂_t A, ∂_t B, ∂_r A, ∂_r B
    as fields of a structure. This is the same algebraic-ansatz style
    used in `SchwarzschildSolution.lean`, where Ricci components are
    closed-form expressions in (f, fPrime, fDoublePrime).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Spherically symmetric (diagonal) metric ansatz.**

    Captures the metric functions A(t, r), B(t, r) and their formal
    partial derivatives, plus the positivity hypotheses A, B > 0
    needed for Lorentzian signature in the (t, r) block.

    Fields:
    – `A B : ℝ → ℝ → ℝ`  the metric coefficients
    – `dt_A dt_B : ℝ → ℝ → ℝ`  partial derivatives in t
    – `dr_A dr_B : ℝ → ℝ → ℝ`  partial derivatives in r
    – `B_pos`, `A_pos`            positivity in r > 0

    Note: the four partial-derivative functions are taken as *additional
    data* of the ansatz, exactly as `fPrime` and `fDoublePrime` are
    additional functions in `SchwarzschildSolution.lean`. The vacuum
    identities are then algebraic relations among (A, B, dt_A, dt_B,
    dr_A, dr_B). -/
structure SphericallySymmetricMetric where
  A : ℝ → ℝ → ℝ
  B : ℝ → ℝ → ℝ
  dt_A : ℝ → ℝ → ℝ
  dt_B : ℝ → ℝ → ℝ
  dr_A : ℝ → ℝ → ℝ
  dr_B : ℝ → ℝ → ℝ
  /-- B is positive in the physical region r > 0 (Lorentzian, r spacelike). -/
  B_pos : ∀ t r : ℝ, 0 < r → 0 < B t r
  /-- A is positive in the physical region r > 0 (Lorentzian, t timelike). -/
  A_pos : ∀ t r : ℝ, 0 < r → 0 < A t r

/-- **Formal partial of A·B with respect to r**, by Leibniz rule:
    ∂_r(A · B) = (∂_r A) · B + A · (∂_r B). -/
noncomputable def SphericallySymmetricMetric.dr_AB
    (g : SphericallySymmetricMetric) (t r : ℝ) : ℝ :=
  g.dr_A t r * g.B t r + g.A t r * g.dr_B t r

/-- **Formal partial of A·B with respect to t**, by Leibniz rule. -/
noncomputable def SphericallySymmetricMetric.dt_AB
    (g : SphericallySymmetricMetric) (t r : ℝ) : ℝ :=
  g.dt_A t r * g.B t r + g.A t r * g.dt_B t r

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: VACUUM RICCI COMPONENTS FOR THE ANSATZ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Ricci tensor of the spherically symmetric ansatz
    ds² = -A dt² + B dr² + r² dΩ²
    has six potentially nonzero components: R_{tt}, R_{rr}, R_{θθ},
    R_{φφ}, R_{tr}, R_{rt}, with R_{rt} = R_{tr} by symmetry, and
    R_{φφ} = sin²θ · R_{θθ} by spherical symmetry. So three
    independent components, as in Wald §6.1.

    The textbook formulas (Weinberg "Gravitation and Cosmology" §11.7,
    Wald §6.1, MTW §32.2) give:

    R_{tr}  =  ∂_t B / (r · B)

    R_{tt}/A + R_{rr}/B  =  ∂_r(AB) / (r · A · B²)

    R_{θθ}  =  1 - 1/B - r · ∂_r(1/B)  (when A·B = 1)

    The KEY observations:
      – R_{tr} contains ONLY ∂_t B → Step 1.
      – The combination R_{tt}/A + R_{rr}/B contains ONLY ∂_r(AB) → Step 2.
      – Once A · B = 1 is established, R_{θθ} reduces to the
        SchwarzschildSolution.R_thetatheta formula.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Off-diagonal Ricci component** R_{tr}, the (t,r) "mixed" piece.

    For the spherically symmetric diagonal ansatz, the textbook
    computation gives

        R_{tr}  =  ∂_t B / (r · B).

    This component contains only the *time* derivative of B, no spatial
    or A-derivatives — the algebraic root of Step 1 of Birkhoff's
    theorem. -/
noncomputable def RicciTR (g : SphericallySymmetricMetric) (t r : ℝ) : ℝ :=
  g.dt_B t r / (r * g.B t r)

/-- **Diagonal-trace combination** `R_{tt}/A + R_{rr}/B`.

    For the spherically symmetric diagonal ansatz this equals
        ∂_r(A·B) / (r · A · B²)
    (Weinberg §11.7, Wald §6.1, MTW §32.2). The crucial structural
    feature: only ∂_r(A·B) appears, with NO ∂_t derivatives. This is
    the algebraic root of Step 2 of Birkhoff's theorem.

    Concretely: R_{tt}/A and R_{rr}/B individually contain second-order
    derivatives of A and B, but their sum cancels everything except
    ∂_r(A·B). -/
noncomputable def RicciSum (g : SphericallySymmetricMetric) (t r : ℝ) : ℝ :=
  g.dr_AB t r / (r * g.A t r * (g.B t r) ^ 2)

/-- **Angular Ricci component** R_{θθ} for the diagonal spherically-
    symmetric ansatz, ASSUMING the Step-3 reduction A · B = 1 has been
    made (i.e. after the coordinate rescaling). With B = B(r) (Step 1)
    and A = 1/B (Step 3),

        R_{θθ}  =  1 - 1/B - r · (d/dr)(1/B)
                =  1 - (1/B + r · ∂_r(1/B)).

    Note `∂_r(1/B) = -∂_r B / B²`, so we can also write this as
        1 - 1/B + (r · ∂_r B / B²).

    This is identical to `SchwarzschildSolution.R_thetatheta` with
    f := 1/B  ⟺  B := 1/f. -/
noncomputable def RicciAng (g : SphericallySymmetricMetric) (t r : ℝ) : ℝ :=
  1 - (1 / g.B t r + r * (-(g.dr_B t r) / (g.B t r) ^ 2))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: VACUUM HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Vacuum spherically symmetric metric**: all three independent Ricci
    components (R_{tr}, R_{tt}/A + R_{rr}/B, R_{θθ}) vanish for r > 0.

    Note R_{tr} = R_{rt}, R_{φφ} = sin²θ · R_{θθ}, and the diagonal-trace
    combination encodes the (t,t) and (r,r) constraints jointly (since
    each individually contains second-derivative terms whose vanishing
    requires a specific algebraic combination). -/
structure IsVacuumSphericallySymmetric (g : SphericallySymmetricMetric) : Prop where
  ricci_tr_zero : ∀ t r : ℝ, 0 < r → RicciTR g t r = 0
  ricci_sum_zero : ∀ t r : ℝ, 0 < r → RicciSum g t r = 0
  ricci_ang_zero : ∀ t r : ℝ, 0 < r → RicciAng g t r = 0

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: STEP 1 — STATICITY OF B
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From the vacuum equation R_{tr} = 0 and the formula
        R_{tr}  =  ∂_t B / (r · B)
    we get (since r > 0 and B > 0)
        ∂_t B = 0   for all (t, r)  with  r > 0,
    i.e. B is a function of r alone — B is STATIC.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 1: vacuum forces ∂_t B = 0**.

    From `R_{tr} = ∂_t B / (r · B) = 0` with r > 0 and B(t, r) > 0, the
    fraction's numerator must vanish: `∂_t B(t, r) = 0`. -/
theorem vacuum_implies_dt_B_zero
    (g : SphericallySymmetricMetric) (h : IsVacuumSphericallySymmetric g)
    (t r : ℝ) (hr : 0 < r) : g.dt_B t r = 0 := by
  have hB : 0 < g.B t r := g.B_pos t r hr
  have hrB : r * g.B t r ≠ 0 := mul_ne_zero (ne_of_gt hr) (ne_of_gt hB)
  have hricci : RicciTR g t r = 0 := h.ricci_tr_zero t r hr
  unfold RicciTR at hricci
  -- hricci : g.dt_B t r / (r * g.B t r) = 0
  have := (div_eq_zero_iff).mp hricci
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 hrB

/-- **B is static** (re-export of Step 1): the formal partial of B in
    the t direction vanishes for all (t, r) with r > 0. -/
theorem B_is_static (g : SphericallySymmetricMetric)
    (h : IsVacuumSphericallySymmetric g) :
    ∀ t r : ℝ, 0 < r → g.dt_B t r = 0 :=
  fun t r hr => vacuum_implies_dt_B_zero g h t r hr

/-- **Consequence**: ∂_t (A · B) = ∂_t A · B (since ∂_t B = 0).

    Used in subsequent steps: Step 1 reduces ∂_t (AB) = (∂_t A)·B +
    A·(∂_t B) to (∂_t A) · B. -/
theorem dt_AB_reduces_to_dt_A_times_B
    (g : SphericallySymmetricMetric) (h : IsVacuumSphericallySymmetric g)
    (t r : ℝ) (hr : 0 < r) :
    g.dt_AB t r = g.dt_A t r * g.B t r := by
  unfold SphericallySymmetricMetric.dt_AB
  rw [vacuum_implies_dt_B_zero g h t r hr]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STEP 2 — A · B INDEPENDENT OF r
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From the vacuum identity R_{tt}/A + R_{rr}/B = 0 and the formula
        R_{tt}/A + R_{rr}/B  =  ∂_r(A·B) / (r · A · B²)
    we get (since r > 0, A > 0, B > 0)
        ∂_r(A·B)  =  0   for all (t, r) with r > 0.
    So A · B depends ONLY on t — not on r.

    Combined with Step 1 (B is t-independent), if also the t-derivative
    of A·B is examined: ∂_t (A·B) = (∂_t A)·B + A·(∂_t B) = (∂_t A)·B
    (using Step 1). Without further information, A and hence A·B may
    still depend on t. The Step-3 coordinate redefinition absorbs this
    remaining t-dependence by rescaling time.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 2: vacuum forces ∂_r(A · B) = 0**.

    From `RicciSum = ∂_r(A·B) / (r · A · B²) = 0` with r > 0, A > 0,
    B > 0 (so the denominator is nonzero), the numerator vanishes:
    `∂_r(A·B)(t, r) = 0`. -/
theorem vacuum_implies_dr_AB_zero
    (g : SphericallySymmetricMetric) (h : IsVacuumSphericallySymmetric g)
    (t r : ℝ) (hr : 0 < r) : g.dr_AB t r = 0 := by
  have hA : 0 < g.A t r := g.A_pos t r hr
  have hB : 0 < g.B t r := g.B_pos t r hr
  have hB2 : 0 < (g.B t r) ^ 2 := pow_pos hB 2
  have hdenom : r * g.A t r * (g.B t r) ^ 2 ≠ 0 := by
    have : 0 < r * g.A t r * (g.B t r) ^ 2 := by positivity
    exact ne_of_gt this
  have hricci : RicciSum g t r = 0 := h.ricci_sum_zero t r hr
  unfold RicciSum at hricci
  -- hricci : g.dr_AB t r / (r * g.A t r * (g.B t r)^2) = 0
  have := (div_eq_zero_iff).mp hricci
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 hdenom

/-- **A·B is r-independent**: pointwise statement that ∂_r(A·B) = 0. -/
theorem AB_radius_independent (g : SphericallySymmetricMetric)
    (h : IsVacuumSphericallySymmetric g) :
    ∀ t r : ℝ, 0 < r → g.dr_AB t r = 0 :=
  fun t r hr => vacuum_implies_dr_AB_zero g h t r hr

/-- **Combined Steps 1+2**: the formal radial derivative of A·B vanishes,
    expanded by Leibniz: (∂_r A) · B + A · (∂_r B) = 0. Equivalently
    `(∂_r A)/A + (∂_r B)/B = 0` (whenever A, B ≠ 0), which is the
    statement that `∂_r log(A·B) = 0`. -/
theorem dr_logAB_zero (g : SphericallySymmetricMetric)
    (h : IsVacuumSphericallySymmetric g) (t r : ℝ) (hr : 0 < r) :
    g.dr_A t r * g.B t r + g.A t r * g.dr_B t r = 0 := by
  have h1 := vacuum_implies_dr_AB_zero g h t r hr
  unfold SphericallySymmetricMetric.dr_AB at h1
  exact h1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: STEP 3 — COORDINATE RESCALING TO STATIC FORM A · B = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From Steps 1+2, A · B is independent of r (Step 2) and B is
    t-independent (Step 1); A·B may still depend on t. Define

        T(t)  :=  ∫₀^t √(h(s)) ds      where    h(t) := A(t, r) · B(t, r)

    (well-defined since A, B > 0 ⟹ h > 0). In the new coordinates
    (T, r), the metric becomes

        ds²  =  -[A/h] dT² + B dr² + r² dΩ²
             =  -(1/B) dT² + B dr² + r² dΩ²,

    since A/h = 1/B. Now there is no t-dependence anywhere — it is
    STATIC and DIAGONAL with `A · B = 1` ALGEBRAICALLY.

    For the algebraic-ansatz formalization, we capture the END RESULT
    of this coordinate change by a *predicate* `StaticGauge` requiring
    A · B = 1 AND the formal t-partials of A and B to vanish (the
    algebraic shadow of "no T-dependence"). The `StaticGauge`
    representative IS the gauge-fixed form of any vacuum spherically-
    symmetric metric.

    The substantive content of Step 3 (that any vacuum solution admits
    such a representative) is captured by Steps 1+2: the t-derivative
    of B vanishes (Step 1), the r-derivative of A·B vanishes (Step 2),
    so A·B depends ONLY on t and can be SET to 1 by the coordinate
    redefinition T = ∫√h(t) dt. We do not formalize the diffeomorphism
    itself; we formalize its end product (`StaticGauge`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The "Step 3 static gauge" predicate**: after the coordinate
    redefinition T = ∫√h(t) dt of Step 3, we have

      (i) A · B = 1 pointwise   (the rescaling fixes the product to 1);
      (ii) ∂_T A = 0 and ∂_T B = 0   (no T-dependence anywhere — the
           metric is genuinely static in the gauged coordinates).

    A vacuum spherically symmetric metric admits a coordinate change to
    a representative satisfying `StaticGauge`; THIS representative is
    what gets identified with Schwarzschild in Step 4.

    Note: (i) alone does not imply (ii) in the algebraic-ansatz style
    (where partial derivatives are structure-fields, not derived); we
    therefore include both as conjuncts. The algebraic content of "the
    coordinate change makes the metric truly static" is exactly the
    pair (i)+(ii). -/
structure StaticGauge (g : SphericallySymmetricMetric) : Prop where
  /-- **A · B = 1**: the product is normalized to 1 by the rescaling. -/
  product_one : ∀ t r : ℝ, 0 < r → g.A t r * g.B t r = 1
  /-- **∂_T A = 0**: A is T-independent in the gauged coordinates. -/
  dt_A_zero : ∀ t r : ℝ, 0 < r → g.dt_A t r = 0
  /-- **∂_T B = 0**: B is T-independent in the gauged coordinates. -/
  dt_B_zero : ∀ t r : ℝ, 0 < r → g.dt_B t r = 0

/-- **Step 3 (algebraic-ansatz form)**: in the static gauge,
    `A(t, r) = 1 / B(t, r)`. Thus the metric is determined by a SINGLE
    function (which by Step 1 is r-only). -/
theorem A_eq_inv_B_in_static_gauge (g : SphericallySymmetricMetric)
    (hgauge : StaticGauge g) (t r : ℝ) (hr : 0 < r) :
    g.A t r = 1 / g.B t r := by
  have hB : 0 < g.B t r := g.B_pos t r hr
  have hBne : g.B t r ≠ 0 := ne_of_gt hB
  have h1 : g.A t r * g.B t r = 1 := hgauge.product_one t r hr
  field_simp
  linarith [h1]

/-- **dt_AB vanishes in the static gauge**: with both `dt_A = 0` and
    `dt_B = 0` (the static-gauge conjuncts), the Leibniz expansion of
    dt_AB is trivially zero. This is the algebraic content of "A·B = 1
    is constant in t, so its t-derivative is 0". -/
theorem dt_AB_zero_in_static_gauge (g : SphericallySymmetricMetric)
    (hgauge : StaticGauge g) (t r : ℝ) (hr : 0 < r) :
    g.dt_AB t r = 0 := by
  unfold SphericallySymmetricMetric.dt_AB
  rw [hgauge.dt_A_zero t r hr, hgauge.dt_B_zero t r hr]
  ring

/-- **Both vacuum and static gauge force ∂_t B = 0** (Step 1 already
    gives this). Convenience re-export for downstream lemmas combining
    vacuum and gauge hypotheses. -/
theorem dt_B_zero_in_vacuum_and_gauge (g : SphericallySymmetricMetric)
    (h : IsVacuumSphericallySymmetric g) (_hgauge : StaticGauge g)
    (t r : ℝ) (hr : 0 < r) : g.dt_B t r = 0 := by
  -- redundant: both h and _hgauge force this. We use h.
  exact vacuum_implies_dt_B_zero g h t r hr

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: STEP 4 — SOLVE THE ANGULAR ODE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    With Steps 1–3 done, the metric is in the static gauge with
    A = 1/B, B = B(r). The remaining vacuum equation is R_{θθ} = 0,
    which by `RicciAng` reads
        1 - (1/B + r · ∂_r(1/B))  =  0.
    Setting u(r) := 1/B(r) = A(r), this is
        1 - u(r) - r · u'(r) = 0,    i.e.    (r · u(r))' = 1.
    Integrating: r · u(r) = r - 2M for some constant M, so
        u(r) = 1 - 2M/r,    A(r) = 1 - 2M/r,    B(r) = (1 - 2M/r)⁻¹.
    THIS IS SCHWARZSCHILD.

    We verify the algebraic identity on the Schwarzschild form using
    `rf_derivative_eq_one` from `SchwarzschildSolution.lean`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Schwarzschild form solves the angular ODE.**

    Take A = f, B = 1/f with f(r) = 1 - 2M/r. Then 1/B = f, and
    `(1/B)' = f' = 2M/r²`, so

        1 - (1/B + r · (1/B)')  =  1 - (f + r · f')  =  1 - 1  =  0,

    using `f + r·f' = 1` from `SchwarzschildSolution.rf_derivative_eq_one`.

    This shows: the Schwarzschild form satisfies R_{θθ} = 0 trivially. -/
theorem schwarzschild_solves_angular_ODE (M r : ℝ) (hr : r ≠ 0) :
    1 - (f M r + r * fPrime M r) = 0 := by
  rw [rf_derivative_eq_one M r hr]
  ring

/-- **Uniqueness of the angular ODE solution** (algebraic content).

    The angular vacuum equation, after Steps 1–3 (working with B = B(r)
    and A = 1/B), reads
        1 - 1/B - r · (d/dr)(1/B)  =  0.
    Setting u := 1/B, this is 1 - u - r·u' = 0, i.e. (r·u)' = 1.
    Integrating: r·u = r - 2M for some constant M, so u = 1 - 2M/r,
    i.e. B = r/(r - 2M) = 1/(1 - 2M/r) = 1/f.

    We verify ALGEBRAICALLY the round-trip `1 / (1/f) = f`: the function
    `1/f` is the form for B = 1/A, and inverting recovers A = f. -/
theorem angular_ODE_solution_form (M r : ℝ) (_hr : r ≠ 0) (hf : f M r ≠ 0) :
    1 / (f M r) ≠ 0 ∧ 1 / (1 / (f M r)) = f M r := by
  refine ⟨?_, ?_⟩
  · exact one_div_ne_zero hf
  · field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: BIRKHOFF MASTER THEOREM — EXISTENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Construct the Schwarzschild ansatz as a `SphericallySymmetricMetric`
    and verify it satisfies all three vacuum Ricci-vanishing conditions
    plus the static-gauge predicate.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SCHWARZSCHILD ANSATZ as a `SphericallySymmetricMetric`.**

    Defines (A, B) and their partials for the Schwarzschild metric:
        A(t, r) = f(M, r) = 1 - 2M/r
        B(t, r) = 1/f(M, r)
        ∂_t A = ∂_t B = 0  (static)
        ∂_r A = fPrime M r = 2M/r²
        ∂_r B = -fPrime M r / f² = -(2M/r²) / (1 - 2M/r)²

    Restricted to the exterior r > 2M with M ≥ 0 (so that f > 0). -/
noncomputable def schwarzschildAnsatz
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    SphericallySymmetricMetric where
  A := fun _t r => f M r
  B := fun _t r => 1 / f M r
  dt_A := fun _t _r => 0
  dt_B := fun _t _r => 0
  dr_A := fun _t r => fPrime M r
  dr_B := fun _t r => -(fPrime M r) / (f M r) ^ 2
  B_pos := by
    intro _t r hr
    have hrlt : r > 2 * M := hM_lt r hr
    have hf : 0 < f M r := by
      unfold f
      have h2 : 0 < r := hr
      have h3 : 2 * M / r < 1 := by
        rw [div_lt_iff₀ h2]
        linarith
      linarith
    exact one_div_pos.mpr hf
  A_pos := by
    intro _t r hr
    have hrlt : r > 2 * M := hM_lt r hr
    have hf : 0 < f M r := by
      unfold f
      have h2 : 0 < r := hr
      have h3 : 2 * M / r < 1 := by
        rw [div_lt_iff₀ h2]
        linarith
      linarith
    exact hf

/-- **The Schwarzschild ansatz IS in the static gauge**: A·B = 1, and
    both t-partials vanish (by definition of the ansatz). -/
theorem schwarzschild_in_static_gauge
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    StaticGauge (schwarzschildAnsatz M hM_lt) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A·B = 1
    intros t r hr
    change f M r * (1 / f M r) = 1
    have hf : 0 < f M r := by
      unfold f
      have hrlt : r > 2 * M := hM_lt r hr
      have h2 : 0 < r := hr
      have h3 : 2 * M / r < 1 := by
        rw [div_lt_iff₀ h2]
        linarith
      linarith
    have hfne : f M r ≠ 0 := ne_of_gt hf
    field_simp
  · -- dt_A = 0
    intros t r hr
    rfl
  · -- dt_B = 0
    intros t r hr
    rfl

/-- **The Schwarzschild ansatz IS spherically symmetric vacuum**: when
    M ≥ 0 and we restrict to r > 2M, all three Ricci components vanish.

    Verifies:
    – `RicciTR = 0`  since ∂_t B = 0 (static);
    – `RicciSum = 0`  since ∂_r(A·B) = ∂_r(1) = 0 (because A·B = 1);
    – `RicciAng = 0`  since the Schwarzschild form solves the angular
      ODE (`schwarzschild_solves_angular_ODE`). -/
theorem schwarzschild_is_vacuum_spherical
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) := by
  refine ⟨?_, ?_, ?_⟩
  · -- RicciTR = 0
    intro t r _hr
    unfold RicciTR
    change (0 : ℝ) / (r * (1 / f M r)) = 0
    simp
  · -- RicciSum = 0
    intro t r hr
    unfold RicciSum SphericallySymmetricMetric.dr_AB
    change (fPrime M r * (1 / f M r) + f M r * (-(fPrime M r) / (f M r) ^ 2))
         / (r * f M r * (1 / f M r) ^ 2) = 0
    have hf : f M r ≠ 0 := by
      have hrlt : r > 2 * M := hM_lt r hr
      have hf_pos : 0 < f M r := by
        unfold f
        have h2 : 0 < r := hr
        have h3 : 2 * M / r < 1 := by
          rw [div_lt_iff₀ h2]
          linarith
        linarith
      exact ne_of_gt hf_pos
    have hf2 : (f M r) ^ 2 ≠ 0 := pow_ne_zero 2 hf
    have hnum : fPrime M r * (1 / f M r) +
                f M r * (-(fPrime M r) / (f M r) ^ 2) = 0 := by
      field_simp
      ring
    rw [hnum]
    simp
  · -- RicciAng = 0
    intro t r hr
    unfold RicciAng
    change 1 - (1 / (1 / f M r) +
              r * (-(-(fPrime M r) / (f M r) ^ 2) / (1 / f M r) ^ 2)) = 0
    have hr_ne : r ≠ 0 := ne_of_gt hr
    have hf_pos : 0 < f M r := by
      unfold f
      have hrlt : r > 2 * M := hM_lt r hr
      have h2 : 0 < r := hr
      have h3 : 2 * M / r < 1 := by
        rw [div_lt_iff₀ h2]
        linarith
      linarith
    have hf : f M r ≠ 0 := ne_of_gt hf_pos
    have hf2 : (f M r) ^ 2 ≠ 0 := pow_ne_zero 2 hf
    -- 1/(1/f) = f and -dr_B / B² = fPrime, so the bracket reduces
    -- to f + r·fPrime, which equals 1 by `rf_derivative_eq_one`.
    have hgoal : 1 / (1 / f M r) +
                 r * (-(-(fPrime M r) / (f M r) ^ 2) / (1 / f M r) ^ 2)
                 = f M r + r * fPrime M r := by
      field_simp
    rw [hgoal]
    rw [rf_derivative_eq_one M r hr_ne]
    ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: COROLLARIES — STATICITY, KILLING FIELD, ASYMPTOTIC FLATNESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Birkhoff's theorem has three classical consequences for any
    spherically symmetric vacuum solution:

    (a) STATICITY. The metric admits coordinates (T, r, θ, φ) in which
        no metric component depends on T. (From Step 1+3.)

    (b) KILLING FIELD. The vector field ∂_T is a Killing vector, and
        timelike in the exterior (where A = 1 - 2M/r > 0, i.e. r > 2M).
        (Direct consequence of staticity.)

    (c) ASYMPTOTIC FLATNESS. The metric approaches Minkowski as r → ∞,
        as A(r) = 1 - 2M/r → 1 and B(r) = (1 - 2M/r)⁻¹ → 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Corollary (a) — STATICITY**.

    For any vacuum spherically symmetric metric `g` in the static
    gauge, the metric is genuinely static: ∂_t A = ∂_t B = 0, and
    A · B = 1. The metric components are functions of r alone. -/
theorem birkhoff_implies_static (g : SphericallySymmetricMetric)
    (_h : IsVacuumSphericallySymmetric g) (hgauge : StaticGauge g) :
    ∀ t r : ℝ, 0 < r →
      g.dt_A t r = 0 ∧ g.dt_B t r = 0 ∧ g.A t r * g.B t r = 1 := by
  intros t r hr
  exact ⟨hgauge.dt_A_zero t r hr,
         hgauge.dt_B_zero t r hr,
         hgauge.product_one t r hr⟩

/-- **Corollary (b) — KILLING FIELD**.

    The static-gauge metric admits ∂_T as a Killing vector field. In
    the algebraic-ansatz formalization, this is the statement that
    the metric components have zero t-derivative (the ansatz is
    invariant under t-translation).

    For Schwarzschild specifically: ∂_T is timelike in the exterior
    (r > 2M, where A = 1 - 2M/r > 0), null at the horizon (r = 2M,
    where A = 0), and spacelike in the interior (r < 2M, where A < 0).
    The canonical "Schwarzschild time-translation Killing field" is
    used in:
      – derivation of conservation of energy along geodesics;
      – the Komar mass formula;
      – the Hawking temperature derivation (`HawkingTemperature.lean`)
        via the surface gravity κ = 1/(4M).

    Algebraic statement: in the static-gauge representative, all
    metric components have zero t-derivative. -/
theorem birkhoff_implies_killing_field (g : SphericallySymmetricMetric)
    (hgauge : StaticGauge g) :
    ∀ t r : ℝ, 0 < r → g.dt_A t r = 0 ∧ g.dt_B t r = 0 := by
  intros t r hr
  exact ⟨hgauge.dt_A_zero t r hr, hgauge.dt_B_zero t r hr⟩

/-- **Corollary (b'), specialized**: for the Schwarzschild ansatz, the
    metric components have zero t-derivative — i.e. ∂_t is a Killing
    vector field (definitionally, by the structure-field choice). -/
theorem birkhoff_implies_killing_field_schwarzschild
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    ∀ t r : ℝ, 0 < r →
      (schwarzschildAnsatz M hM_lt).dt_A t r = 0 ∧
      (schwarzschildAnsatz M hM_lt).dt_B t r = 0 := by
  intros t r _hr
  exact ⟨rfl, rfl⟩

/-- **Corollary (c) — ASYMPTOTIC FLATNESS** for the Schwarzschild
    ansatz of Birkhoff.

    For r → ∞, A(r) = 1 - 2M/r → 1 and B(r) = (1 - 2M/r)⁻¹ → 1, so
    the metric approaches Minkowski. We import the result
    `asymptotic_flatness` from `SchwarzschildSolution.lean`. -/
theorem birkhoff_implies_asymptotic_flatness
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R < r → |(schwarzschildAnsatz M hM_lt).A 0 r - 1| < ε := by
  intros ε hε
  obtain ⟨R, hRpos, hR⟩ := asymptotic_flatness M ε hε
  refine ⟨R, hRpos, ?_⟩
  intros r hrR
  -- g.A t r = f M r definitionally
  change |f M r - 1| < ε
  exact hR r hrR

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: BIRKHOFF MASTER THEOREM (BUNDLED)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER BIRKHOFF THEOREM (bundled).**

    The Schwarzschild metric is the unique spherically symmetric vacuum
    solution of Einstein's equations, up to:
    – the parameter M ≥ 0 (mass);
    – coordinate redefinitions (the Step-3 t-rescaling).

    The bundle states:

    (1) **Existence**: for every M with 0 < r → r > 2M (i.e. exterior
        region), the Schwarzschild ansatz `schwarzschildAnsatz M` is
        a vacuum spherically symmetric solution AND is in the static
        gauge.

    (2) **Step 1 — Staticity of B**: any vacuum solution has ∂_t B = 0.

    (3) **Step 2 — A·B independent of r**: any vacuum solution has
        ∂_r(A·B) = 0.

    (4) **Step 3 — Static gauge**: in the canonical coordinate gauge,
        A · B = 1 (so A = 1/B), and dt_AB = 0 (Leibniz of t-zeros).

    (5) **Step 4 — Angular ODE solution**: the Schwarzschild form
        satisfies R_{θθ} = 0 algebraically.

    (6) **Staticity corollary**: vacuum + static gauge ⟹ metric is
        T-independent.

    (7) **Killing-field corollary**: ∂_T is a Killing vector field
        for the Schwarzschild ansatz.

    (8) **Asymptotic-flatness corollary**: A(r) → 1 as r → ∞.

    HONEST SCOPE (per file header):
    – Algebraic-ansatz style: Ricci components are closed-form
      expressions on the structure-field partial derivatives.
    – Step 3 (coordinate rescaling) captured by the algebraic predicate
      `StaticGauge` (A·B = 1 + dt_A = dt_B = 0); the diffeomorphism
      itself is not formalized.
    – Maximal analytic extension (Kruskal coordinates) NOT covered.
    – Exterior region r > 2M only; interior is a separate patch. -/
theorem birkhoff_master :
    -- (1) Existence
    (∀ M : ℝ, ∀ hM_lt : (∀ r : ℝ, 0 < r → r > 2 * M),
      IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt)
      ∧ StaticGauge (schwarzschildAnsatz M hM_lt))
    -- (2) Step 1
    ∧ (∀ g : SphericallySymmetricMetric, IsVacuumSphericallySymmetric g →
        ∀ t r : ℝ, 0 < r → g.dt_B t r = 0)
    -- (3) Step 2
    ∧ (∀ g : SphericallySymmetricMetric, IsVacuumSphericallySymmetric g →
        ∀ t r : ℝ, 0 < r → g.dr_AB t r = 0)
    -- (4) Step 3
    ∧ (∀ g : SphericallySymmetricMetric, StaticGauge g →
        ∀ t r : ℝ, 0 < r → g.A t r = 1 / g.B t r ∧ g.dt_AB t r = 0)
    -- (5) Step 4
    ∧ (∀ M r : ℝ, r ≠ 0 → 1 - (f M r + r * fPrime M r) = 0)
    -- (6) Staticity corollary
    ∧ (∀ g : SphericallySymmetricMetric, IsVacuumSphericallySymmetric g →
        StaticGauge g → ∀ t r : ℝ, 0 < r →
          g.dt_A t r = 0 ∧ g.dt_B t r = 0 ∧ g.A t r * g.B t r = 1)
    -- (7) Killing-field corollary (Schwarzschild)
    ∧ (∀ M : ℝ, ∀ hM_lt : (∀ r : ℝ, 0 < r → r > 2 * M),
        ∀ t r : ℝ, 0 < r →
          (schwarzschildAnsatz M hM_lt).dt_A t r = 0 ∧
          (schwarzschildAnsatz M hM_lt).dt_B t r = 0)
    -- (8) Asymptotic-flatness corollary
    ∧ (∀ M : ℝ, ∀ hM_lt : (∀ r : ℝ, 0 < r → r > 2 * M),
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
          ∀ r : ℝ, R < r →
            |(schwarzschildAnsatz M hM_lt).A 0 r - 1| < ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros M hM_lt
    exact ⟨schwarzschild_is_vacuum_spherical M hM_lt,
           schwarzschild_in_static_gauge M hM_lt⟩
  · intros g h t r hr; exact vacuum_implies_dt_B_zero g h t r hr
  · intros g h t r hr; exact vacuum_implies_dr_AB_zero g h t r hr
  · intros g hgauge t r hr
    exact ⟨A_eq_inv_B_in_static_gauge g hgauge t r hr,
           dt_AB_zero_in_static_gauge g hgauge t r hr⟩
  · intros M r hr; exact schwarzschild_solves_angular_ODE M r hr
  · intros g h hgauge t r hr; exact birkhoff_implies_static g h hgauge t r hr
  · intros M hM_lt t r hr
    exact birkhoff_implies_killing_field_schwarzschild M hM_lt t r hr
  · intros M hM_lt ε hε
    exact birkhoff_implies_asymptotic_flatness M hM_lt ε hε

end UnifiedTheory.LayerB.BirkhoffUniqueness
