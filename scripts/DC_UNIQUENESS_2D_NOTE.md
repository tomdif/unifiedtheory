# 2D reduced-DC uniqueness — conjecture refuted (honest result)

**Setup.** Follow-on to the `tropical-nets-lean` idea #1: the repo proves canonical
uniqueness only for convex (`TropicalPoly`) functions; the full ReLU case is nonconvex
(`P − Q`, difference-of-convex). In 1D the *reduced* DC form is unique (Jordan
decomposition of `f'' = μ₊ − μ₋`). I **conjectured this fails in 2D** — that cycle
constraints on edge-curvatures (`E > V`) would force tie-prone compromises and a
counterexample.

**Test.** `scripts/dc_uniqueness_2d.py`. PL `f` on a triangulated grid; minimal-total-
bending DC as an LP:
`min Σ_e slack_e(Q)` s.t. `slack_e(Q) ≥ 0` (Q convex) and `slack_e(Q) ≥ −λ_e(f)`
(P = Q+f convex). Objective is affine-gauge-invariant; non-uniqueness *beyond affine* =
counterexample. Optimal-face dimension probed with 6 random objective tie-breakers.

**Result — the conjecture is refuted.**

| f | creases (cvx/ccv) | min bending | non-affine spread | verdict |
|---|---|---|---|---|
| `x²+y²` (control) | 12 / 0 | 0 | 0 | unique |
| saddle `x²−y²` | 6 / 6 | 5.333 | 4e-15 | unique |
| `|x|−|y|` (sparse creases) | 4 / 4 | 4.000 | 3e-15 | unique |
| monkey `x³−3xy²` | 17 / 17 | 15.000 | 8e-15 | unique |
| checkerboard bumps | 12 / 12 | 16.000 | 6e-15 | unique |

Every case — including symmetric tie-prone ones and the sparse-crease `|x|−|y|` case
where Q has many free edges off f's crease lines (the "off-complex" freedom) — gives a
**unique** reduced DC form mod affine. The cycle coupling does raise the minimal bending
above the facewise-Jordan value (e.g. saddle: 5.333) but does **not** create ties.

**Honest reading.** My counterexample conjecture is wrong; the evidence points the other
way: **reduced (min-total-bending) DC decomposition appears to be unique in 2D**, i.e.
the 1D theorem likely *does* lift. The interesting "new theorem" therefore flips sign:

> **Conjecture (revised).** The minimal-total-bending DC decomposition of a PL function
> on ℝ² is unique up to a shared affine term. Equivalently, behaviorally equivalent 2D
> ReLU networks have identical reduced canonical (P, Q).

**Limitations (not a proof).** Empirical; finite battery; P, Q restricted to a fixed
grid complex (off-grid creases only partially probed via sparse-crease cases); L1
total-bending notion of "reduced."

**Real open frontier = dimension 3.** In ≥3D the curvature of a PL function is genuinely
matrix-valued on codim-1 faces and the obstruction is richer than the scalar 2D case, so
that is where uniqueness most plausibly first fails. The honest next experiment is the
3D analog of this LP. If uniqueness holds there too, the conjecture is "unique in all
dimensions," which would be the actual theorem worth formalizing.

Reproduce: `python3 scripts/dc_uniqueness_2d.py`

---

## 3D result (`scripts/dc_uniqueness_3d.py`) — also unique

Freudenthal tet mesh (6 tets/cell, 3×3×3 = 27 verts, 48 tets, 72 interior faces),
global convexity enforced (every vertex above every tet plane — so the codim-2 = edge
coupling is fully captured).

| f | cvx/ccv faces | min bending | non-affine spread | verdict |
|---|---|---|---|---|
| `x²+y²+z²` (control) | 24/0 | 0 | 0 | unique |
| saddle `x²+y²−2z²` | 16/8 | 32 | 1.4e-14 | unique |
| saddle `x²−y²` | 8/8 | 16 | 6.7e-15 | unique |
| octahedral `\|x\|+\|y\|−\|z\|` | 16/8 | 16 | 2.8e-15 | unique |
| `\|x\|−\|y\|` (sparse) | 8/8 | 16 | 6.7e-15 | unique |
| monkey `x³−3xy²` | 16/16 | 48 | 1.8e-14 | unique |
| triple saddle `xyz` (genuinely 3D) | 18/18 | 30 | 1.1e-14 | unique |

**Test soundness:** two optima differing by a non-affine `Δ` necessarily have
`slack·Δ ≠ 0` (zero bending on every face ⟺ `Δ` affine). The tie-breakers perturb the
objective within `slack`'s row space, so any non-affine optimal-face direction is
strictly separated — the test cannot silently miss non-uniqueness.

**Conclusion.** Reduced (min-total-bending) DC is unique mod affine in 1D (theorem), 2D,
and 3D. The "fails at a low dimension" conjecture is refuted through 3D. Candidate
theorem, now dimension-agnostic:

> Minimal-total-bending DC decomposition of a PL function on ℝⁿ is unique up to a shared
> affine term — i.e. behaviorally equivalent ReLU networks have identical reduced (P,Q).

**Still not a proof.** Empirical; fixed mesh (off-mesh creases only partially probed via
sparse cases); L1-bending notion. Decisive next steps: (a) a proof via LP duality /
Jordan-type argument, or (b) an *adversarial* search — optimize over f to maximize the
optimal-face dimension, i.e. actively hunt a tie rather than spot-check.

---

## CORRECTION (round 4) — overclaims retracted, result reframed

Two problems, both real.

**1. "Provably non-blind" was false; the adversarial run exposed it.**
The tie-break argument doesn't close: one perturbation `t = sᵀ·slack` gives
`t·Δ = sᵀ(slack·Δ)`, and `slack·Δ ≠ 0` does NOT force `sᵀ(slack·Δ) ≠ 0` for a fixed `s`.
It's detected with probability 1 over random `s` ("generic"), not "provably." Worse, the
adversarial script's *exact* certificate (optimal-face dim via dual support) and the
tie-break now **disagree**: cert reports face_dim 4–9, tie-break reports ~1e-15 (unique),
e.g. on `x²−y²`. The cert is the wrong one — dual support undercounts the *implicit
equalities* at a degenerate LP optimum (constraints active on the whole face but with zero
dual), so it overcounts face dimension. Net: I have **no trustworthy detector** as written.
Correct fix = an L2 selection (min `‖bending‖²` among bending-minimizers, strictly convex
in bending-space, so genuinely unique) plus a direct face-extent LP in bending-space — not
done here.

**2. This is already a literature question, and the universal conjecture is the wrong target.**
Brandenburg, Grillo, Hertlich, *Decomposition Polyhedra of Piecewise Linear Functions*
(arXiv:2410.04907): DC decompositions of a CPWL function form a polyhedron (intersection of
two translated cones); minimal decompositions are its **vertices**; uniqueness is
case-dependent, **proven** for *hyperplane functions* (= one-hidden-layer ReLU nets,
Example 4.18) and *order statistics / median* (Example 4.20). Consequences:
  - Their minimality = **piece count** (Pareto), NOT my total-bending. Different objective
    over the same polyhedron — their uniqueness theorems do not certify my bending results.
  - My `|x|−|y|` test is literally a hyperplane function ⇒ it re-confirmed a theorem. The
    other cases are symmetric `f` on a symmetric mesh ⇒ single-vertex by symmetry. The
    battery was biased toward the proven-unique cases.
  - The paper gives **no** explicit non-unique example and does **not** settle deeper nets,
    so "non-unique in general" is *expected/open*, not established. Do not overcorrect into
    claiming it's proven non-unique.

**Reframed target.** Not "unique for all f" (probably false, and unprovable on a fixed
mesh since off-mesh creases change the vertex set, and my objective ≠ the literature's).
The real question is *characterize the f with a unique minimal decomposition* — which the
decomposition-polyhedron / vertex framework is built to answer. Any counterexample must be
a multi-vertex decomposition polyhedron with the objective tying across vertices; random f
on a fixed mesh cannot find it (measure zero). The 2D/3D "unique" spreads are most likely
correct but uninteresting: they test cases at or near the proven-unique classes.

---

## Case-by-case check vs the proven-unique classes (`scripts/verify_hyperplane_class.py`)

Verified, not asserted — each separable case has an explicit `g − h` with `g, h`
convex on the mesh (`conv·g ≥ 0` checked) and `g − h = f`:

| case | hyperplane fn? | class |
|---|---|---|
| `x²+y²+z²` (control) | yes (`g=f, h=0`) | proven unique (Ex. 4.18) |
| `x²+y²−2z²` | yes (`x²+y²` − `2z²`) | proven unique |
| `x²−y²` | yes (`x²` − `y²`) | proven unique |
| `\|x\|+\|y\|−\|z\|` | yes | proven unique |
| `\|x\|−\|y\|` | yes | proven unique |
| monkey `x³−3xy²` | **no** (non-separable) | outside Ex. 4.18 |
| triple saddle `xyz` | **no** (non-separable) | outside Ex. 4.18 |

**5/7 are hyperplane functions = one-hidden-layer ReLU nets ⇒ proven unique by
Brandenburg-Grillo-Hertlich Ex. 4.18.** The separable quadratics interpolate to sums of
axis-aligned `\|coord − t\|` terms (each a `max{2 affines}`), exactly Ex. 4.18's form. Only
`xyz` and `x³−3xy²` sit outside — and both are highly symmetric (single-vertex by symmetry)
and my detector is unreliable, so even their "unique" verdicts aren't trustworthy.

**Final honest verdict on this whole thread.** The battery contains essentially no clean
evidence for the universal conjecture: ~5/7 re-confirm a theorem, ~2/7 are untrustworthy
symmetric probes. The right object is the decomposition polyhedron of 2410.04907; the right
question is characterizing unique-decomposition `f` (open in general, proven for hyperplane
functions and order statistics); and a fixed-mesh total-bending experiment is the wrong
instrument for it (objective ≠ piece-count; off-mesh creases change the vertex set).

---

## RESOLUTION (round 5) — the conjecture is FALSE; non-uniqueness is generic

A rigorous detector settles it. For each bending coordinate `e`, maximize/minimize
`(slack·Q)_e` over the exact optimal face `{feasible, Σ slack·Q = B*}` (`2E` LPs, no
genericity). Validated against ground truth: reads **unique** (1e-9) on the proven-unique
hyperplane functions `x²−y²`, `|x|−|y|`.

It then finds — and `dc_verify_candidate.py` confirms with explicit two-decomposition
checks — a **genuine non-unique example**: two decompositions `(P,Q)`, both convex, both at
the same minimal total bending `B*=64.715`, differing by a non-affine function (residual
2.88). And it is **generic**: `114/120` random Gaussian `f` are non-unique (max range 8.5);
the unique cases are exactly the structured hyperplane functions.

**So my earlier "unique in 2D/3D" conclusion was wrong** — a blind-detector + biased-case
artifact. The tie-break was blind (the LP solver deterministically returned the same vertex
under the perturbations, exactly the "generic ≠ provable" gap flagged in review), and the
battery was 5/7 hyperplane functions = the proven-unique class.

**Correct statement.** For the total-(curvature)-bending DC objective, minimal
decompositions are **generically non-unique**; uniqueness holds on the hyperplane-function
class (one-hidden-layer ReLU nets). This instantiates, for the curvature objective, the
case-dependence that Brandenburg–Grillo–Hertlich (2410.04907) prove for piece-count — and
supplies an explicit non-unique example, which their paper does not give.

**Scope/credit (honest).** Objective = total bending, not their piece-count (a different
though natural functional). 2D fixed mesh. The *structure* (uniqueness is special, holds
for hyperplane functions) is theirs; the contribution here is a validated detector, an
explicit verified non-unique instance, and the empirical genericity (114/120).
Scripts: `dc_uniqueness_rigorous.py`, `dc_verify_candidate.py`.
