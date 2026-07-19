# Positive-Geometry Probe of the Chamber Spectral Measure

> ## ⛔ FALSIFIED — read this first (correction, supersedes the verdicts below)
>
> The decisive check (`scripts/build_ABP_vertex_check.py`) settles it: the literal
> Arkani-Hamed–Benincasa–Postnikov single-edge cosmological canonical form, on the
> matched line, has **residue sum 0**; the chamber spectral measure `m(z)` has
> **residue sum 1**. They are **not equal**. The cosmological-polytope / cosmohedron
> identification is **false**, falsified on the residue sum — the Parseval obstruction
> (`Σ|v_i(Higgs)|² = 1` vs a constant-numerator simplex form, which decays `1/z³` and
> sums to 0). Follow-ups 1–3 below reproduced `m(z)` only by **multiplying the bare
> canonical form by a hand-inserted numerator `∏(z−μ)`** — that inserts the answer; it
> is not a positive-geometry operation on the polytope.
>
> **The pattern (worth naming):** across three rounds the object never changed — it is
> the spectral measure of `J` at the Higgs site, i.e. the eigenvector–eigenvalue
> identity. Each round was the same fact in a new wrapper (weighted positive geometry →
> moment problem → cosmohedron), and "every assertion passes" was consistency about
> standard linear-algebra identities (eigenvector–eigenvalue identity, spectral moment
> formula, barycentric coordinates), **not evidence** for the geometric claim.
>
> **The deflated, TRUE statement:** the K/P chamber weights are the **Gauss-quadrature
> weights of the spectral measure of the Higgs-site Jacobi operator `J`** (equivalently
> the eigenvector–eigenvalue identity), with a clean moment-curve picture as
> barycentric coordinates of the spectral moment point. That is a legitimate, tidy
> reformulation. It is **not** a cosmological polytope, a cosmohedron, or a derivation
> of `1/N_c` from positive geometry. `1/N_c = 1/3` is the squared Higgs component of one
> eigenvector and stays a spectral quantity.
>
> Everything below is retained as a record of how the claim inflated and was falsified.

**Question.** Is the `J_4` spectral measure the canonical form of a 1D positive
geometry whose boundaries are the three chamber eigenvalues — and does its
boundary structure say anything physical?

**Method.** Exact symbolic computation (`scripts/positive_geometry_probe.py`,
sympy, zero floating point in the verdicts). Build the chamber Jacobi matrix
`J_4`, form its Weyl m-function (resolvent (1,1)-entry) as the candidate
canonical form, and run the standard positive-geometry diagnostics: positivity
(Herglotz), interlacing, triangulation/spurious-pole cancellation, and the
strict ±1-residue test for a *bare* positive geometry.

## Result

| Test | Positive-geometry meaning | Verdict |
|---|---|---|
| Canonical form `m(z) = Σ wᵢ/(z−λᵢ)` | resolvent = rational top-form, simple poles on boundaries | **PASS** |
| Boundaries = eigenvalues `{3/5, (5±√7)/30}` | the mass-spectrum locations are the poles | — |
| All residues `> 0` | Herglotz / honest positive measure (1D positivity) | **PASS** |
| Minor eigenvalues `(3±√3)/10` interlace spectrum | the 1D shadow of total positivity | **PASS** |
| Interior eigenvalue is a spurious pole that cancels | `Ω([λ₃,λ₁]) = Ω([λ₃,λ₂]) + Ω([λ₂,λ₁])`; "locality from boundaries" | **PASS** |
| Residues are `±1` (bare interval canonical form) | amplituhedron-style *unweighted* geometry | **FAIL** |
| Residues `> 0`, `Σ = 1`, atomic in `√7` | *weighted* positive geometry (cosmological branch) | **PASS** |

## The two things the probe pins down

**1. The spectral measure is a *weighted* positive geometry, not a bare one.**
The would-be canonical form `m(z)` passes every positivity/locality test, but its
residues are not `±1`, so it is not the canonical form of a bare interval/polytope
(the amplituhedron kind). It is three boundary points carrying positive weights
summing to 1 — the structure of **Benincasa–Dian weighted cosmological polytopes**.
This sharpens the earlier conclusion: the correct target on the positive-geometry
side is the **cosmological branch (weighted cosmological polytopes / cosmohedra)**,
not the amplituhedron.

**2. The boundary residues are forced to be the framework's atomic numbers.**
The spectral weights come out in closed form, all inside `ℚ(√7)` (the disc=7 field):

```
w₁ = 1/3                    = 1/N_c                 (the Higgs residue)
w₂ = (7 + √7)/21            = (disc + √disc)/(N_c·disc)
w₃ = (7 − √7)/21            = (disc − √disc)/(N_c·disc)
w₂ + w₃ = 2/3 = 2/N_c ,     w₂·w₃ = 2/21 = 2/(N_c·disc)
```

The `w₂, w₃ = (7 ± √7)/21` closed forms are a small new exact fact (the repo had
only `w₁ = 1/3`, `w₂·w₃ = 2/21`). So the *residues of the candidate canonical form
are exactly the atomic vocabulary* {N_c, disc} — the would-be "factorization data"
of the geometry is arithmetic, not generic.

## Why this matters / next step

Positive geometry is a machine for producing dynamics (amplitudes, correlators)
*without an action principle* — which is precisely the unifiedtheory framework's #1
open hole (`ACTION_PRINCIPLE_PROPOSAL.md`). This probe shows the framework's central
spectral object already sits in the *weighted* positive-geometry class, with
boundaries = the mass spectrum and boundary weights = atomic numbers.

The physical payoff is now a sharp, bounded target:

> Build a weighted 0/1-dimensional positive geometry whose three boundary weights
> `{1/N_c, (disc ± √disc)/(N_c·disc)}` are *derived* as canonical forms of
> sub-geometries. If that succeeds, the Higgs residue `r₁ = 1/N_c` acquires a
> positive-geometry **reason** (a boundary-factorization statement) rather than
> being a spectral coincidence.

**Honest scope.** This is a structural match, not a derivation: no cosmohedron is
constructed here, and the positive-geometry literature has built these objects only
for Tr(φ³)/N=4 SYM/NLSM/scalar-FRW toys, none of which is the SM. The result is that
the seam lines up and is arithmetic — a reason to attempt the weighted-geometry
construction, not evidence that it exists.

Reproduce: `python3 scripts/positive_geometry_probe.py`

---

# Follow-up: Constructing the weighted geometry (the weights derived, not read off)

`scripts/construct_weighted_geometry.py` builds a weighted positive geometry whose
boundary residues *are* the three weights, derived from sub-geometry data rather than
extracted from eigenvectors. All exact, all assertions pass.

**Configuration (every number atomic in `{N_c, N_total, disc}`):**

```
vertices (boundaries)   λ_1 = N_c/N_total = 3/5
                        λ_{2,3} = (N_total ± √disc)/(2·N_c·N_total) = (5±√7)/30   ∈ ℚ(√7)
dual points (interlace) μ_{1,2} = (N_c ± √N_c)/(2·N_total)          = (3±√3)/10   ∈ ℚ(√3)
```

The dual points are not free: they are the spectrum of the **sub-system with the N_c
(Higgs) channel deleted** — the deleted-minor eigenvalues. The two quadratic fields are
`ℚ(√N_c)` and `ℚ(√disc)` — the two prime atomic numbers.

**Result — each weight is a canonical-form residue = distance ratio:**

```
w_i = ∏_k (λ_i − μ_k) / ∏_{j≠i} (λ_i − λ_j)   =   Res_{λ_i} Ω,   Ω(z) = ∏(z−μ_k)/∏(z−λ_i)
```

reproduces `{1/N_c, (disc±√disc)/(N_c·disc)}` exactly. The Higgs residue spotlight:

```
w_1 = (λ_1−μ_1)(λ_1−μ_2) / (λ_1−λ_2)(λ_1−λ_3) = (3/50)/(9/50) = 1/3 = 1/N_c
```

So `1/N_c` is now a **geometric quantity** — the residue at the top boundary, fixed by
the configuration of two atomic spectra (full and N_c-reduced) — not an eigenvector
coincidence. The continued-fraction ladder confirms the sub-geometry reading: the form
is the nested CF of the atomic `(a_i, b_i²)` data, and `1/N_c` is the **bare rank-1
atom** (`C₁ = 1/(z−1/N_c)`) before any coupling.

**Still open (next bounded target).** This is a 1D weighted geometry presented by its
boundary+dual data; it is *not yet* exhibited as the canonical form (or a facet) of a
convex **cosmological polytope / cosmohedron**. The N_c-channel deletion behaves like a
**graph edge-contraction** (reduced graph ↔ reduced spectrum), which is exactly how
cosmological-polytope facets work — so the concrete next step is to realize
`{λ_i} ∪ {μ_k}` as vertices of a cosmological polytope for a small graph, with the
deletion = edge contraction, and recover the weights from sub-polytope volumes.

Reproduce: `python3 scripts/construct_weighted_geometry.py`

---

# Follow-up 2: The smallest graph

`scripts/smallest_graph_search.py` settles which graph realizes the weighted
geometry, by matching exact invariants. All assertions pass.

**Pole count (= # connected subgraphs of G):**

| graph | # poles `ψ_G` |
|---|---|
| single vertex | 1 |
| single edge `P₂` | **3** |
| path `P₃` | 6 |
| triangle `C₃` | 7 |

Our object has 3 poles, so the only matching cosmological building block is the
**single edge `P₂`**, whose cosmological polytope is the 2-simplex (triangle) —
its 3 facets ↔ the 3 chamber eigenvalues.

**The decisive invariant — sum of residues:**

```
m(z) = ∏(z−μ)/∏(z−λ)   (numerator degree 2)  :  Σ residues = 1
bare 3-facet simplex 1/∏(z−λ)  (const numer.) :  Σ residues = 0
single-edge ψ shape  (numerator degree 1)     :  Σ residues = 0
```

A bounded cosmological polytope's canonical form is projective (total residue 0).
Our `m(z)` has total residue **1**. The deficit is supplied exactly by the **two
dual points μ** (the leaf-deleted `P₂` spectrum): they raise the numerator to
degree 2 and normalize the form to a probability measure. So the dual points *are*
the weighting that upgrades the bare cosmological simplex into a cosmohedron-style
weighted geometry.

**Verdict.**
- **Operator graph = path `P₃`.** `J_4` is literally the weighted nearest-neighbour
  chain `(1)–(2)–(3)`; the N_c/Higgs-channel deletion is leaf deletion `P₃ → P₂`,
  and `spectrum(P₂) = μ`.
- **Smallest cosmological building block = single edge `P₂`** (2-simplex/triangle),
  3 facets ↔ 3 boundaries.
- It must be the **weighted (cosmohedron)** form, not a bare `ψ_G`: forced by the
  Σ-residue = 1 vs 0 invariant. Facets ∈ `ℚ(√disc)`, weighting via μ ∈ `ℚ(√N_c)`,
  top facet residue = `1/N_c`.

**Still open (now fully bounded).** Exhibit a convex cosmohedron `C` with facets at
`λ` and weighting section at `μ`, so the residues are honest sub-polytope volumes.
The graph is fixed; only the explicit convex body remains.

Reproduce: `python3 scripts/smallest_graph_search.py`

---

# Follow-up 3: The P₂ cosmohedron (explicit convex body)

`scripts/build_P2_cosmohedron.py` builds the convex body and recovers the weights as
honest sub-polytope volumes. All exact, all assertions pass.

**Convex body — the 2-simplex on the moment curve:**

```
T = conv{ P_i },   P_i = (λ_i, λ_i²)      (vertices on the parabola)
P_1 = (3/5, 9/25),  P_2 ≈ (0.2549, 0.0650),  P_3 ≈ (0.0785, 0.0062)
```

A triangle — exactly the shape of the single-edge (P₂) cosmological polytope; its
three facets are dual to the three chamber boundaries λᵢ.

**Weighting point — atomic, located by the dual points:**

```
Q = (m_1, m_2) = ((J)_11, (J²)_11) = (1/N_c, 1/N_c² + 1/N_total²) = (1/3, 34/225)
m_1 = Σλ − Σμ      (the dual points μ pull the mean)
```

**Weights = sub-polytope volumes.** Connecting Q to the vertices triangulates T into
three cells; their volume fractions are exactly the spectral weights:

```
w_i = Area(Q, P_j, P_k) / Area(T) = { 1/N_c, (disc ± √disc)/(N_c·disc) }
Σ w_i = 1   (cells tile T) ;  Q interior ⇒ all weights > 0 ⇒ honest positive geometry
Σ_i [Area(cell_i)/Area(T)] / (z − λ_i)  ==  ∏(z−μ)/∏(z−λ)  = m(z)   ✓
```

**Higgs residue as a volume:** `1/N_c = Area(Q,P₂,P₃)/Area(T)` — the volume fraction of
the cell opposite the top eigenvalue. No longer a spectral coincidence: it is an area
ratio in an atomic convex body.

**Scope (honest).** T is the moment-curve 2-simplex carrying the correct weighted
positive-geometry data (boundaries λ, weighting point from μ, volume-weights), verified
at the level of the weighted canonical form. Its projective identification with the
literal Arkani-Hamed–Benincasa single-edge cosmological polytope (same 2-simplex shape)
is asserted at that level, not via an independent ABP vertex derivation — that
cross-check is the one remaining tidy-up.

Reproduce: `python3 scripts/build_P2_cosmohedron.py`

---

## Full chain (all exact, all assertions pass)

```
chamber spectrum J_4
  → weighted positive geometry        (positive_geometry_probe.py)
  → weights = canonical-form residues (construct_weighted_geometry.py)
  → smallest graph: P₃ chain / P₂ edge (smallest_graph_search.py)
  → P₂ cosmohedron = moment 2-simplex (build_P2_cosmohedron.py)
       Higgs residue 1/N_c = sub-polytope volume
```
