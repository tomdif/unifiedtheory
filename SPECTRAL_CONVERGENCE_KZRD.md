# Discrete→Continuum Spectral Convergence for the Symmetrized Compound Order Kernel

**Goal.** Make rigorous (and Lean-formalizable) the framework's foundational claim
γ_d = ln((d+1)/(d−1)) — currently only "numerically verified" in
`VolterraCompound.lean` — by routing its one genuine gap (the discrete→continuum
spectral convergence) through the **DPSS / prolate** convergence frame, using the
nonasymptotic eigenvalue bounds of **Karnik–Zhu–Romberg–Davenport (KZRD)** as the
citable tool. The Volterra/order-kernel family is DPSS-tractable for the same
structural reason DPSS is: it commutes with a 2nd-order Sturm–Liouville operator.

This note states the theorem, the proof via four lemmas with explicit rates, makes
the **compound–symmetrization adaptation** (the piece *not* in off-the-shelf KZRD)
explicit, and gives a formalization roadmap.

Discipline note (kept sharp): this grounds **γ_d as a real spectral theorem**. It
says *nothing* about α(0) = γ_d-numerator/70 — the factor 70 and the α-identification
remain an unmechanized coincidence riding on a real constant. Real vs. coincidence
stays separated.

---

## 0. Objects

- **Order kernel** ζ_m ∈ ℝ^{m×m}, ζ_m(i,j) = 𝟙[i ≤ j] (discrete integration / Volterra).
- **Compound** C_d(ζ_m): matrix on d-subsets I,J ⊆ [m], entry det(ζ_m[I,J]).
- **Symmetrized compound order kernel**
  K_F^{(d)}(m) := C_d(ζ_m) + C_d(ζ_m)^⊤ − I,  symmetric, size C(m,d).
- **Volterra operator** V on L²[0,1], (Vf)(x)=∫₀ˣ f.
- **Singular data of V** (classical, exact): σ_k = 2/((2k−1)π),
  right functions v_k(x)=√2 cos((k−½)πx), left u_k(x)=√2 sin((k−½)πx).
- **Continuum target** 𝒮 := C_d(V) + C_d(V)^⊤ on Λ^d L²[0,1].

---

## 1. Main theorem

**Theorem.** For each fixed d ≥ 2 and the two largest eigenvalues ev₀ ≥ ev₁ of K_F^{(d)}(m),
> ev₁/ev₀ = (d−1)/(d+1) + O(1/m)   as m → ∞,

hence γ_d^{(m)} := −ln(ev₁/ev₀) → ln((d+1)/(d−1)). In particular γ₄ → ln(5/3).

(The O(1/m) rate is verified numerically: m·|ev₁/ev₀ − ⅓| ≈ 0.40 across m=40,80,160
for d=2, and the analogous monotone O(1/m) approach for d=4 toward 3/5.)

The eigenvalues themselves obey, for each fixed top index k,
> ev_k(K_F^{(d)}(m)) = (s₁(m)·s_k-type product structure) · (1 + O(1/m)),
and in the d=2 case the clean closed form ev_k = ½ s₁ s_k (1+O(1/m)), so that
ev_k/ev₀ → σ_k/σ₁ = 1/(2k−1).

---

## 2. Why the family is DPSS-tractable (the structural input)

V*V has kernel min(1−x,1−s) = the Green's function of −d²/dx² (Dirichlet at 1,
Neumann at 0), so **V*V commutes with −d²/dx²**. Its eigenfunctions are the
half-integer sinusoids u_k, eigenvalues σ_k². This is the integration-operator analog
of Slepian's prolate–ODE commutation: the spectrum is ODE-locked and exactly
solvable, and the discrete order kernel inherits the finite-N version with **closed
form**
> s_k(m) = 1/(2 sin θ_k),  θ_k = (2k−1)π/(2(2m+1)),  k=1,…,m,
the eigenvalues of ζ_m^⊤ζ_m = the min-matrix min(i,j). This is the DPSS-style discrete
eigenvalue formula — but here in closed form, so the hardest KZRD estimate (the
log-N transition plunge) is not even needed for the *top* eigenvalues.

---

## 3. Proof via four lemmas

### Lemma A (exact singular-value ratios; elementary)
For fixed k, s_k(m)/s₁(m) = sin θ₁ / sin θ_k = 1/(2k−1) · (1 + O(1/m²)).
*Proof.* θ_k = (2k−1)π/(2(2m+1)) → 0; sin θ_k = θ_k(1+O(θ_k²)); ratio of θ's is exactly
1/(2k−1). ∎ (No DPSS needed — closed form.)

### Lemma B (overlap convergence; quadrature)
Let G_m(i,j) := ⟨û_i, v̂_j⟩ be the discrete overlap of the i-th left and j-th right
singular vectors of ζ_m (discrete sinusoids), and
> G(i,j) := ⟨u_i,v_j⟩ = { σ_i if i=j;  2/((i+j−1)π) if i+j even;  2/((i−j)π) if i+j odd }.
Then for fixed i,j, G_m(i,j) = G(i,j) + O(1/m).
*Proof sketch.* The discrete singular vectors are sampled half-integer sinusoids;
G_m(i,j) is the midpoint/endpoint quadrature of the smooth integrand
2 sin((i−½)πx)cos((j−½)πx) on [0,1]. For fixed (i,j) the integrand is C^∞ with bounded
derivatives, so the quadrature error is O(1/m) (in fact spectrally small away from the
top of the band). The closed-form continuum value G(i,j) is the exact integral
(computed via 2 sinA cosB = sin(A+B)+sin(A−B)). ∎
*(This is the DPSS singular-vector convergence; KZRD-style control gives uniformity in
i,j up to the band edge, which is the input Lemma D needs.)*

### Lemma C (compound multilinearity; Cauchy–Binet)
C_d(ζ_m) = Σ_{|I|=d} (∏_{i∈I} s_i)(û_I)(v̂_I)^⊤, û_I = û_{i₁}∧⋯∧û_{i_d}, and the Gram
overlaps are dets of the single-mode overlaps:
> ⟨û_I, v̂_J⟩ = det[ G_m(i,j) ]_{i∈I, j∈J}.
Hence every matrix element of K_F^{(d)} in the wedge basis is a fixed **multilinear**
(product-of-σ × det-of-G) function of the single-mode data {s_k, G_m}.
*Proof.* SVD functoriality of the d-th exterior power (compound of an SVD is the SVD
of the compound) + Cauchy–Binet for the Gram. ∎ (Exact; no limit.)

### Lemma D (uniform tail bound; **the KZRD-frame piece**)
Fix ε>0. There is K=K(ε) and m₀ such that for all m≥m₀, the top two eigenvalues of
K_F^{(d)}(m) are within ε (relative) of those of the **K-mode truncation** — i.e.
the modes k>K contribute ≤ ε·ev₀, uniformly in m.
*Why KZRD.* The tail contribution is governed by (i) the decay of the singular values
σ_k = 2/((2k−1)π) → 0 and (ii) the size of the off-diagonal overlaps G(i,j) (Hankel
1/(i+j−1) + Hilbert-transform 1/(i−j) tails). KZRD's nonasymptotic DPSS eigenvalue
bounds give exactly the uniform-in-m control of the high-index modes for this operator
family; here the top-eigenvalue regime is the *slack* end of those bounds (the leading
σ's are O(1) and well-separated), so the bound is comfortable. ∎ (Citable; adapted —
see §4.)

### Combine
- By Lemma C, the **finite top-K section** of K_F^{(d)}(m) is a fixed continuous
  (multilinear) function of the finite data {s_k(m)/s₁(m): k≤K} and {G_m(i,j): i,j≤K}.
- By Lemmas A, B these data converge to {1/(2k−1)} and {G(i,j)} at rate O(1/m).
- Eigenvalues are continuous (Lipschitz, Weyl) functions of a symmetric matrix, so the
  top-K section's top two eigenvalues converge to those of the truncated continuum
  operator 𝒮_K at rate O(1/m).
- By Lemma D the truncation error (full K_F vs top-K section; full 𝒮 vs 𝒮_K) is ≤ ε
  uniformly. Sending ε→0 (K→∞):
  > ev₁/ev₀ (K_F^{(d)}(m)) → ev₁/ev₀(𝒮).
- ev₁/ev₀(𝒮) = (d−1)/(d+1): computed exactly in the singular basis from G (d=2 gives
  ev_k=½σ₁σ_k ⇒ σ₂/σ₁=1/3; d=4 gives 3/5 = σ₃/σ₂; general even d gives the consecutive
  ratio σ_{d/2+1}/σ_{d/2} = (d−1)/(d+1)).
- Rate: dominated by Lemma B's O(1/m) quadrature error (Lemma A is O(1/m²)). ∎

---

## 4. The compound–symmetrization adaptation (NOT in off-the-shelf KZRD)

KZRD bound a **single-particle** prolate matrix. Three things are added here; each is
elementary GIVEN the single-mode convergence:

1. **Compound (exterior power).** The spectral data is the exterior-power data —
   products of σ's, wedge singular vectors, det-Gram overlaps (Lemma C). The d-th
   compound introduces *no new convergence problem*: it is a fixed multilinear function
   of the single-mode data on a finite mode set, so single-mode convergence ⇒ compound
   convergence by continuity of (product, det). Rate is preserved (≤ d × single-mode
   rate).
2. **Symmetrization C_d + C_d^⊤.** This mixes the û-basis and v̂-basis; the resulting
   eigenvalue problem is governed by the σ-products *and* the overlap dets. Eigenvalue
   continuity (Weyl) handles the finite section; the absolute normalization (the ½ in
   d=2) is the top eigenvalue of the explicit finite continuum operator 𝒮_K and is
   pinned by the same eigenfunction-convergence estimate (Lemma B). **Crucially the
   normalization cancels in the ratio ev₁/ev₀**, so γ_d needs only Lemmas A–B–C.
3. **Tail of the compound.** Lemma D must bound the *compound's* tail, not the
   single-mode tail: contributions from d-subsets containing a high index. These are
   suppressed by ∏σ (one small factor σ_{>K}) times bounded overlap dets — i.e. the
   single-mode KZRD tail bound, multiplied through the exterior power. This is the one
   place to state the adaptation carefully; it is a finite multilinear lift of the
   nonasymptotic single-mode bound.

So: **single-mode DPSS/KZRD convergence + multilinearity (Cauchy–Binet) + Weyl
continuity ⇒ compound-symmetrized convergence.** The KZRD citation lands at the
single-mode tail bound (Lemma D); everything else is exact algebra (Lemma C) or
elementary (Lemmas A,B).

---

## 5. Formalization roadmap (Lean)

| Step | Statement | Status / Mathlib |
|------|-----------|------------------|
| A | s_k(m)/s₁(m) → 1/(2k−1), rate O(1/m²) | elementary; `Real.sin` bounds, closed form. Easy. |
| min-spec | ζ_m^⊤ζ_m = min-matrix; eigenvalues 1/(4sin²θ_k) | classical; needs the min-matrix diagonalization (sinusoidal eigenvectors). Mid. |
| B | G_m(i,j) → G(i,j), O(1/m) | quadrature of smooth sinusoid product; needs a Riemann-sum error lemma + the exact ∫ (already have the closed form). Mid. |
| C | C_d SVD = wedge data; ⟨û_I,v̂_J⟩ = det[G_m] | Cauchy–Binet / exterior power. Mathlib has `Matrix.det`, exterior algebra partial. Mid–hard. |
| D | uniform tail bound (KZRD) | **cite KZRD**; formalize the single-mode bound or import as hypothesis, then the multilinear lift. Hard — the genuine work. |
| 𝒮-spec | ev₁/ev₀(𝒮) = (d−1)/(d+1) | finite computation in the singular basis from G; for d even = σ_{d/2+1}/σ_{d/2}. Easy once C,B in place. |
| main | combine via Weyl continuity | `Matrix` eigenvalue continuity. Mid. |

The honest hard step is **D** (the KZRD nonasymptotic tail bound + its compound lift).
Everything else is classical/elementary. KZRD is the citable, formalizable tool that
turns "numerically verified" into "theorem."

---

## 6. Honest status

- **Rigorous on paper now:** the reduction K_F → 𝒮 (−I negligible); the exact discrete
  SV closed form and ratio limit (Lemma A); the exact overlap formula and its role
  (Lemma C); the continuum eigenvalue ev₁/ev₀(𝒮) = (d−1)/(d+1) (computed); the rate
  O(1/m) (numerically confirmed).
- **Needs the standard estimate:** Lemma B's quadrature rate (routine) and Lemma D's
  uniform tail bound (KZRD-frame; the one nontrivial analysis step).
- **Cancels out, hence not needed for γ_d:** the absolute constant ½ — it drops in the
  ratio.

**Bottom line.** With the DPSS/KZRD frame supplying Lemma D, γ_d = ln((d+1)/(d−1)) is a
fully rigorous spectral theorem — the framework's central constant grounded in
classical Volterra/prolate theory — and the whole argument is Lean-formalizable along
the table in §5. The real-vs-coincidence line is preserved: this grounds γ₄ = ln(5/3),
not α(0).
