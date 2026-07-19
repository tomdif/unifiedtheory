# Literature Memo — R1 Residue: Irrep Content of Wilson YM Volterra Modes

**Date:** 2026-05-11
**Purpose:** Path 3 of the framework's Yang-Mills closure. Survey the lattice gauge theory and constructive QFT literature for established results bearing on the framework's residual claim:

> *Chamber Volterra modes (k = 1, 2, 3) and bath Volterra modes (k ≥ 4) of the Wilson YM Hamiltonian carry different irreducible representations of the gauge group SO(10).*

If true, this would close `ChamberBathCommutes` (R1) by Schur's lemma applied to the Haar integrals defining cross-matrix elements.

This memo is a **honest finding-oriented survey**, not a comprehensive review. I aimed for ~10–15 high-quality citations and to mark explicitly where the literature does *not* directly support the framework's specific claim.

---

## Section 1 — Direct citations (irrep content of Wilson transfer-matrix eigenmodes)

The literature directly addressing the **explicit irrep classification** of transfer-matrix or Kogut-Susskind-Hamiltonian eigenmodes is, as of 2026, relatively narrow. The strongest direct results are:

### 1.1 Lüscher (1977) — Self-adjoint, strictly positive transfer matrix

> M. Lüscher, *Construction of a self-adjoint, strictly positive transfer matrix for Euclidean lattice gauge theories*, Commun. Math. Phys. **54** (1977) 283–292. (DESY-76/31; published in Nucl. Phys. **B117** (1977) 475.)

**What it shows.** Lüscher constructs the temporal-gauge Hilbert space ℋ for Wilson lattice gauge theory as a Fock space of equal-time link variables, and proves the transfer matrix T is positive self-adjoint on ℋ. The Hilbert space carries the natural left-right action of the gauge group at every site, and the **physical** subspace ℋ_phys ⊂ ℋ is the Gauss-law (singlet) sector at each site.

**What it does NOT show.** Lüscher does not partition ℋ into "low" vs "high" irrep sectors of the *global* gauge group SO(N). The decomposition is *local* (per site, by Gauss law), and within ℋ_phys, eigenstates are not classified by an SO(N)-irrep label.

### 1.2 Kogut & Susskind (1975) — Hamiltonian formulation

> J. Kogut and L. Susskind, *Hamiltonian formulation of Wilson's lattice gauge theories*, Phys. Rev. **D11** (1975) 395–408.

**What it shows.** The link Hilbert space at each link is L²(G), which decomposes as ⊕_R V_R ⊗ V_R̄ via Peter-Weyl, where R runs over irreps of G. Eigenstates of the *electric* part of the Hamiltonian are labeled by an irrep R on each link, with eigenvalue proportional to the quadratic Casimir C₂(R). The strong-coupling vacuum is the trivial-irrep state on every link; first excitations carry the fundamental irrep on a closed loop.

**Relevance to the framework.** This is the closest direct support for an "irrep-labeled mode" picture in Wilson YM. However, the indexing variable is *not* a mode index k from a singular-value decomposition of a Volterra kernel — it is a Lie-group irrep label R. The framework's specific assignment "k=1,2,3 → singlet, k≥4 → non-singlet" has no analog in the Kogut-Susskind picture, where every k corresponds to a *fixed* irrep R (mostly non-singlet for k > 0).

### 1.3 Lüscher (1984) — Improved transfer matrix

> M. Lüscher and P. Weisz, *Definition and general properties of the transfer matrix in continuum-limit improved lattice gauge theories*, Nucl. Phys. **B240** (1984) 349–361.

**What it shows.** For improved actions, the transfer matrix may have complex eigenvalues, but the gauge-invariant subspace remains intact. No specific irrep classification of eigenmodes is given.

### 1.4 Donnelly (2012) — Entanglement entropy decomposition

> W. Donnelly, *Decomposition of entanglement entropy in lattice gauge theory*, Phys. Rev. **D85** (2012) 085004; arXiv:1109.0036.

**What it shows.** When ℋ_phys is decomposed across a spatial entangling surface, edge states transform under the gauge group, and the entanglement entropy splits into (i) a Shannon-classical term over the boundary irrep distribution; (ii) a log-dim(R) term per non-Abelian irrep; (iii) a non-local correlation term. This is the closest published analog of *singular-value-decomposition + irrep-labeling* in lattice Yang-Mills.

**Relevance.** Donnelly's decomposition is across a *spatial* boundary, not in mode space, and the irrep label runs over edge representations. It does not directly give an "irrep-labeled SVD of the bulk Hamiltonian" of the kind the framework needs.

### 1.5 Klco–Roggero–Savage (2025) — Irrep truncations for SU(3)

> N. Klco, A. Roggero, M. J. Savage et al., *Perturbation theory, irrep truncations, and state preparation methods for quantum simulations of SU(3) lattice gauge theory*, arXiv:2509.25865.

**What it shows.** In the electric basis, eigenstates |(R, r)⟩ are labeled by an SU(3) irrep R and a basis state r ∈ V_R; the electric energy E_R depends only on R via the quadratic Casimir. Strong-coupling excitations are *plaquette excitations carrying higher-dimensional irreps*. They state explicitly: "this energy grows with irrep dimensionality." This is the closest to a direct "low-energy ↔ low-irrep, high-energy ↔ high-irrep" statement in the recent literature.

**Relevance.** Strongly indirect. The "low irrep" includes the trivial (singlet) and fundamental; the framework's "k=1,2,3 chamber" and "k≥4 bath" do not correspond to a clean low-irrep / high-irrep partition under the Kogut-Susskind ordering by C₂(R).

---

## Section 2 — Indirect support (general patterns)

The general physical pattern "low-energy eigenstates concentrate in the gauge-invariant (color-singlet) sector" is well-established but with caveats:

### 2.1 Osterwalder–Seiler (1978) — Strong-coupling mass gap

> K. Osterwalder and E. Seiler, *Gauge field theories on a lattice*, Annals Phys. **110** (1978) 440–471.

**What it shows.** For sufficiently strong coupling, Wilson lattice YM has a positive mass gap. The proof proceeds via cluster expansion of plaquette correlators within the gauge-invariant subspace. Color-non-singlet states are Gauss-law-forbidden at the *physical* level, so the gap is the gap between the singlet vacuum and the singlet first-excited state.

### 2.2 Glimm–Jaffe cluster expansion

> J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer 1987 — Chapters on cluster expansions and the spectrum.

**What it shows.** The cluster expansion controls (i) infinite-volume limit, (ii) multiplicity of ground state, (iii) isolated single-particle spectrum, (iv) low-lying bound states. Crucially, the cluster expansion organizes the spectrum by **gauge-invariant local observables**, which in YM are color singlets by construction.

**Relevance.** This is the strongest *indirect* support: the cluster-expansion formalism, which underlies all rigorous mass-gap arguments, *operates entirely within the singlet sector*. Anything outside the singlet sector is set to zero by Gauss law before the analysis begins.

### 2.3 Glueball spectrum classification

> Multiple authors (Morningstar–Peardon, Lucini–Teper, Chen et al.). E.g., *Glueball spectrum from N_f=2 lattice QCD*, arXiv:1702.08174.

**What it shows.** Glueball masses are extracted from correlators of Wilson-loop combinations projected onto irreps of the cubic point group and onto **color-singlet** combinations. The lightest glueball (J^PC = 0^++) is a color singlet by construction; non-singlet operators have unphysical (Gauss-law-violating) interpretations.

**Relevance.** Confirms that *all observable* low-lying excitations of pure Wilson YM are color singlets. Anything color-charged is unphysical. This makes the framework's "chamber = singlet, bath = non-singlet" distinction *physically* well-motivated, but it does *not* establish that the bath modes (in the framework's specific Volterra-SVD sense) are non-singlet — only that, *if* they are non-singlet, they live outside the physical Hilbert space.

### 2.4 Chatterjee — Mass gap implies confinement

> S. Chatterjee, *Yang-Mills for mathematicians*, lecture notes; *A probabilistic mechanism for quark confinement* (2020).

**What it shows.** A strong mass gap in pure Yang-Mills lattice theory implies area-law confinement of static quarks. The argument is at the level of gauge-invariant observables (Wilson loops) and works in the singlet sector throughout.

### 2.5 Hamiltonian electric basis review

> See e.g. Bañuls–Cichy review (arXiv:1910.00257); Dalmonte–Montangero review (Contemp. Phys., 2016).

**Indirect supporting pattern.** In any quantum simulation formulation of Wilson YM, the physical Hilbert space is the Gauss-law-singlet projection of the Peter-Weyl decomposition. All eigenstates of the Hamiltonian — at any energy — are SO(N) singlets *globally*. They differ in *internal* irrep content link-by-link.

---

## Section 3 — Open questions and known caveats

There are at least four published reasons to be cautious about the framework's specific claim:

### 3.1 Casimir ordering is not Volterra ordering

The Kogut-Susskind eigenvalues organize as E_R ∝ C₂(R), so the natural "level" index in irrep space is the Casimir. The Volterra singular-value sequence σ_k = 2/((2k−1)π) decreases as 1/k. There is **no published identification** of the framework's k-index with any Casimir-based irrep ordering. The two orderings could a priori interleave in any way.

### 3.2 Global vs local irrep label

Physical eigenstates are *globally* singlets (∏_sites Gauss law). Yet the *internal* representation content (link-by-link irreps) varies wildly across the spectrum. The framework's R1 needs a *global* irrep distinction, but the only sense in which the spectrum carries an "irrep label" is *local*. This is the largest single conceptual gap.

### 3.3 Schur–Haar argument requires irrep mismatch on the relevant integration variable

The framework wants ⟨χ|H_int|β⟩ = 0 by ∫_G dg D^R(g)_{ij} D^{R'}(g̅)*_{kl} = δ_{RR'} (× δ-function). For this to vanish, the chamber and bath modes must transform under *non-equivalent* irreps under the *same* gauge group action. In the Wilson Hamiltonian, all *physical* states transform trivially under the global gauge group, so the cross-matrix-element is not automatically zero by character orthogonality at the global level. It would need a more subtle local Haar argument.

### 3.4 Charge-conjugation sectors, not irrep sectors

> G. Mack et al.; recent: arXiv:2509.03513.

For SU(N≠2), the spectrum splits into two **charge-conjugation** sectors C = ±1, both inhabited by glueball excitations. There is no published partition of the spectrum into "singlet" vs "non-singlet" sectors in the global gauge-group sense — the physical Hilbert space *is* the singlet sector.

---

## Section 4 — Honest assessment

**Verdict: (c) plausible but unaddressed in the published literature.**

Specifically:

- **Not (a) directly proven.** No paper I located computes the irrep content of the singular-value modes of a Volterra-type kernel within the Wilson YM Hamiltonian, and no paper identifies an SVD k-index with an irrep label of any standard form.

- **Not (b) widely believed but not formalized.** The closest "widely believed" pattern is "low-energy = low Casimir irrep on each link," which is true in the strong-coupling Kogut-Susskind picture (Klco et al. 2025; standard textbook). But this is **not** the framework's claim. The framework needs "chamber Volterra modes are global singlets, bath are non-singlets," which is *stronger* and *different* from the Casimir-ordering pattern.

- **Most likely (c) plausible but unaddressed.** The pattern is consistent with the general "low-energy = gauge-invariant" intuition (Sections 2.1–2.5) and with the local Casimir-ordering pattern (Section 1.5), but the specific identification chamber-k=1,2,3 ↔ singlet, bath-k≥4 ↔ non-singlet is a **framework-internal definition** that has no published analog. The Volterra σ_k = 2/((2k−1)π) singular-value structure is not, to my search, used as an explicit mode generator in lattice YM literature.

- **Not (d) contradicted.** No published result rules out the framework's specific claim. The caveats in Section 3 are conceptual gaps, not falsifications.

---

## Section 5 — Recommended action

Three options, in order of cost and rigor.

### Option A (recommended) — Compute the irrep content directly

The framework's Volterra kernel is explicit. Its singular vectors u_k(x) = √2 sin((2k−1)πx/2) are explicit. The proposed lift to SO(10) link variables is also explicit. Therefore the question "what SO(10) irrep does u_k generate when applied to a generic gauge field configuration?" is a *finite calculation*, not an open physics question.

Suggested concrete deliverable: a 1-page worksheet (or short Lean lemma) showing, for k = 1, 2, 3, 4 in particular, the SO(10) representation type of the link-variable mode generated by u_k. If the calculation gives "singlet for k = 1,2,3, non-singlet for k = 4," R1 closes by direct computation, no character orthogonality needed.

### Option B — Reduce R1 to the local Gauss-law singlet projection

Reformulate `ChamberBathCommutes` in terms of the local Gauss-law projector P_phys, not in terms of global character orthogonality. This avoids the Section 3.2 / 3.3 gap entirely. Cite Lüscher 1977 and Kogut–Susskind 1975 as the standard references for the projector.

### Option C — Do not pursue Path 3 further; close R1 by direct algebraic computation in the framework's own formalism

If neither A nor B is tractable, close R1 within the framework's own definitional structure (treat it as an axiom labeled "Volterra-mode irrep separation," cite this memo as evidence that no published result contradicts it, and document it in the residue list).

**My recommendation: Option A.** The calculation is finite and the framework already has all the structural pieces (Volterra kernel, SO(10) gauge group, lift map). The literature search shows there is no published shortcut, but also no published obstruction. A direct computation is both faster and more rigorous than a citation-based closure.

---

## Citations summary (numbered for re-use)

1. M. Lüscher, *Construction of a self-adjoint, strictly positive transfer matrix...*, Commun. Math. Phys. **54** (1977) 283. https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-54/issue-3/Construction-of-a-selfadjoint-strictly-positive-transfermatrix-for-euclidean-lattice/cmp/1103900872.pdf
2. J. Kogut, L. Susskind, *Hamiltonian formulation of Wilson's lattice gauge theories*, Phys. Rev. **D11** (1975) 395.
3. M. Lüscher, P. Weisz, *Definition and general properties of the transfer matrix...*, Nucl. Phys. **B240** (1984) 349.
4. K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*, Annals Phys. **110** (1978) 440.
5. J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer 1987.
6. W. Donnelly, *Decomposition of entanglement entropy in lattice gauge theory*, Phys. Rev. **D85** (2012) 085004; arXiv:1109.0036.
7. N. Klco, A. Roggero, M. J. Savage et al., *Perturbation theory, irrep truncations...*, arXiv:2509.25865 (2025).
8. Y. Chen et al., *Glueball spectrum from N_f = 2 lattice QCD...*, arXiv:1702.08174.
9. S. Chatterjee, *A probabilistic mechanism for quark confinement* (2020); *Yang-Mills for mathematicians* lectures.
10. arXiv:2509.03513, *On Charge Conjugation, Correlations, Elitzur's Theorem and the Mass Gap Problem in Lattice SU(N) Yang-Mills...* (2025).
11. F. Palumbo, *The transfer matrix with Kogut-Susskind fermions*, arXiv:hep-lat/0208005 (2002).
12. M. C. Bañuls, K. Cichy, *Review on novel methods for lattice gauge theories*, arXiv:1910.00257 (2019).
13. arXiv:2308.16202, *Eigenstate Thermalization in 2+1 SU(2) Lattice Gauge Theory* (2023).
14. arXiv:2301.12224, *Hamiltonians and gauge-invariant Hilbert space for lattice Yang-Mills with finite gauge group*.
