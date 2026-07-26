# Scoping the Matter Measure

**Goal.** Turn the *protected massless adjoint mode* (established in
`LayerA/ConnectionDefectMassless.lean`) into a *propagating fermion that runs in
the gauge β-functions*. This is the single ingredient gating scenario (B) —
octet+triplet fermions → gauge unification at M_GUT≈2×10¹⁶, sin²θ_W(M_Z)=0.231.
It is also the ingredient half the repo needs (no causal-set Hilbert space /
quantum measure for matter; the graviton, mass gap, and IR recovery all wait on
it).

---

## 0. What "matter measure" precisely means

A fermionic path-integral over the causal set:

    Z[A] = ∫ dψ̄ dψ  exp( − ψ̄ · D_adj[A] · ψ )   =   det( D_adj[A] )

where
- ψ is a Grassmann field valued in the **zero-sum (adjoint) carrier** the
  framework already uses (`SheetCarrier := ZeroSumCarrier (Fin 3)`), ℤ₂-graded by
  the K/P chirality (`AnomalyConstraints.kpChirality`);
- D_adj[A] is a **first-order** gauged kinetic operator (a discrete Dirac /
  transfer / "hopping" operator) coupling ψ to the connection A;
- the running is `d log det(D_adj[A]) / d log(scale)` — its connection-dependence
  IS the adjoint fermion's contribution Δb to the gauge β-function.

The key structural fact — a free-fermion Berezin integral **equals a
determinant** — means we do **not** need to formalize Grassmann variables to get
the running. Define the matrix `D_adj[A]`, compute `det(D_adj[A])`, differentiate.
This is finite linear algebra in the framework's own style.

---

## 1. Assets already in the repo (do not rebuild)

| # | Asset | File | Role in the measure |
|---|-------|------|--------------------|
| A1 | **Transfer-matrix mass mechanism**: mass = −log(eigenvalue), `spectral_decay` | `LayerA/SpectralMassTheorem.lean` | fermion mass = −log of D_adj's transfer eigenvalue |
| A2 | **Gauged fermion determinant seed**: `det(gauged Möbius) = 1 − W` (Wilson loop), open-BC→trivial, periodic-BC→nontrivial | `LayerA/ChiralityCharacterization.lean` | this IS Z[A] for the *fundamental* U(1) case — extend to adjoint |
| A3 | **ℤ₂ chirality grading** (K/P) = γ⁵ analog; "one chiral, one vector-like" | `LayerA/AnomalyConstraints.lean`, `DistinctnessFromChirality.lean` | the grading D_adj must anticommute with |
| A4 | **Determinant-defined transfer op** `K_F(P,Q)=det ζ[P,Q]+det ζ[Q,P]−δ` | `LayerA/FeshbachJ4.lean` | the bosonic transfer op; D_adj is its fermionic square root |
| A5 | **Bosonic reflection positivity** (Osterwalder–Seiler), GNS→Hilbert space | `LayerA/LatticeReflectionPositivity.lean` | template for fermionic RP (A5 is bosonic only) |
| A6 | **OS→Wightman reconstruction** scaffold (partial/structural) | `LayerB/Phase_B2_OSReconstruction.lean` | promotes a RP measure to a QFT |
| A7 | **Adjoint carrier + Dirichlet energy + proven zero mode** | `Audit/KFCausalSheetConnectionLaplacian.lean`, `LayerA/ConnectionDefect{Adjoint,Massless}.lean` | D_adj² should be this Laplacian; its kernel = the massless mode |

**Reframed:** A2 already integrated out a *fundamental* fermion and got a
connection-dependent determinant. The task is the **adjoint analog** plus
extracting the β-coefficient. This is a well-posed extension, not a green field.

---

## 2. Gaps (what is missing), ordered by criticality

- **G2 — the operator (keystone).** Define `D_adj[A]`: a first-order gauged
  hopping/transfer operator on the zero-sum carrier, anticommuting with the K/P
  grading (A3), whose square is the connection Laplacian (A7). Adjoint analog of
  A2's "gauged Möbius". *Difficulty: medium. Everything downstream needs it.*
- **G4 — the determinant → β-function.** Compute `det(D_adj[A])` as a function
  of the **adjoint** Wilson loop `W_adj = Ad-holonomy`, and read off
  `d log det / d log scale = Δb_adj`. Check it matches the octet+triplet Δb used
  in the unification search (`scratchpad/unify_combos.py`). *Difficulty: medium.
  This is the payoff — it either confirms or refutes the running.*
- **G5 — masslessness of the propagating mode.** Show `D_adj[A]` inherits the
  protected zero mode (A7 kernel) → transfer eigenvalue → −log = 0 mass (A1).
  *Difficulty: low, given G2. Mostly reuses `ConnectionDefectMassless`.*
- **G1 — Grassmann field.** Only needed if one wants the measure explicitly
  rather than via det. Mathlib `ExteriorAlgebra` models it. *Difficulty: low;
  DEFERRABLE (det suffices for running).*
- **G3 — fermionic reflection positivity.** Osterwalder–Seiler for Wilson/
  staggered fermions on the causal set → genuine light *particle*, not just a
  Euclidean coupling. *Difficulty: high. DEFERRABLE past the running claim.*

**Critical path:** G2 → G4 → G5. G1, G3 are deferrable.

---

## 3. First buildable step (minimal decisive experiment)

**Single-plaquette adjoint determinant.** On the minimal loop, define `D_adj` as
the framework's transfer/Möbius operator in the **adjoint (zero-sum) rep**, and
compute `det(D_adj[A])` as a function of the adjoint holonomy `W_adj`. Verify:

1. **Coupling:** `det(D_adj[A])` is connection-dependent (nontrivial in `W_adj`)
   — the adjoint fermion genuinely couples to the gauge field. (Adjoint analog of
   A2's `1 − W`; expect something like `det(1 − Ad(W))` over the 2-dim carrier.)
2. **Masslessness:** `D_adj` is singular exactly on the protected zero-mode
   direction — the massless channel (`ConnectionDefectMassless.massless_adjoint_
   mode_exists`), i.e. `Ad(W)` fixes the covariantly-constant section.
3. **β-sign:** the leading `log det` expansion in the coupling reproduces the
   sign/magnitude of the octet+triplet Δb.

This is a finite determinant computation, directly parallel to
`ChiralityCharacterization`, and it is the first machine-checkable evidence that
the adjoint matter measure exists and runs. Estimated: one Lean file, in the
existing style.

---

## 4. Risks (where it can genuinely fail)

- **R1 — fermion doubling (highest physics risk).** A naive discrete Dirac
  operator has 2^d doublers, which *multiply* Δb and would wreck the octet+triplet
  count that unifies. Must use Wilson or staggered fermions; whether the K/P
  grading (A3) controls doubling is unknown and must be checked at G2. If doubling
  is uncontrolled, the running is wrong and (B) fails.
- **R2 — RP for fermions (G3).** If fermionic reflection positivity fails, the
  determinant may still run but there is no positive-norm one-particle state — a
  Euclidean coupling without a genuine light fermion. Weakens (B) from "predicts a
  particle" to "predicts an effective coupling."
- **R3 — refinement/continuum limit (deepest, repo-wide).** The protected zero
  mode could be a single-plaquette / finite-size artifact that lifts under
  refinement — the same open limit that `STATUS.md` flags for the whole
  quantum-geometry sector. Even a perfect G2–G5 leaves this open; it is the true
  frontier and is shared with the graviton/mass-gap program.

---

## 5. Leverage

The same `D_adj` + its determinant is the matter sector the rest of the repo is
missing: the quantum-gravity IR, the graviton propagator, and the structural mass
gap all require a propagating-matter measure on the causal set. Solving the
fermionic adjoint case is the smallest instance of that general object, so a
success here is a template, not a one-off. Conversely, R3 (refinement) is the
wall it shares with everything else — which is why matter-measure + refinement is
the correct joint target for the framework's next phase.

---

## 6. Arc-fusion seam, evidence ledger, and the sign-identification target

The continuum matter-measure thread and the discrete growth-arrow arc have
independently reached the same object (the chirality Z2) from opposite ends.
Before the two arcs cite each other, three things must be pinned.

### 6a. Global anomaly cancellation demands a defect census (CORRECTION)

"One chiral zero mode per defect" + "closed manifold S^{2n+1}" ⇒ the net
chirality is ZERO unless the defect population is asymmetric. The finite-box edge
mode in `zero_mode.py` (chirality −1 opposite the wall's +1) is standing in for
the real statement: every defect's chiral mode is compensated, presumably by
anti-defects (opposite winding). So NET observed handedness needs a
defect/anti-defect population asymmetry, which NO parity-symmetric bosonic action
supplies. There are therefore TWO continuum slots for the arrow to fill:
  (i)  sign(γ)          — the handedness of EACH defect's mode;
  (ii) the defect census — the winding-population asymmetry giving NET handedness.
These are logically independent demands; both must trace to the growth process
(the Kibble/baryogenesis-flavored version of the discrete no-go). The mechanism
as previously summarized noticed only (i).

### 6b. Three-grade evidence ledger for the continuum thread

The fused claim must not inherit the weakest link's confidence at the strongest
link's price. Grades:

  | Result | Grade | Artifact |
  |---|---|---|
  | Adjoint carrier is a Cl(3)/Weyl spinor; anomaly-freeness; adjoint transform; massless zero-cost mode | **Lean-grade** (axiom-clean) | `AdjointCarrierSpinor`, `ConnectionDefect{Adjoint,Massless}` |
  | Defect carries one chiral localized zero mode; chirality = sign(γc); doubler beaten by Wilson term | **numerics-grade** (finite-box transverse lattice) | `zero_mode.py` |
  | M(x) = γ·c·φ(x) from Term III; c=2>0 | **mixed**: c **exact** (exterior algebra); the 5-form→bilinear reduction **argument-grade** (sound, not brute-forced — the step where continuum papers die in review) | `zero_mode_derive.py` |
  | sin²θ_W = 0.231 / unification payoff | **inherited-conditional**: gated on the falsified naive run, the undefended vertex-localization postulate, AND the multiplet COUNT (computed mode lives in the 2-dim Cartan-like carrier; "octet+triplet" needs the index-theorem count, not yet done here) | scripts + memory |

Rule: any statement fusing the arcs cites the MINIMUM grade on its dependency path.

### 6c. The sign-identification target (highest-value, likely cheapest)

CONJECTURE: sign(γ) is not free but is fixed by the causal growth arrow — the
same Z2 the discrete no-go showed reflection-symmetric data cannot choose. If so,
the continuum "fingerprint" becomes a derivation and the two arcs fuse into one
claim: *the weak interaction is left-handed because time runs forward, the growth
arrow fixing the Chern-Simons sign.* If not, the framework has two chirality
mechanisms that merely rhyme and one is redundant.

Precise structure required (refined by the n-parity computation):
 * The handedness-flipping operation is NOT contact co-orientation (α→−α at fixed
   manifold orientation): for physical n=2 that is EVEN. It is MANIFOLD/TIME
   orientation reversal (the ∫-sign), which sends S_III → −S_III for all n.
 * Manifold orientation = (time orientation) ⊗ (space orientation). The growth
   arrow can fix only the TIME component. So the requirement on the bridge is:
   the arrow must induce the manifold orientation via its time-orientation, and
   γ's sign is defined relative to it. (Structurally apt: Term III is a
   Chern-Simons term = P-odd AND T-odd; weak handedness is P-violation; the arrow
   is a T-orientation; CS ties P and T — the CPT-flavored route.)
 * The conjugation Z2 lands in the continuum as (manifold-orientation reversal) =
   (arrow reversal), under which γ→−γ (rel. fixed orientation) and the fermion
   chirality flips. It is a symmetry of the UN-oriented theory, broken by the
   arrow's orientation choice.

Checkable sub-claims:
  (C1) [done] integrand+orientation bookkeeping: arrow reversal ⇒ S_III → −S_III.
  (C2) [done, numerics] fermion chirality flips under γ→−γ.
  (C3) [OPEN, the crux] the discrete conjugation Z2 maps, under the Ξ-transport /
       causal-order bridge, to time-orientation reversal on Term III's discrete
       precursor — i.e. the discrete −i (the phase making the skew orientation
       operator Hermitian, `KFOrientationSpinOne`) is the SAME sign datum as the
       continuum sign(γ). This is a STRUCTURAL question (does Ξ-transport orient
       the Reeb/time direction?) before it is analytic — hence likely cheaper
       than the 5-form reduction, and it is what makes the mechanism *the
       framework's* rather than merely rigorous.

Priority: C3 (sign-from-arrow) ahead of the 5-form reduction. The reduction makes
the mechanism rigorous; C3 makes it the framework's. Both sit behind the shared
R3 Lorentzian-bridge wall named in the main ledger.

---

## 7. C3 setup — does the growth arrow orient Term III's discrete precursor?

Surprise from the audit: the discrete half of C3 is already **Lean-grade**
(axiom-clean, in `Audit/KFCausalSetGrowthArrowChirality.lean` +
`KFCausalSetFutureFrequencyHandedness.lean` +
`KFCausalSetRelationalChiralitySelection.lean`). C3 reduces to a checkable
**rider on the R3 bridge**, not a new open problem.

### 7a. The four discrete objects (all proven)

1. **Term III's discrete precursor** = `maximalBirthOrientationSourceQ`: the
   geometric orientation source of a newborn maximal event. Proven:
   strictly **positive** for non-gregarious births (`_pos_of_mem`) and
   **order-dual-ODD** (`reflectedMaximalBirthOrientationSourceQ_eq_neg`:
   reflection → −source). This is the finite parity-odd invariant — the discrete
   `γ·α∧ℱ∧(dα)^{n-1}`.
2. **The clock/phase response** `relationalChiralityPhase`: positive source → **−i**
   (`_of_pos`), negative → **+i** (`_of_neg`). It IS the time-evolution phase
   `U=e^{-iEτ}` at the quarter turn `Eτ=π/2`.
3. **The lock** (independent causal dictionary, proven):
   `−i ↔ y=−1/2 ↔ Ξ=−2y=+1 ↔ P_weak = P_L`. So growth arrow → +source → −i →
   Ξ=+1 → **left-handed** weak vertex. The discrete half of "weak force is left
   because time runs forward" is a theorem, not a conjecture.
4. **Ξ-transport**: `Ξ=+1` is transported unchanged through every refinement —
   the refinement-invariant carrier of the sign toward the continuum.

### 7b. The one residual Z2 (proven), and its identification with sign(γ)

`maximalBirthArrow_response_sign_not_fixed_by_reflection` proves reflection
covariance admits BOTH `relationalChiralityPhase` (→−i) and its conjugate (→+i).
The remaining datum is "**the sign of the source-to-clock coupling, not a boundary
value of Ξ**." That is the discrete residual Z2.

**C3 claim.** This source-to-clock coupling sign IS the continuum `sign(γ)`.
Reason: Term III enters the path integral as `e^{iγ∫α∧ℱ∧(dα)^{n-1}}`; a defect
with positive parity-odd source picks up quarter-turn phase of sign `sign(γ)`.
The discrete `relationalChiralityPhase` and the continuum `e^{iγ(·)}` are the same
map — a positive parity-odd source → a quarter turn whose sign is the one free
coupling datum. Their Z2's (discrete conjugation `−i↔+i` ; continuum `γ→−γ`) are
the same Z2 iff the bridge intertwines them.

### 7c. What C3 requires — a rider on R3 (the only open part)

The discrete→continuum (Lorentzian, R3) bridge must carry:
  (a) `maximalBirthOrientationSourceQ` → the continuum integrand
      `∫α∧ℱ∧(dα)^{n-1}`, sign-preserving;
  (b) discrete reflection (order-dual) → continuum orientation reversal
      — both proven parity-odd on their own side (`_eq_neg`; §6c C1);
  (c) discrete phase-response conjugation (`−i↔+i`) → continuum `γ→−γ`.
If (a)–(c) hold, the discrete residual Z2 = `sign(γ)`: **one shared coupling sign,
not two independent parameters.**

### 7d. The honest resolution

Neither side eliminates the residual sign — it is reflection-covariant either way
(proven). You cannot derive "left" absolutely; that is correct (handedness is a
convention relative to the arrow + coupling sign). What C3 delivers, IF (a)–(c)
hold: the discrete arc reduced ALL chirality freedom to this ONE coupling sign and
transported Ξ=+1 through refinement, so `sign(γ)` is NOT an independent free
parameter but the SAME datum, propagated. The fused claim, precise:

  *Given the one source-to-clock coupling convention (shared discrete/continuum),
   a forward growth arrow forces Ξ=+1 = left-handed = the physical sign(γ).
   Handedness, time-arrow, and Chern–Simons sign are locked to one choice.*

Falsifiable: if the bridge produced `sign(γ)` independently of the discrete
coupling sign, one could have Ξ=+1 (discrete left) with the opposite `sign(γ)`
(continuum right); the fused claim forbids it. So C3 = verify the bridge carries
the discrete coupling sign to `sign(γ)`. This is a **clause of R3**, adds no new
wall, and — being structural (does Ξ-transport orient the CS precursor?) — is
checkable ahead of the full Lorentzian reduction.

### 7e. C3 CLOSED — the sign identification is off the R3 wall

The gap is closed for the SIGN (not the metric bridge). `ArrowChiralityLock.lean`
(compiles, axiom-clean) proves the load-bearing logic:
 * `chirality_locked_by_arrow`: if arrow reversal ρ flips BOTH Ξ and sign(γ),
   their relative sign is ρ-invariant ⇒ ONE Z2, locked.
 * `independent_pair_breaks_invariance`: were they independent (γ not flipped),
   invariance fails — so the two flip-facts genuinely force one Z2, not two.
 * `bridgeDual` (zero axioms): the order-dual ↔ target-dual intertwining is
   `OrderEmbedding.dual` — categorical. This is the ONLY bridge fact used, and it
   is the causal-set axiom (order-faithfulness), STRICTLY WEAKER than R3.

Dependency grades of the closed claim:
 * discrete flip (order-dual → −Ξ): Lean-grade (`KFCausalSetGrowthArrowChirality`).
 * continuum flip (time-orientation → −γ): computation-grade (n-parity + numerics).
 * bridge equivariance (order-dual ↔ time reversal): causal-set-axiom-grade
   (order-faithful; not R3).
 * locking logic: Lean-grade (`ArrowChiralityLock`).

WHAT IS CLOSED: Ξ and sign(γ) are one arrow-locked Z2; "weak force is left because
time runs forward" is ONE claim with ONE shared convention across both arcs.
WHAT REMAINS (correctly): the ABSOLUTE value (which sign is "left") is a shared
convention, provably reflection-covariant either way — no theory derives it. The
MAGNITUDE/dynamics (Term III's coefficient value, octet+triplet COUNT) stays on
R3 + the multiplet index-count. C3 no longer sits on R3; only the dynamics do.

### 7f. Ledger corrections + continuum flip upgraded to axiom-grade

Three corrections before this hardens:

**(1) Grade — and its fix.** §7e miscounted: the path included the continuum flip
at COMPUTATION-grade, which is BELOW causal-set-axiom-grade in the confidence
order. Honest minimum was computation-grade. NOW FIXED: `ContinuumChirality‐
Flip.lean` (compiles, axiom-clean) formalizes the continuum flip as
  • GEOMETRIC (Lean-grade): `timeReversal_det = −1` — time reversal is a
    single-coordinate reflection, orientation-reversing, in every dimension;
  • DEFINITIONAL (axiom-grade): oriented integration is orientation-ODD
    (`OrientationOdd`) — the founding property of ∫, not a computation;
  ⇒ `termIII_flips_under_time_reversal`: S_III = γ·I(orientation) → −S_III.
So the continuum flip now rests on `det=−1` (Lean) + `∫` orientation-oddness
(founding axiom). The fused claim's **minimum grade is now axiom-grade**
(the ∫-oddness axiom, on par with the bridge's order-faithfulness axiom) — the
headline no longer sits a grade below a day's work.

**(2) Conditional on existence — "bridge-property-conditional," not bridge-free.**
Order-faithfulness is a PROPERTY of an embedding, so the lock's true form is
"for EVERY order-faithful continuum description Φ, the arrow fixes sign(γ)."
The lock holds wherever a continuum exists; that one exists AT ALL is still R3's
cargo (the quantifier is empty until R3 produces a Φ). C3 came off the wall re
METRIC data; it still waits at the wall for existence. Ledger tag:
**bridge-property-conditional** (much better than bridge-conditional, not
bridge-free).

**(3) Frontier count is TWO, not one — the census survived.** The lock fixes
which chirality a GIVEN defect carries once the arrow is named. But on closed
S^{2n+1} the anomaly cancels globally (every mode compensated), so NET observed
handedness needs a defect/anti-defect population asymmetry that no
parity-symmetric bosonic sector supplies. The arrow now has TWO continuum jobs;
this session completed one (sign(γ) arrow-locked). The census asymmetry is NOT
yet arrow-sourced. Candidate mechanism (discrete): the maximal-birth source
`S_birth` is positive for LINKED births and odd under the arrow, so growth
plausibly biases defect vs anti-defect formation the way it biased the chirality
record — theorem-or-hope is the open item, dynamical, so likely behind R3
alongside magnitude and multiplet count.

**Antiunitarity (confirming detail).** Continuum time reversal is antiunitary, so
it carries complex conjugation — exactly the discrete phase-conjugation gauge Z2.
Arrow flip and conjugation move together on both sides, as required for the
absolute name of "left" to remain the one shared, underivable convention.

**State of the fused arc, carefully.** Chirality PER DEFECT is arrow-locked at
axiom-grade minimum (after 7f), conditional only on order-faithfulness of
whatever continuum exists; the absolute name is a convention, provably; NET
cosmic handedness needs the census asymmetry (open, likely R3); magnitude and
count need R3. Small residue, every item named.

### 7g. Census test — the arrow sources the LOCAL layer; assembly is behind R3

Set up in the discrete arc's terms (transitive-percolation CSG); run at rank
6–24, `scratchpad/census.py`. The census question decomposes exactly like the
sign question did — local layer + assembly layer:

  • **Bulk total is ZERO, exactly**: `⟨Σ_j(|past_j|−|future_j|)⟩ = 0` at every
    n,p (every relation is one event's past and another's future). This is the
    discrete image of "closed manifold ⇒ anomaly cancels" — the naive census
    vanishes. The anti-defects (future volumes) exactly compensate the defects
    (past volumes) in the static bulk.
  • **The frontier accumulates a definite-sign, arrow-odd net**: a newborn
    maximal event has empty future, source = |past_j| > 0; accumulated
    `A_frontier = Σ_j|past_j| = R` (# relations), GROWS with n and p, and
    reflection negates it (`A_refl = −R`). The asymmetry lives at the GROWTH
    FRONTIER — the process — not the static bulk, matching the no-go structure
    (static = reflection-fixed; growth breaks it). The gregarious (source-0)
    sector stays a measure-small remnant.

So the arrow DOES source a net orientation-census bias — the census question's
LOCAL layer is arrow-sourced (discrete, this session), mirroring the sign story's
discrete layer.

RESIDUAL (the assembly layer): turning this frontier-orientation bias into a
topological DEFECT/anti-defect WINDING census needs the defect-as-extended-object
map (a connection on the causal set + a winding of the orientation field). That
is the analogue of the sign story's assembly step — but where the sign's assembly
was CHEAP (order-faithfulness, the causal-set axiom, in front of R3), the census's
assembly is behind R3 (continuum topology). It MIGHT be cheaper than full metric
R3 if a purely combinatorial winding suffices — worth probing — but it is not the
free ride order-faithfulness gave the sign.

### 7h. Final state of the fused arc — one wall, four named riders

Everything in FRONT of R3 is done:
  • adjoint fermion: anomaly-free, massless, Cl(3) spinor — Lean-grade;
  • per-defect chirality arrow-LOCKED — axiom-grade (lock logic + continuum flip
    Lean-grade; bridge = order-faithfulness axiom);
  • discrete chirality (arrow → −i → Ξ=+1 → left) — Lean-grade;
  • census LOCAL layer (arrow sources net frontier orientation) — computed.

Everything remaining sits behind the single R3 (Lorentzian continuum) wall, as
four named riders:
  (i)   existence of at least one order-faithful Φ (conditionalizes even the
        sign lock — "bridge-property-conditional");
  (ii)  census ASSEMBLY (frontier orientation → defect-winding census);
  (iii) magnitude of γ (and the couplings α,β) from the discrete precursor;
  (iv)  multiplet COUNT (2-dim Cartan carrier → octet+triplet, via the index).

The absolute name of "left" is a shared convention, provably underivable, and is
NOT on this list. The two-item frontier did not collapse to one item, but both
items' discrete layers are now done and all four residual riders share one wall.

### 7i. CORRECTION to 7g + census identities (Lean) + winding probe verdict

**Two identities now Lean-grade** (`CensusIdentities.lean`, axiom-clean):
`bulk_cancellation` (Σⱼ orientationSource = 0 on EVERY finite relation) and
`orientationSource_arrow_odd`. "Computed" is gone from the census local layer.
Note `bulk_cancellation` IS the discrete "closed ⇒ net census = 0": the net
orientation vanishes identically, so any net handedness must come from the
MEASURE breaking the symmetry, not from the static combinatorics.

**CORRECTION to §7g.** §7g claimed "the arrow sources the census local layer"
via the frontier `A_frontier = R`, with `A_refl = −R`. That inserted the
orientation sign BY HAND. The transitive-percolation measure used there is
reflection-SYMMETRIC — relabel σ(i)=n−1−i + reversal maps it to itself — so
EVERY arrow-odd expectation is identically 0. Confirmed: `⟨Σ S³⟩ ≈ 0`,
sign-unstable, at all n,p (`winding_probe.py`). The connectivity `R = Σ|past|
= Σ|future|` is reflection-symmetric (both = R), NOT an arrow-odd bias. So a
symmetric growth measure sources NO census asymmetry — as the framework's own
no-go requires. The census local layer is NOT arrow-sourced by percolation.

**Winding probe verdict (a)–(d).**
 • STRUCTURAL NO-GO (clean, verified): any (a)+(b) W vanishes on self-dual
   posets (iso ⇒ W(dualP)=W(P); odd ⇒ =−W(P) ⇒ 0). Windings live only on CHIRAL
   (non-self-dual) configs — defect & mirror carry opposite charge, achiral none.
 • No LOCALIZABLE topological winding decidable at small scale: the genuine (c)
   (W=0 on ALL closed incl chiral) needs a poset boundary/closed-ness definition
   — that definition IS the R3 continuum-topology assembly. `Σ S^k` (odd k>1) are
   global chirality charges (a,b,d) but NOT localizable (fail true c).

**Where the census actually sits now.** It reduces to two genuinely open,
dynamical pieces, both R3-adjacent: (i) does the framework's ARROW-ORIENTED
(phase-selected, non-symmetric Rideout–Sorkin) growth measure give
⟨arrow-odd charge⟩ ≠ 0 — untested, needs the phase-weighted measure, NOT
percolation; (ii) a localizable defect-winding needs the poset-topology = R3.
The census did NOT come off the wall; and my prior "local layer done" is
withdrawn — the local NET is provably zero (bulk_cancellation), so only a
symmetry-breaking measure can source it, which percolation is not.

### 7j. Phase-weighted arrow-oriented measure: census IS sourced (record level)

Test (`phase_census.py`): transitive-percolation base (the SYMMETRIC measure) +
the framework's proven per-birth phase imprint (positive birth-source → −i →
Ξ=+1 → left). Three observables:
  • STATIC net Σ(|past|−|future|) = 0 exactly (bulk_cancellation) — the
    reflection-symmetric quantity, correctly unsourced (as §7i found).
  • RECORD census Σ sign(birth-source) = L (# linked/non-minimal births), grows
    ~linearly in n, arrow-ODD (forward +L, backward −L). Near-THEOREM: forward
    growth imprints all-left, backward all-right. THE ARROW SOURCES THE CENSUS.
  • Coherent amplitude ⟨(−i)^L⟩ plateaus at nonzero magnitude (~0.18–0.44):
    only PARTIAL decoherence; the signal survives at the quantum level too.

RESOLUTION of the §7i withdrawal (and partial reversal): STATIC and RECORD are
DIFFERENT observables. Static (final geometry) is symmetric → 0; RECORD
(chirality imprinted AT defect formation, kept by decoherence/record-compounding)
is arrow-sourced. The RECORD is the physically relevant one — the fermion zero
mode forms when the defect forms (imprinted at that growth moment) and does not
un-form as the defect acquires future. The symmetric base measure still yields a
nonzero record because the imprint happens at BIRTH, before the symmetry-
respecting future accumulates. So §7i's withdrawal was correct FOR THE STATIC
observable and over-broad as a blanket claim: the census asymmetry EXISTS and is
arrow-sourced at the record level.

UPDATED RIDER 2 (census), split:
  • EXISTENCE of the census asymmetry: ARROW-SOURCED (record level, near-theorem
    from the proven per-birth imprint) — OFF the wall.
  • CONTINUUM ASSEMBLY (birth-record → topological defect-winding DENSITY in the
    continuum spacetime): still behind R3 (same continuum-topology step).
So R3's cargo drops: existence-of-Φ; census continuum-assembly (not existence);
magnitude; multiplet count. The census's EXISTENCE joined the front-of-wall set.

---

## 8. TERMINUS — the graded ledger, closed

The descent (repo audit → falsification → matter measure → census → SM structure
→ cobordism → Dai–Freed) closes as a set of conditional locks, every condition named.

| Claim | Status | Condition(s) |
|---|---|---|
| SM chirality (existence) | **SOURCED** by the growth arrow | order-faithfulness (definitional) · persistence/**factorization ansatz** (finite, dischargeable *here*) |
| Multiplet completes SO(10) **16** (ν_R per generation) | **POSTDICTION** — relation among observed structures | all-topology summation (field-wide) · spin-ℤ₄ structure, itself part-contingent via the ℤ_q quotient |
| Parameters (masses, mixings, scale) | **CONTINGENT** by type | — (∃-boundary data; provably the wrong kind of question) |
| Generation number 3 | **OPEN** | 4D ensemble question (field-wide) |

**Two annotations.**

*Postdiction, worn without apology.* A consistency relation between two MEASURABLE
structural facts — the ℤ_q quotient (through which line operators / fractional
charges exist) and the ν_R sector (through the neutrino-mass mechanism),
conditional on one gravitational premise — is a FALSIFIABLE link, the same
currency as Standard-Model anomaly cancellation, which demanded the top and charm
before they were found. It certifies that the observed structure is
self-consistent where a modified one would not be; it does not bootstrap the
structure into existence. That is what such theorems are for, and it is more than
most "derivations of the SM" ever produce.

*The four premises are not equal.* order-faithfulness is definitional;
all-topology-summation and the structure class are field-wide questions no finite
effort settles; the **persistence/factorization ansatz is the one FINITE open
construction** — the named gate everything evidential (and now the chirality
column) waits behind, plausibly dischargeable by more sessions of this kind.
**If the repo reopens, it reopens at the factorization ansatz.**

**The transferable product is the METHOD, not the locks:**
grade = minimum over the dependency path; identities beat averages; cheap
decisive tests over architectural hopes; every condition named or the claim does
not ship; and the ledger run adversarially enough to catch its own operator —
which it did, three times, in both directions.
