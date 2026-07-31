# Definitions and vocabulary (the arc's technical glossary)

**Causet / level n.**  Isomorphism class of an n-element finite partial
order.  Counts per level: 1, 2, 5, 16, 63, 318, 2045, 16999 (A000112).

**Growth tree.**  Nodes = causets; links C → C′ when C′ = C plus one new
maximal element born above a downset D of C.  *Multiplicity* μ(C→C′) =
number of distinct downsets of C realizing the link.  *Parents* of C′ =
causets obtained by deleting one maximal element.  *Descendants /
future cone* of C = causets reachable from C via links ⇔ causets
containing C as a downset.

**Precursor.**  The past of the new element = the downset D it is born
above.  *Gap locality* (verified): the BD action gap of a birth depends
only on the isomorphism class of its precursor.

**Action units.**  S/σ = N − Σ_{pairs} W(k), k = number of elements
strictly between; 4D weights W = (1, −9, 16, −8), 2D weights
W₂ = (2, −4, 2).  All gaps are integers; all 2D gaps are odd (parity
theorem: the 2D weights are even).

**The ansatz.**  Transition amplitude a(C→C′) = ρ·e^{igφ}, ρ ≥ 0, g the
action gap, φ = σ/ℏ; Markov sum rule Σ_children a = 1 per supported
causet.

**Covariance (amplitude-level).**  The product of amplitudes along any
labeled growth path depends only on the endpoint class.  Equivalent to
the coboundary form a = [Ã(C′)/Ã(C)]e^{igφ} and hence to the **wave
equation**  Σ_{C′} μ(C→C′) Ã(C′) e^{igφ} = Ã(C),  Ã ≥ 0, Ã(root) = 1.

**Support.**  {C : Ã(C) > 0} — the causets the dynamics can actually
form.  Covariance forces the support to be **downward-closed** (every
parent of a supported causet is supported), since every parent lies on
some labeled path.

**Witness.**  A particular LP solution of the wave system.  **Canonical
member** = the witness maximizing Σ Ã over deep levels (an LP vertex;
one arbitrary-but-reproducible representative).

**Forced death.**  A causet with max Ã = 0 over the family (verified by
LP, or by pull-up test in nonlinear settings).  Removals propagate
through future cones (downward-closure).

**Reach-back cascade.**  A death at level n+1 removes a term from
level-n equations and can force earlier deaths.  The only mechanism by
which depth constrains the past (equations couple adjacent levels
only).  Observed: never fires under manifold confinement (n ≤ 8).

**Freedom / dimension.**  Affine dimension of the solution set of the
wave system (variables minus rank).  **Consumed dimension** of a
selector = unrestricted dimension minus the selector-constrained
dimension at the same depth.

**Confined family.**  The wave family restricted to causets of order
dimension ≤ 2 (2-orders = intersections of two linear orders = the 2D
manifoldlike-compatible class; smallest dim-3 posets are the 3+3 crowns
at n = 6).  Order dimension is monotone under induced subposets, so the
class is automatically closed under both downsets and sub-sampling.

**Sub-sampling kernel (Bombelli coarse-graining).**
T_{n,N}(c, C) = (#n-element subsets of C inducing c) / C(N,n) —
row-stochastic.  **One-step self-similarity** = the linear constraint
Ψ_n = T_{n,N} Ψ_N for a single (n, N) pair, where Ψ(C) =
ext(C)·Ã(C)·e^{iS(C)φ} and ext(C) = number of labeled growth paths
(natural labelings).  Kernels compose exactly (T₅₇ = T₅₆T₆₇), so
demanding several steps at once is the (infeasible at this depth)
semigroup fixed point; one-step exactness is the finite-n proxy for an
asymptotic RG property.

**Ordering fraction.**  r(C) = #relations / C(n,2); 2D continuum
benchmark: r → 1/2 (random 2-orders); the n = 7 classical ensemble mean
is 0.533 (finite-size).  ψ-weighted mean r uses weights ψ = ext·Ã ≥ 0
(linear in Ã — LP-rangeable); ψ²-weighted uses |Ψ|² (a pre-decoherence
proxy, not the physical measure).

**Pinned range.**  The interval of achievable weighted mean r over a
(positivity-exact) family — computed by LP + τ-bisection.  "Rigid" =
narrow pinned range; "steerable" = wide.

**Stationarity.**  Amplitudes depending only on the precursor class
(the rule "doesn't know what time it is") — dead with covariance (by
reduction to Bell causality → factoring) and without it (0/60 phases,
certificate at n ≤ 2).  Hence **the couplings must age**.

**The μ = 2 kill.**  The recurring mechanism: the two automorphic
downsets of the 2-antichain contribute coefficient 2 to sum rules,
breaking every ratio/product/stationarity principle tested (π/4
certificate, labeled cluster, orbit cluster via the Λ-in-N cascade,
stationarity).  The labeled-vs-orbit counting choice (birth order
physical or gauge) is the unresolved axiom this exposes.

**Selection ledger.**  Bell causality (strict, modulus): impossible.
Cluster decomposition (labeled path, event, orbit): impossible.
Stationarity: impossible.  Manifold confinement: exactly free.
One-step self-similarity: feasible, consumes 628 of 1553 dimensions at
depth 7, and pins the geometry statistics.
