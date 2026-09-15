# Paper 3 — Selection principles for quantum causal growth: locality, factorization and timeless laws are impossible; coarse-graining self-similarity binds and excludes continuum-mimicking statistics

**Draft 1, 2026-08-01.**  Companion to Papers 1 (dichotomy) and 2
(landscape/existence).  Vocabulary: DEFINITIONS.md.  Scripts:
bell_cut_2d.py, cluster_gate_2d.py, orbit_cluster_exact.py,
stationarity_check_2d.py, self_similar_2d.py, positivity_qp_2d.py,
psi2_check_2d.py; certificates in PI4_CERTIFICATE.md.

## Abstract

The covariant family of 2D action-phase growth dynamics (Paper 2) is
vastly underdetermined; here we test which physical principles can
select within it, with an exact certificate for every verdict.  Every
locality- and independence-flavored principle fails: quantum Bell
causality in ratio form reduces to signature factoring and dies on the
collision table; its modulus-only weakening over-determines the family
(rank 312 against a 234-dimensional manifold); cluster decomposition
fails in labeled per-path form (after uniquely pinning the phase to
π/3), in event form (at the root), and in orbit-counted form (the
Λ-in-N cone cascade) — the recurring executioner being the multiplicity
μ = 2 of the two-antichain, which also underlies the π/4 anomaly.
Making the time order physical does not escape: per-precursor
stationary dynamics are infeasible at every phase already for
two-element universes, with or without covariance — **the couplings
must age**; no timeless rule generates action-phase growth.  One
principle survives: one-step sub-sampling self-similarity (a Bombelli
coarse-graining fixed point, linear and exactly normalized), which
consumes 628 of the family's 1553 dimensions at depth 7.  Its physical
signature is an exclusion: over the entire positivity-exact
self-similar polytope the ψ-weighted mean ordering fraction of
seven-element universes is confined to [0.253, 0.464] — in particular
its supremum lies strictly below both the 2D continuum benchmark (1/2)
and the finite-size classical sprinkling value (0.533) — whereas the
unconstrained covariant family reaches [0.124, 0.769] and so permits
continuum-mimicking statistics.  The Born-proxy (ψ²-weighted) statistic
conforms empirically: multi-start ascent over the polytope finds no
member above 0.461 (exact supremum open).  The one binding principle
forbids what the unconstrained theory allows.  The falsification target was
one-sided and has now been TESTED: at depth 8 the supremum crossed
1/2 (0.5353) and the exclusion dissolved, exactly as the dissolution
branch of this programme anticipated (§3′).  The programme is closed
negative at its first depth extension; what it delivered is the
onset structure and one completed falsification cycle.

## 1. The selection ledger (all certificates hand-checkable)

| Principle | Form | Verdict | Kill mechanism |
|---|---|---|---|
| Bell causality | strict (SZ ratio) | impossible | ⟹ factoring ⟹ collision table |
| Bell causality | modulus-only | impossible | rank 312 vs dim 234; dimension → 0 |
| Cluster | labeled, per-path | impossible | pins φ = π/3, then μ = 2 at the 2-antichain |
| Cluster | labeled, event | impossible | root forces cos φ = 1 |
| Cluster | orbit-counted | impossible | pins φ = π/3; Λ dies; N ⊃ Λ (downset) dies; L's equation reads 2 = 1 |
| Stationarity | with covariance | impossible | ⟹ Bell ⟹ factoring |
| Stationarity | without covariance | impossible | two-phasor certificate at n ≤ 2, 0/60 phases |
| Manifold confinement | dim ≤ 2 | free | zero collateral at depths 6–8 |
| Self-similarity | one-step T₆₇ | **binds** | consumes 628 dims; excludes r ≥ 0.464 |
| Self-similarity | multi-step (semigroup) | infeasible at depth | kernels compose; finite-size, not principle |

Two structural morals.  First, the failures are one failure: histories
of indistinguishable structure do not count locally — every kill traces
to embedding/automorphism multiplicities, and the labeled-versus-orbit
counting choice (is birth order physical?) is the exposed unresolved
axiom.  Second, the phases at which textbook quantum intuitions hold
exactly (π/4 quadrature, π/3 factorization) are precisely the forbidden
ones.

## 2. The aging theorem

Per-precursor amplitudes w(P) with the Markov sum rule satisfy, at any
phase, the difference of the 2-antichain and root equations:
w(•)e^{−iφ} + w(2A)e^{−3iφ} = 0 — two nonnegative phasors, cancelable
only at φ = π/2, where the root equation is purely imaginary.  Dead at
n ≤ 2 for every phase (0/60 mechanically), covariance nowhere used.
With covariance the independent route (stationarity ⟹ Bell ⟹
factoring) reaches the same verdict.  Hence: **stationary action-
coupled growth is impossible in 2D and at most trivially degenerate in
4D; the dynamical rule must be epoch-dependent.**  We note the Noether
shadow (exact energy conservation should fail at some level) and the
consonance with cosmic-renormalization and everpresent-Λ phenomenology,
where epoch-dependent couplings are precisely the required microscopic
input.

## 3. The surviving principle and its exclusion

One-step self-similarity Ψ₆ = T₆₇Ψ₇ is feasible, linear, exactly
normalized, confinement-compatible, and consumes 628 dimensions —
seven times the manifold selector's bite.  The multi-step versions are
infeasible at this depth; because sampling kernels compose exactly,
this is a finite-size statement about the semigroup fixed point, and
the constraint imposed throughout is the one-step proxy for an
asymptotic RG property — never semigroup invariance.

The steering experiment separates tuning from prediction.  Rigorous
LP ranges (τ-bisection, positivity exact) for the ψ-weighted mean
ordering fraction of 7-stems:

    plain confined family:        r_ψ ∈ [0.1241, 0.7687]
    one-step self-similar family: r_ψ ∈ [0.2533, 0.4639]

The plain family brackets both 0.5 and the classical n = 7 ensemble
mean 0.533; the self-similar family excludes both.  A withdrawn interim
value (0.32–0.35, penalty-era, ψ²-weighted at particular members) is on
record in the repository history together with the pre-registered
correction discipline that replaced it with the LP interval.

**Weighting status.**  The LP interval is ψ-weighted (linear); the
Born-physical statistic is ψ²-weighted (pre-decoherence proxy).  The
ψ²-weighted values at the ψ-extremal members and best-found bounds from
multi-start Frank–Wolfe ascent over the polytope are reported in
Section 5; the exact ψ² supremum is stated as open where it is open.

**Exact profile unreachability.**  Fitting ψ ∝ √p(random 2-orders) —
which would make |Ψ|² reproduce classical sprinkling statistics
exactly — fails at the 77% level even in the plain family: the quantum
family cannot impersonate the classical ensemble even when asked to,
which also disarms the concern that the optimization target was
trivially achievable.

## 3′. The depth-8 test: the exclusion dissolves (2026-08-02)

The falsification programme of Section 3 ran its first depth test,
with readings pre-registered (selfsim_depth8.py, selfsim_d8_ipm.log;
pipeline gated on exact reproduction of the depth-7 intervals, which
passed).  Two structural facts and one verdict:

(i) FEASIBILITY ONSET.  The one-step self-similar polytope is
genuinely empty at depths 5 and 6 (direct feasibility LPs, not a
scan artifact): one-step Bombelli self-similarity is first
satisfiable at depth 7.  The depth-7 interval was therefore the
constraint's onset point — where it binds tightest — not a generic
sample.

(ii) THE DEPTH-8 NUMBER.  sup r_psi(8) = 0.5353 (interior point,
converged; plain-confined control at depth 8: [0.1050, 0.8041],
straddling both targets as the control must).  The upper endpoint
moved 0.4639 -> 0.5353 in one level, crossing both 1/2 and the
classical sprinkling value: THE EXCLUSION WAS A DEPTH-ONSET
ARTIFACT.  At depth 8 the one-step self-similar family permits
continuum-mimicking ordering statistics, and the falsifiable
fingerprint claimed in the abstract does not survive its first depth
extension.

What remains true: the depth-7 binding (628 dims consumed, the
interval [0.2533, 0.4639]) is exact, and the constraint's bite
weakens as depth grows beyond its onset.  What is NOT yet in
evidence (referee): a mechanism.  Two feasible depths and one
monotone step are equally consistent with (a) the sup converging to
the classical value, (b) the sup sailing past it (another 0.07 step
lands at 0.60), or (c) the polytope dilating with depth as the
unconstrained control does.  "Crossed the classical value" is the
finding; "converging to it" is not a claim this data supports.

THE DECIDING NUMBER (pre-registered before it lands): the depth-8
infimum.  (i) inf rises toward the classical value as the sup
crossed it -> the interval is NARROWING ONTO the classical point,
and the result is not a dissolution but a CORRESPONDENCE CANDIDATE:
self-similar quantum growth forced toward continuum sprinkling
statistics in depth — a classical limit obtained rather than
assumed, and a stronger claim than the one that died.  (ii) inf
falls in step with the control's — the polytope is dilating, the
constraint is empty of content in depth, and this section's negative
closing stands as written.  (iii) intermediate — more depths needed,
no reading.

RESOLVED (2026-08-02, selfsim_d8_ipm.log; independently reproduced
2026-09-15).  inf r_psi(8) = 0.19626.  **READING (ii) FIRES.**  The
depth-8 self-similar interval is [0.1963, 0.5353] against depth-7's
[0.2533, 0.4639], while the control moved [0.1241, 0.7687] ->
[0.1050, 0.8041].  Both endpoints moved OUTWARD.  The correspondence
candidate of (i) is dead on arrival: the interval is not narrowing
onto the classical point, it is dilating toward the unconstrained
family.

One correction to the pre-registration's own wording.  (ii) said the
infimum would fall "in step with the control's".  It did not -- it
fell about three times as far (0.0570 against the control's 0.0191),
and the self-similar width grew 61% against the control's 8.5%.  The
constraint therefore sheds content FASTER than the ambient family
dilates, a stronger negative than (ii) anticipated; the fraction of
the control's width left un-excluded rose from 32.7% to 48.5%.

VERIFICATION NOTE.  Both depth-8 endpoints were reproduced on
2026-09-15 by an independently written construction (sparse LP,
Charnes-Cooper linear-fractional solve, interior point), gated on
exact reproduction of the depth-7 intervals: sup 0.5352513327 against
the logged 0.5352513327144708 (10 significant figures), inf
0.1962574349 against 0.19625741911367697 (8).  Both solves attain the
optimum on a recession direction (t -> 0, amplitude box inactive), as
the original run did; at depth 7 that costs 8.6e-5 against the
box-constrained tau-bisection -- four orders of magnitude below the
0.057 move in the infimum, so the verdict does not depend on it.

The abstract's exclusion claim is hereby scoped to depth 7 and the
falsification programme's first test is closed negative on the
exclusion reading, with the infimum resolving the fork to dilation.

## 4. Honest scope

All results are at depth ≤ 8, in 2D, for the literal ansatz (nonneg
moduli, action phases), at representative generic phases; ψ² statistics
are pre-decoherence proxies; "manifoldlike" is the order-dimension-2
proxy; the one-step/semigroup distinction is finite-size.  The
falsification programme is: compute the self-similar sup r at each
accessible depth; the exclusion survives exactly as long as the sup
stays bounded away from 1/2.

## 5. Computed supplements

**ψ²-weighting.**  At the ψ-extremal members of the self-similar
polytope: near the supremum, r_ψ = 0.4638 with r_{ψ²} = 0.4520; near
the infimum, r_ψ = 0.2533 with r_{ψ²} = 0.1808.  Multi-start
Frank–Wolfe ascent on the ψ²-weighted ratio over the polytope (five
starts, both senses) finds best r_{ψ²} = 0.4611 and worst 0.1567; no
member was found within 0.039 of 1/2.  The exclusion is therefore
rigorous in ψ-weighting and empirically weighting-independent; the
exact ψ² supremum (a nonconvex maximum) remains open and is listed as
such.

**Profile fit.**  The positivity-native ρ-continuation fit of
ψ ∝ √p(random 2-orders) inside the self-similar family did not converge
to the constraint set (equality residual 9.45) and is reported as
numerically unresolved — and unnecessary: the LP ranges above already
preclude classical statistics.  In the plain family the earlier fit
reached 77% relative error at a 1.9% equality violation; the
unreachability claim is quoted with that violation caveat.

**Coherence check.**  The canonical confined member's one-step Bombelli
defect is 2.509 against random-vertex defects spanning 2.37–3.20: the
canonical construction is not anomalously close to the fixed point, and
its ordering fraction landing inside the withdrawn penalty-era interval
was coincidence.  We state this plainly rather than let the numbers
suggest otherwise.

## Status ledger

[LEAN] the aging certificate's arithmetic and the μ = 2 kills' common
engine are queued for formalization; the collision/parity substrate is
already formal (Papers 1).  [MECH] every ledger row is an exit-0 script
with exact LP/rank verification.  [PHYS] the ansatz; ψ² as physical
proxy; one-step as RG proxy.  Open: the ψ² supremum; depth growth of
the self-similar sup; the counting-convention axiom; decoherence of the
self-similar member.
