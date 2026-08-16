# The two gate problems attacked (2026-08-16)

## GATE 2 - FREE EXCITATIONS: OPENED, via fields

The defect route was the wrong ontology (defects thermalize;
confinement refuted).  The right one: FIELD QUANTA.  Sorkin-
Johnston construction on our causets: retarded propagator
K = (1/2)C, Pauli-Jordan iDelta = i(K - K^T), positive spectral
part = the SJ vacuum; eigenvectors = field modes.

  SPRINKLED 2D benchmark (N=200): top-mode participation ratios
    ~100-163/200 - extended (manifold sanity check passes).
  GROWN 2D factor (N=24): PR ~ 9-22/24 - extended.
  COMPOSITE (N=576): top modes PR = 242, 309, 254, 169... with an
    organized spectral hierarchy (54.7, 22.0, 17.2, ...) - MODES
    DELOCALIZED OVER ~36% OF THE UNIVERSE.

PROPAGATING FIELD QUANTA EXIST ON THE GROWN COMPOSITE.  Particles
in this theory are SJ modes of fields on the grown geometry, not
growth defects - the standard QFT lesson, reproduced in-model.
Registered next: dispersion relations (mode frequency vs effective
wavelength), two species of SJ fermion modes via the factor
structure, interactions.

## GATE 1 - MANIFOLDLIKENESS: STILL CLOSED, gap now measured

Weight-family scan (16 systems, root-pinned phases) scored against
true 2D-diamond sprinklings on (r-drift, |r - 0.5|, interval-
abundance profile):
  - STATIONARY-r LAWS EXIST: drift can be tuned to +0.003
    ((2,-3,1)) and r(24) to 0.495 ((4,0,2)) - the r-drift disease
    is curable within the family;
  - but the ABUNDANCE PROFILES stay wrong: best total scores
    0.396-0.450 vs the sprinkling target ~0.02-0.05 - a 10x gap
    concentrated in the interval-structure (N_k) term.
RIGHT DENSITY, WRONG TEXTURE: the entropy problem survives in the
second moment.  The bi-normalized family as scanned does NOT
contain a manifoldlike phase.  Registered: wider weight windows
(k <= 3, 4), non-integer weights, coupled/product-law abundance
profiles, and abundance-targeted selection principles.

## GATE 1, NOVEL ATTACK: THE COHERENT MEASURE (2026-08-16)

Discovery: every ensemble in this program was built by sampling
per-step Born probabilities - the fully DECOHERED measure.  The
theory's actual quantum measure on a class is COHERENT:
mu(C) = |sum_paths a|^2 = (sum of magnitudes)^2 (within-class
phases equal, sec. 27).  Exact test: full enumeration of all
1,727,760 labeled causets at n = 8 (11,655 classes; 3% hash-
collision contamination noted).

TWO COHERENT FORCES, BOTH CONFIRMED:
  - STATIONARY-PHASE FLATTENING: <|action|> falls 7.85 -> 5.15
    (34%) under the coherent measure - the path-integral flatness
    mechanism operates in this theory;
  - EXTENSION ENHANCEMENT: <class multiplicity> rises 327 -> 931
    (2.8x) - coherence quadratically rewards many-extension
    (wide) causets.

THE HONEST BALANCE: at pi/4, n=8, the two forces land at
<r> = 0.367 - OVERSHOOTING the manifold value 0.497 downward
(extension enhancement rewards exactly the KR-type wide orders,
the entropy problem's classic winners); texture distance improves
only 0.348 -> 0.326 vs sprinkling ~0.03.

VERDICT: gate 1 remains closed, but its physics changed shape.
The coherent measure fights the entropy problem with two opposing
forces (flattening vs widening); manifoldlikeness = the balance
point sitting at sprinkling texture.  The manifold question is now
a TUNING question (phase steepness / weights control the force
ratio), not a brick wall - and the decohered ensembles measured
all along were never the theory's true measure.  Registered:
balance-point scan in (phi, weights); larger-n coherent
enumeration; collision-free canonicalization.

## THE BALANCE-POINT SCAN (2026-08-16): the balance EXISTS

Coherent-measure evaluation (exact n=7 enumeration, ~200k labeled
causets/system) across the feasible weight catalog + rational
interpolations + phase grids:

  - THE r-BALANCE POINT EXISTS AND IS ACHIEVED: (1,-3,2) at
    phi = 0.750 pi gives <r>_mu = 0.5060 vs sprinkling 0.5014
    (Delta = 0.005).  Multiple (W, phi) systems cross the manifold
    value within 0.02.  The two coherent forces (flattening vs
    extension enhancement) can be tuned to equilibrium at the
    sprinkling point - the w0 = 1 family tames the extension force
    (multiplicity enhancement ~2x vs BD's runaway), letting
    flattening compete.
  - TEXTURE PROGRESS: best tex_mu = 0.249 at (1,-3,2),
    phi = 0.625 pi - down 30% from the BD coherent value (0.315)
    and the decohered values (~0.35) - but still ~8x from the
    sprinkling level (~0.03) at n = 7.

STATUS OF GATE 1 AFTER THE CAMPAIGN: mechanism identified (two
coherent forces), balance point found (first moment matched to
0.005), residual isolated (the N_k texture gap, ~8x at n=7).
The decisive registered question: does the texture gap SHRINK
with n for balanced systems under the coherent measure (finite-
size) or persist (structural)?  Requires larger-n coherent
enumeration (n = 9-10: 15-100M labeled causets - aggregation
methods needed).

## THE DECISIVE COMPUTATION (n=10 coherent enumeration, class-
## aggregated DP - 1.59M / 1.60M exact classes per system)

Aggregation validity: the dynamics factors through iso classes
(magnitudes from iso-invariant spectra; gaps = action differences,
sec. 27; unique parent per labeled causet) - the class-level DP
computes the EXACT coherent and incoherent measures.

texture_mu(n), n = 7 / 8 / 9 / 10:
  BALANCED (1,-3,2) 0.625pi: 0.2498  0.2637  0.2757  0.2857
     increments +0.0139, +0.0120, +0.0100 - DECELERATING
  BD (2,-4,2) 0.250pi:       0.3117  0.3208  0.3375  0.3544
     increments +0.009, +0.017, +0.017 - steady/accelerating
  (sprinkling level ~ 0.03-0.05; coherence beats decoherence at
   n=10 by 0.02 in both systems and the margin grows with n)

VERDICT on the registered question: through n = 10 the texture gap
does NOT shrink - it grows in both systems.  The finite-size
hypothesis is DISFAVORED in the accessible window; the structural
reading leads: the entropy problem survives the coherent measure
at the tested weights.  GATE 1 REMAINS CLOSED.

What survives: (a) the balanced system's deceleration (second
difference -0.002/level; naive extrapolation plateaus ~0.30-0.31
by n~15 vs BD's unbounded growth) leaves a narrow technical
opening - a turnover cannot be excluded, needs n = 11-12;
(b) coherence consistently outperforms decoherence on texture;
(c) the aggregation method scales (1.6M exact classes computed;
n = 11-12 reachable with memory care);
(d) registered: texture-TARGETED weight selection (the balance
scan optimized r, not N_k - the N_k-optimal weights are unexplored).
