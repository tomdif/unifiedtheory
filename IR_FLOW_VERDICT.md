# The IR flow verdict: no upward running at accessible scale —
# and the formal reading is saturation-confounded (2026-08-12)

## Data (ir_flow_interval_dimension.log; 40 quantum paths n = 60,
## finals saved to ir_flow_finals.npz; 400 sprinklings per d;
## 12 classical-uniform paths, 0 cap kills)

d_int(L) = local log-slope of closed-interval volume V against
longest-chain length L:

  window     L1-2  L2-3  L3-4  L4-5  L5-6  L6-7  L7-8  L8-9  L9-10
  quantum    0.87  1.46  1.84  1.73  1.64  1.36  1.27  1.18  0.79
  uniform    0.88  1.43  1.79  1.69  1.46  1.48  1.19  1.14  0.97
  d2-sprink  0.76  1.10  1.31  1.42  1.49  1.50  1.51  1.48  1.43
  d3-sprink  0.84  1.43  1.76  1.70  1.68  0.65
  d4-sprink  0.83  1.56  1.95

r-invariance sanity: parent 0.6378 vs thinned 0.6344 — passed (the
predicted invariance that motivated this estimator design).

## The formal reading — and why it cannot be taken at face value

The registered discriminator (quantum-minus-d2 excess trend) returned
-0.70, formally reading (iii) FLOW DOWN.  RECORDED AS CONFOUNDED, my
design error: the d2 calibration has height ~15.5 at n = 60 while the
quantum ensemble has height ~10, so the large-L windows compare
SATURATED quantum intervals (V approaching n, slope collapsing) against
unsaturated d2 ones.  The signature is unmistakable in the baselines
themselves: d3 (height ~8) crashes to 0.65 at L6-7, d4 has no windows
past L4, and the uniform-growth curve falls exactly like the quantum
one.  The pre-registration lacked a saturation control; the d2-anchored
trend is not evidence of collapse.

## The defensible statements

1. MATCHED-BASELINE COMPARISON (quantum vs classical uniform growth —
   heights 10.0 vs ~12, saturation matched): excess = +0.05, +0.03,
   +0.05, +0.04, +0.18, -0.12, +0.08, +0.04, -0.18 — mean +0.02, no
   trend.  **The quantum law adds NO scale-local dimensional running
   beyond classical growth at n = 60.**  Relative reading: (ii),
   scale-invariant.
2. NO UPWARD IR FLOW at accessible scales — reading (i) is cleanly
   excluded (every window from L4 on is flat-to-declining even before
   saturation corrections).  The running-dimension hope did not
   materialize at this size.
3. UV INTERVAL STRUCTURE IS d3-LIKE: in the unsaturated windows
   (L <= 4) the quantum curve (0.87, 1.46, 1.84) tracks the
   d3-sprinkling shape (0.84, 1.43, 1.76), sits well above d2, and
   touches toward d4 at L3-4.  Two footnotes: the classical growth
   ensemble shares this small-scale shape (it is a growth-process
   feature, not a quantum one), and it sits in tension with the
   global MM chart (d_eff ~ 1.7): the LOCAL interval dimension at
   short scales is higher than the GLOBAL ordering-fraction
   dimension — the two estimators see different structure, itself a
   diagnostic (global anti-correlation of the coordinate orders
   coexisting with locally ~3d-like intervals).
4. The thinning magnifier (thinned-to-20 small-L windows lower than
   bare) is consistent with mild downward drift of the local dimension
   at larger parent scales, but the thinned causets saturate even
   earlier — not load-bearing.

## Where this leaves the emergent-spacetime ladder

The bare quantized law at n <= 60: UV plateau at global d_eff ~ 1.7
(deep-dimension verdict), locally d3-like interval texture at short
scales, and NO sign of upward flow toward the action's dimension.  The
honest position: at accessible scales the theory is a SCALE-INVARIANT
2-ish-dimensional quantum phase, and any 4D emergence must live at
scales (or in variables — coarse-grained/record observables) beyond
this window.  The level-3 climb (MCMC to n ~ 200+, where L <= 20
windows stay unsaturated) remains the decisive instrument, now with a
sharpened estimator requirement: saturation-free windows (V << n) and
matched-height baselines, both pre-registered this time.

## Honest scope

- The saturation confound was discovered POST-registration; both the
  formal (iii) and the corrected (ii) readings are reported, with the
  matched-baseline comparison as the defensible one.
- 40 + 12 paths; interval statistics per window in the thousands at
  small L, hundreds at large L.
- The d_int estimator conditions on longest-chain length; alternative
  proper-time proxies (midpoint chains, Alexandrov-ball counts) have
  different finite-size behavior — corroboration at larger n needed.

## Registered follow-ups

1. MCMC sampler to n >= 200; d_int with V <= n/6 window cut and
   matched-height baselines (pre-registered saturation control).
2. The global-vs-local dimension split (r-chart 1.7 vs interval 1.8+
   at short scale): compute both on d = 2.5-3 fractional-like
   benchmarks to see which chart the quantum ensemble actually
   matches - possibly neither (anti-KPZ class again).
3. Coarse-grained/record-variable dimension (the possibility that 4D
   lives in the record algebra, not the bare order) - connects the
   geometry arc to the records arc.
