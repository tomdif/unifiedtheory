# Emergent dimension of the quantized 4D law at birth scale:
# no 4D at n <= 20 — instead, dimensional reduction to d_eff ~ 2
# (2026-08-12)

## The question and the instrument

Does the unique quantized 4D growth law (action-phased bi-normalized,
phi4 = 4/sqrt6) grow four-dimensional order statistics?  First-ever
measurement, enabled by the canonicalization-free gap sampler extended
to the 4D bracket (gap of a birth with downset D:
g = 1 + sum_{y in D} c(k_y), c = (-1,+9,-16,+8), fully vectorized over
downset bitmasks; anchors verified).  200 quantum paths to n = 20;
baselines at MATCHED n: diamond sprinklings d = 2..5 (50k samples),
classical uniform growth (400 paths), fan/chain references.  Readings
registered in emergent_dimension_4d.py.

## Feasibility hardened again

ZERO infeasible parents in 200 paths x 19 growth steps: the
phi4 = 4/sqrt6 theory exists on every visited parent state through
depth-19 (n = 20 causets).  And the branching-onset prediction of
four-d-normalization-check is CONFIRMED in-sample: the law is exactly
deterministic through the 5-element parent (H = 0) and branches first
at the 6-element parent (H jumps to 0.51 nats), precisely where the
sine-sign crossing of the fan-top gap said it must.  (The predicted
RECURRENCE period ~3.85 is untestable on typical paths — they leave
the fan at the first branch; ensemble H then rises smoothly to 4.25
nats at n = 19.)

## The measurement

  r(n) = ordering fraction; sprinkling baselines are n-independent:
  d=2: 0.500  d=3: 0.229  d=4: 0.099  d=5: 0.043.

   n    quantum      uniform    (d=2)   (d=4)
    6   0.3333       0.5035     0.501   0.099
    8   0.4041(87)   0.5079     0.500   0.099
   12   0.5086(88)   0.5175     0.500   0.099
   16   0.5490(64)   0.5322     0.501   0.099
   20   0.5644(51)   0.5441     0.501   0.099

  Texture at n = 20 (quantum vs uniform): minima 1.76 vs 2.48
  (near-single origin), links 44.9 vs 40.5 (relation-dense), height
  5.75 vs 6.21 (SUB-classical height - not chain collapse; a dense,
  ordered, moderately tall geometry).

## Verdict

Registered reading (i) — emergent 4D — is NOT observed: at matched
size the 4D-diamond value is r ~ 0.099 and the quantum law sits at
0.56, five sigma-decades away and moving in the other direction.  The
mechanical "nearest d" is 2, but r does not TRACK the 2D value — it
crosses it (n ~ 11) and keeps rising at ~+0.003/element (declining
increments), i.e. the effective Myrheim-Meyer dimension falls through
2 and continues slowly downward at n = 20.

THE HONEST PHYSICS FRAMING: n <= 20 is the deep-UV regime, and
**every major quantum-gravity program reports dimensional reduction to
d_eff ~ 2 at UV scales** (CDT spectral dimension, asymptotic safety,
Horava).  Measured d_eff ~ 2-and-drifting at Planckian sizes is
therefore not the naive failure of the fixed-point hypothesis — it is
consistent with the universal UV signature, HERE DERIVED FROM A UNIQUE
PARAMETER-FREE QUANTUM LAW rather than postulated dynamics.  What the
data cannot yet decide is the crossover question:

  - r(n) SATURATES (d_eff plateaus near 2, then grows toward the
    action's dimension at larger n): the standard dimensional-
    reduction narrative, emerging from first principles — the
    headline outcome, still open;
  - r(n) keeps rising (degenerate hyper-ordering): the law never
    becomes manifold-like — reading (ii) at all scales.

The increments are falling (0.0085 -> 0.0069 -> 0.0059 per two
elements over the last six), mildly favoring saturation, but n = 20
cannot arbitrate.  The decisive tool is an MCMC-over-downsets sampler
(the 2^n enumeration caps the current method at n ~ 22); registered
as the top follow-up.

## What stands regardless

1. First measurement of the quantized theory's emergent geometry:
   near-single origin, relation-dense, sub-classical height, d_eff
   falling through 2 at UV sizes — its geometric identity card.
2. Branching-onset prediction confirmed exactly (n = 6).
3. phi4-feasibility verified to n = 20 (zero failures, ~3800 parent
   states).
4. The 2D-engine contrast: there the quantum law's height exponent
   EXCEEDED classical (0.69 vs 0.58) while here height is
   sub-classical - the two engines deform geometry differently;
   dimension-dependence of the quantum deformation is itself a
   measurable structure.

## Honest scope

- n <= 20, 200 paths; gap-max-entropy selection (band caveat as
  before); the burst-period component of the prediction untested
  (fan-conditional).
- MM ordering fraction is one dimension estimator; midpoint-scaling
  and spectral dimension would discriminate "reduction to 2" from
  "collapse below 2" more sharply - both need larger n.
- The d = 2..5 baselines are diamond sprinklings; other frames (box,
  cylinder) shift r by O(1) factors but nothing brings 4D near 0.56.

## Registered follow-ups

1. MCMC-over-downsets sampler -> n ~ 50-100: the saturation-vs-
   collapse discriminator (THE question this unit isolates).
2. Spectral-dimension estimator on the sampled ensembles (random
   walks on the causet) - the sharpest contact with the CDT/AS
   dimensional-reduction literature.
3. The 2D-engine version of this scan (pi/4 law) for the same
   observables - cross-engine universality of the quantum deformation.
