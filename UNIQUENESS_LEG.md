# The uniqueness leg: complex quadratic quantum growth is forced
# (2026-08-13)

## Theorem (uniqueness of bi-normalized complex quantum growth)

Let a growth dynamics on causal orders satisfy:

  A1 LINEARITY.  Amplitudes propagate linearly (the class amplitude
     is a linear function of parent amplitudes), carrying action
     phases: per-edge factors rho * chi(g) with rho >= 0 and chi a
     unit character of the gap group (Z, +).
  A2 COVARIANCE.  Class amplitudes are independent of path order
     (the phase-telescoping property).
  A3 LOSSLESSNESS.  Record formation is reversible on ALL states:
     the step extends to an invertible measure-norm-preserving linear
     map on system (x) record (the dilation picture of
     KFCausalRecordedRefinementDilation).
  A4 FACT STABILITY.  Recorded (hereditary) events keep their
     measure under refinement, for all states.
  A5 NONCLASSICALITY.  At least one step genuinely mixes: its matrix
     is not a weighted permutation (some branching superposes).
  A6 MEASURE REGULARITY.  The measure of an amplitude is continuous,
     multiplicative along path composition, and zero only at zero.

Then:
  (i)   the measure is |.|^p for some p (A6);
  (ii)  p = 2 (A3 + A5, Lamperti obstruction - proof below);
  (iii) the amplitude algebra is commutative (A2), rules out
        quaternionic phases;
  (iv)  it is not R: with p = 2, REAL binary bi-normalized branching
        is deterministic (a,b real, a+b=1, a^2+b^2=1 => {(1,0),(0,1)})
        - so nontrivial branching at the +-1-gap root (A5) forces
        complex phases;
  (v)   hence complex Born structure with double conservation
        (sum a = 1 from A3-counitality; sum |a|^2 = 1 from A4 via the
        record-martingale dichotomy), and the root phase is quantized
        at pi/4 (root_phase_is_pi_div_four).

In words: THE UNIQUE WAY FOR TIME TO PASS WITHOUT ERASING ANYTHING,
WHILE ANYTHING NONTRIVIAL HAPPENS, IS COMPLEX QUADRATIC QUANTUM
MECHANICS - with its phase then pinned by consistency.

## The analytic core (ii): the Lamperti obstruction at 2x2

CLAIM.  For real p in [1, infinity), p != 2, there is NO 2x2 complex
matrix M with all four entries nonzero such that ||Mx||_p = ||x||_p
for all x in C^2.  (Hence a p-norm-preserving linear step has
disjoint column supports = weighted permutation = no mixing; with A5
this forces p = 2.  For p = 2 mixing isometries exist - the unitary
group - which is exactly the interference sector.)

PROOF.  Let M = [[a, b], [c, d]], all entries nonzero.  Testing
x = e1, e2: |a|^p + |c|^p = 1 and |b|^p + |d|^p = 1.  Test
x(t) = (1, t) with real t -> 0+:

    h(t) := |a + b t|^p + |c + d t|^p  must equal  r(t) := 1 + t^p.

Since a, c != 0, h is C^2 near t = 0 with
    h(0) = 1,
    h'(0) = p [ |a|^{p-2} Re(conj(a) b) + |c|^{p-2} Re(conj(c) d) ],
    h''(0) = p [ |a|^{p-2} |b|^2 + |c|^{p-2} |d|^2 ]
           + p(p-2) [ |a|^{p-4} Re(conj(a) b)^2
                      + |c|^{p-4} Re(conj(c) d)^2 ].

Case 1 < p < 2:  r(t) - 1 = t^p with t^p / t^2 -> infinity, while
(h(t) - 1 - h'(0) t)/t^2 -> h''(0)/2 finite (smoothness), and
r'(0) = 0 forces h'(0) = 0.  Matching h = r then requires
(r-1)/t^2 -> finite: contradiction.

Case p > 2:  now t^p/t^2 -> 0, so matching requires h''(0) = 0.  But
for p > 2 both bracketed terms in h''(0) are nonnegative and the
first is strictly positive (b, d not both zero - indeed both
nonzero): contradiction.

Case p = 1:  r'(0+) = 1.  h'(0+) = Re(conj(a)b)/|a| + Re(conj(c)d)/|c|
<= |b| + |d| = 1, with equality iff b = beta a, d = delta c for real
beta, delta > 0.  Repeating with x = (1, -t): equality forces
b = -beta' a, d = -delta' c with beta', delta' > 0: contradiction.

(p = 2 evades every step: r(t) = 1 + t^2 has a genuine t^2 term, and
h''(0) = 2(|b|^2 + |d|^2) = 2 with the h'(0) = 0 condition being
exactly COLUMN ORTHOGONALITY Re(conj(a)b + conj(c)d) = 0 - i.e. the
unitary sector.  QED)

General size reduces to 2x2: any overlap of two column supports
restricts to a 2x2 all-nonzero block on the span of two basis
vectors, and the same expansion applies; hence p != 2 forces disjoint
supports globally (the Lamperti structure).

## What each axiom buys, and what is honestly assumed

- A3 is the strong axiom, and it is the RIGHT one: per-fiber scalar
  p-normalization alone does NOT select p (scalar record trees with
  sum |a|^p = 1 have stable records for every p - the record-
  transport proof never uses p = 2).  The selection happens exactly
  where the repo's dilation theorems live: record formation as a
  reversible LINEAR map on all states.  Losslessness-as-reversibility
  is quantum mechanics' true fingerprint.
- A5 excludes the classical escape (permutation dynamics = relabeled
  determinism) at every p: without mixing there is no interference
  and no quantum question.
- A2 (path-order independence) forces the phase group abelian:
  noncommuting unit phases (quaternionic i, j) give path-order-
  dependent class amplitudes - covariance breaks.  Formal witness in
  the Lean file.
- (iv) is one line: (a+b)^2 - (a^2+b^2) = 2ab = 0.
- Octonions fail associativity before commutativity; excluded a
  fortiori by A2.

## Formalization status: the Lamperti leg is now FULLY machine-checked

Lean (KFCausalUniquenessLeg.lean, axiom-clean, 13 theorems):
real-binary determinism; the p = 1 discrete instance; quaternion
path-order witness; and `lamperti_columns_ne_two` - the COMPLETE
Lamperti obstruction, for EVERY real p with 0 < p, p != 2, in EVERY
dimension n, from the same four probes e1, e2, (1,1), (1,-1).

The proof needs no calculus and no duality.  With q = p/2 and
squared-norm variables, the parallelogram law couples the probe
coordinates: A_i + B_i = 2(P_i + Q_i).  Then:

  p > 2 (q > 1):  midpoint CONVEXITY of x^q bounds
    S = sum (A_i+B_i)^q <= 2^q * 2 from above, while STRICT
    SUPERadditivity (from x^q < x on (0,1)) forces S > 2^q * 2 at
    any coordinate where both columns are nonzero.
  0 < p < 2 (q < 1):  everything mirrors.  Midpoint CONCAVITY
    bounds S >= 2^q * 2 from below, while STRICT SUBadditivity
    forces S < 2^q * 2.  Same probes, inequalities reversed.

CORRECTION (2026-08-13): an earlier version of this note claimed the
four probes were provably slack for 1 < p < 2, so that band would
need the t-expansion or duality.  That claim was WRONG - it paired
the inequalities the wrong way (forward Minkowski is simply invalid
for q < 1; the valid tools at q < 1 are concavity and subadditivity,
and they point in exactly the directions needed).  The t-expansion
in the section above remains a correct alternative proof, but it is
no longer load-bearing: there is no remaining analytic debt in the
Lamperti leg.

Also machine-checked, new consequences:

- `p_two_probes_force_unitary`: at p = 2 the probes e1, e2, (1,1),
  (1,i) force conj(a)b + conj(c)d = 0 - the escape hatch at p = 2 is
  EXACTLY the unitary group.  "Lossless + mixing => unitary" is now
  a theorem, completing the dichotomy from both sides.
- `mixing_lossless_forces_p_eq_two` (NO-HYBRID THEOREM): a linear
  step preserving the total |.|^p measure that superposes any two
  basis directions anywhere forces p = 2 for the whole space.  There
  is no lossless world in which a quantum sector coexists with a
  measurement apparatus (or any sector) running on a different
  measure exponent: one interference event anywhere forces the Born
  rule everywhere.  This is why the classical world does not get its
  own probability calculus.

## The classification layer (2026-08-13, second pass)

The obstruction is now upgraded to a CLASSIFICATION, all
machine-checked in the same file:

- `lossless_ne_two_is_weighted_permutation` (POSITIVE Lamperti):
  for 0 < p, p != 2, a lossless step on C^n IS a weighted
  permutation - each column has exactly one nonzero entry, of unit
  modulus, and the entry locations form a permutation.  Proof: the
  no-hybrid theorem makes column supports pairwise disjoint; n
  disjoint nonempty supports in n coordinates are singletons
  (counting); the probe normalization pins each entry to modulus 1.
- `l2_lossless_columns_orthogonal`: general-n unitarity - an
  l^2-lossless step has orthonormal columns.  The p = 2 sector is
  exactly U(n), at every dimension.
- `lossless_dichotomy` (THE GRAND DICHOTOMY): every lossless linear
  dynamics on any measure system |.|^p is EITHER a weighted
  permutation OR lives at p = 2 with unitary structure.  There is no
  third kind of lossless time evolution.  Classical relabeling and
  quantum rotation exhaust what can exist.
- `frozen_measure_ne_two` (THE FROZEN WORLD, discrete core): for
  p != 2 there is a FIXED permutation sigma with
  ||(Tx)(sigma j)|| = ||x j|| for every state x - the action on
  measures is sigma regardless of the phase data.  Probabilities can
  only be relabeled, never continuously transported.

FROZEN-WORLD COROLLARY (continuous version; discrete core in Lean,
topological glue analytic): the lossless group at p != 2 is the
generalized permutation group S_n x T^n, whose identity component is
the phase torus T^n - and the theorem above says the torus acts
trivially on measures.  So ANY continuous path of lossless maps
starting at the identity leaves every measure fixed for all time:
in a p != 2 world, nothing observable can ever change continuously.
Only at p = 2 does the lossless group (U(n)) have continuous
directions that transport probability - Hamiltonian flow exists
only in the Born world.  "Why is time evolution unitary?"  Because
unitary evolution is the only continuous lossless motion that
exists at all.

## The theorem chain, with Lean witnesses per arrow

  A3 + A5 (lossless + some step mixes)
    => p = 2                    [mixing_lossless_forces_p_eq_two]
    => step is unitary          [p_two_probes_force_unitary]
    => amplitudes not real      [real_binary_bi_normalized_deterministic]
    => phases commute (not H)   [phase_order_matters_in_quaternions]
    => complex Born structure, root phase pi/4
                                [root_phase_is_pi_div_four, in
                                 KFCausalBornQuadraturePhase.lean]

The only analytic (non-Lean) input remaining in the uniqueness
theorem is axiom A6's classification step (continuous multiplicative
measure => |.|^p), which is classical real analysis, and the
identification of physical losslessness with linear measure-norm
preservation (A3), which is the physical content, not mathematics.

## Scope

Uniqueness is relative to A1-A6; the axioms are the honest content
and each is physically named (linearity, covariance, losslessness,
fact stability, nontriviality, regularity).  Within this frame the
answer to "why quantum?" is now a theorem chain with one analytic
lemma at its heart and machine-checked instances at its corners.
