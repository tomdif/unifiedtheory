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

Lean (KFCausalUniquenessLeg.lean, axiom-clean, 43 theorems):
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

## The divisible-time theorem (2026-08-14): A5 eliminated

The classification above still consumed the nonclassicality axiom
A5 ("some step mixes") - a quantumness assumption invoked to derive
quantum mechanics.  It is now REPLACED by a statement about time,
machine-checked in the same file:

- `frozen_measure_pow`: iterating the frozen world - the k-th power
  of a lossless p != 2 step moves measures by the k-th power of its
  permutation: ||(S^k x)(sigma^k j)|| = ||x j||.
- `root_at_symmetric_order_forces_static`: a lossless p != 2 step
  raised to the power m = |Perm(Fin n)| = n! is measure-static -
  Lagrange's theorem (pow_card_eq_one) kills the permutation part.
- `divisible_time_forces_static` (static form): if the step T of a
  lossless p != 2 dynamics has a lossless m-th root for EVERY m
  (time has no smallest step), then ||T x j|| = ||x j|| for every
  state and coordinate.  In a p != 2 world with divisible time,
  nothing ever happens.  (Proof: take the root at m = n! and apply
  the previous theorem.  No topology - the n! trick replaces the
  continuity argument entirely.)
- `change_and_divisibility_force_born` (headline form): LOSSLESSNESS
  + TIME HAS NO SMALLEST STEP + SOMETHING HAPPENS  =>  p = 2, hence
  (by the dichotomy) unitary quantum mechanics.  All three axioms
  are statements about time; none mentions superposition,
  interference, or any quantum concept.

Honest scope: "divisible time" is formalized as exact m-th roots in
the lossless semigroup for every m >= 1 - the discrete surrogate for
continuity (a continuous lossless one-parameter flow through T
supplies such roots by S = flow(t/m)).  The hypothesis asks the
roots to be lossless for the SAME exponent p, which is the physical
meaning of sub-steps of a lossless evolution.  Note the theorem
needs only ONE root order, m = n!; full divisibility is assumed
because that is the physical axiom, and the proof then chooses its
weapon.

## The purity pass (2026-08-14): reducing the axioms themselves

Four further machine-checked reductions (same file, now 27 theorems):

- `root_at_group_exponent_forces_static`: the consumed root order
  sharpened from n! to the group exponent of S_n = lcm(1,...,n)
  (n = 10: 2520 vs 3628800).  One lossless root at that single
  order forces staticity.
- `antiunitary_has_no_half_step` (+ `square_of_semilinear_is_linear`):
  the square of ANY semilinear map — linear or conjugate-linear —
  is complex-LINEAR, so a nonzero conjugate-linear (antiunitary)
  step has no semilinear square root at all.  The divisibility
  axiom, applied at m = 2, eliminates antiunitary evolution: time
  evolution is unitary rather than antiunitary BECAUSE HALF-STEPS
  EXIST.  Purely algebraic; no norm appears.  (That real-linear
  lossless maps at p = 2 are unitary-or-antiunitary is Wigner's
  classification — the recorded seam.)
- `lossless_bijection_is_real_linear` (LINEARITY DERIVED,
  Mazur-Ulam): for p >= 1, ANY surjective map of state space
  preserving the state measure and pairwise distinguishability
  (the measure-distance between any two states) is real-linear.
  The linearity axiom A1 reduces to losslessness-of-information:
  no linear structure is assumed of the dynamics.  Boundary:
  0 < p < 1 is a quasi-metric band where Mazur-Ulam does not
  apply; complex-vs-conjugate linearity is the Wigner gap, closed
  at p = 2 by the half-step theorem above.
- `born_function_unique` (+ `monotone_additive_on_cone_is_linear`,
  THE BORN FUNCTION FROM MONOTONE CAUCHY): a measure additive over
  perpendicular decompositions and monotone in amplitude is
  EXACTLY f(x) = x^2 f(1) — the Born function itself, not merely
  the exponent.  NO CONTINUITY ASSUMED: monotone solutions of
  Cauchy's functional equation are linear (rationals pin the
  values, order squeezes the irrationals; Hamel pathologies are
  killed by monotonicity, not topology).  This makes the
  classification half of A6 a theorem.  Registered open seam: the
  existence half — deriving Pythagorean additivity of the measure
  from a mixing lossless step (the Orlicz-Lamperti generalization
  of the structure theorem).  With that, A6 dissolves entirely.

The axiom set this pass targets, in its purest currently-motivated
form:

  * probability is additive over the alternatives time creates,
    and monotone in amplitude          [born_function_unique makes
                                        the quadratic form a THEOREM
                                        given Pythagorean additivity]
  * time passes without information loss
                                       [now includes linearity via
                                        Mazur-Ulam — A1 no longer
                                        independent for p >= 1]
  * time has no smallest step          [kills the permutation part
                                        (n!/lcm root + Lagrange) AND
                                        the antiunitary branch (m=2)]
  * something happens                  [the nontriviality trigger]

What remains genuinely assumed: the preferred branching basis (the
additive decomposition the causal order supplies — physical bedrock,
named, not hidden); finite dimension n (the lcm trick is finitary;
note the infinite shift has NO m-th roots in Sym(Z), so divisibility
constrains infinite permutations too — open); the Wigner
classification seam; the Orlicz-Lamperti seam; and 0 < p < 1 for
the Mazur-Ulam step.

## THE ZERO-STRUCTURE CAPSTONE (2026-08-14, second pass):
## the Born exponent from a bare set-map of states

`born_from_time_alone` (machine-checked, axiom-clean; file now 33
theorems).  Hypotheses — and this is the entire list:

  * a number p >= 1, fixing the measure sum ||.||^p;
  * for every m, a SET-MAP G of the state space with G^[m] = F,
    surjective, preserving the state measure and pairwise
    distinguishability (time has no smallest step; sub-steps lose
    nothing);
  * some measure changes under F (something happens).

Conclusion: p = 2.  NOTHING ELSE IS ASSUMED.  Not linearity, not
additivity, not complex structure, not even that F itself is
lossless (it is a composite of lossless roots — derived).  The
dynamics enters as a bare function on states.

The internal chain: Mazur-Ulam turns each root into a REAL-linear
map; a new real block-structure theorem
(`real_lossless_frozen_measure`) shows that an R-linear lossless
step at p != 2 moves measures by a fixed permutation — the
complex-linearity of the earlier structure theorems was never
essential, because the Lamperti probes are all real combinations of
the 2n real basis directions e_j, i*e_j, and the within-block pair
(e_j, i*e_j) is exactly the one the probes cannot couple
(||1+i||^p != 2): the block structure is FORCED by what the probes
cannot say.  Then the group-exponent root plus Lagrange freezes
every measure, contradicting change.

What structure remains in the hypotheses, exhaustively: the measure
family Sum ||.||^p itself (the last structural plank; section 15's
monotone-Cauchy theorem shows how it dissolves given Pythagorean
additivity — the Orlicz-Lamperti seam); p >= 1 (Mazur-Ulam's
metric band); finite n; the preferred branching basis.  And the
conclusion is the Born EXPONENT: upgrading p = 2 to full unitarity
requires complex structure on the dynamics (an O(2n)-vs-U(n) gauge
seam — measure-losslessness alone at p = 2 permits all real-
orthogonal maps; unitarity additionally needs phase covariance or
Wigner's transition-probability hypothesis).

In Lean terms this is now literally a zero-axiom theorem: every
hypothesis is a plain mathematical statement about a function and
a number, and the proof closes over propext / Classical.choice /
Quot.sound alone.

## THE FULL PACKAGE + THE FIRST BREACH (2026-08-14, third pass)

Two further machine-checked summits (file now 38 theorems):

`quantum_mechanics_from_time_alone` — the gauge seam is CLOSED.
The zero-structure capstone concluded only p = 2, because
measure-losslessness at p = 2 permits all of O(2n).  Adding the one
physically-forced covariance — the global phase is unobservable, so
each sub-step commutes with it (only the quarter-turn x -> i*x is
used) — upgrades Mazur-Ulam's real-linearity to complex-linearity
(`phase_covariant_real_linear_is_complex_linear`), and with p = 2
the general-n unitarity theorem delivers orthonormal columns.
Final form: for p >= 1, if every m admits a surjective set-map
root of F preserving measure, distinguishability, and phase, and
anything changes, then p = 2 AND F is complex-linear with
orthonormal columns.  UNITARY QUANTUM MECHANICS, WHOLE, from three
named physical inputs: time (divisible, lossless), gauge (phase
unobservable), change.

`balanced_beam_splitter_forces_born` — the Orlicz-Lamperti wall is
BREACHED at the canonical mixing step.  For an ARBITRARY monotone
measure Sum f(||.||) (no power family, no continuity, f(0) = 0):
losslessness across one balanced two-way interference step — a
50/50 beam splitter, columns (e1 +- e2)/sqrt(2) — forces
f(x) = x^2 f(1) exactly.  Probing the splitter gives
f((s+t)/sqrt2) + f(|s-t|/sqrt2) = f(s) + f(t); t = 0 yields the
halving law f(s/sqrt2) = f(s)/2; together they produce the
Jordan-von Neumann quadratic functional equation
f(s+t) + f(s-t) = 2f(s) + 2f(t), whose monotone solutions are
exactly x^2 f(1) (`monotone_quadratic_functional_eq` — naturals by
two-step induction, rationals by scaling, irrationals by order
squeeze; no topology anywhere).  Dynamical wrapper from an actual
lossless real-linear step: `lossless_beam_splitter_step_forces_born`.

Physics reading: INTERFERENCE AND PROBABILITY-ADDITIVITY COEXIST
FOR EXACTLY ONE MEASURE CALCULUS.  A world with a monotone measure,
losslessness, and one balanced interference event is already Born.
What remains of Orlicz-Lamperti: arbitrary mixing matrices (not
just the canonical splitter) for general monotone f — the last
stretch of the wall.

## DENSE SPLITTING RIGIDITY (2026-08-14, fourth pass):
## generic interference forces Born over ALL monotone measures

The beam-splitter breach needed one fine-tuned 50/50 event.  The
fine-tuning is now removed (file at 43 theorems):

`dense_splitting_forces_linear` / `splitter_family_forces_born` /
`lossless_splitter_family_forces_born`: a monotone measure
Sum f(||.||) lossless across two-way splitters of a DENSE set of
transmittances lambda in (0,1) is exactly f(x) = x^2 f(1).  Only
ONE column per splitter is consumed.

The mathematical heart, and the new tool of the pass, is
`dense_splitting_no_jump`: CONTINUITY IS DERIVED, NOT ASSUMED.  If
the measure had a jump of size J at some y, the split identity
g(lam*x) + g((1-lam)*x) = g(x) transports increments, so EVERY
available ratio copies the jump in full onto the pair
{lam*y, (1-lam)*y}; N distinct ratios give N disjoint copies below
y, but a monotone function has only finite total variation there —
contradiction for N large.  Order kills the jump.  Continuity then
extends the split identity from dense ratios to all ratios, giving
exact Pythagorean additivity, and monotone Cauchy finishes.  The
only inputs anywhere are ORDER and LOSSLESSNESS.

Physics: a dense transmittance family is what ONE GENERIC
interference device supplies — iterating a single lossless rotation
of angle theta with theta/pi irrational produces splitters of
transmittance cos^2(k*theta), dense in (0,1) (orbit density of
irrational rotations; classical — its Lean formalization via
AddSubgroup.dense_or_cyclic is the one remaining glue step of this
pass, cited not formalized).  So: A WORLD WITH A MONOTONE MEASURE,
LOSSLESSNESS, AND ONE GENERIC INTERFERENCE DEVICE ITERATED IN TIME
IS ALREADY BORN.  Fine-tuning is not required; genericity suffices.

Orlicz-Lamperti status after this pass: the measure family is
forced to Born by (i) one exact 50/50 splitter [section 18], or
(ii) any dense family of splitters [this section].  What remains is
the single-arbitrary-matrix case (one fixed mixing step with no
special structure and only its own powers available) — the last
stretch of the wall.

## The theorem chain, with Lean witnesses per arrow

  A3 + A5 (lossless + some step mixes)
    => p = 2                    [mixing_lossless_forces_p_eq_two]
  or, WITHOUT A5:
  A3 + divisible time + something happens
    => p = 2                    [change_and_divisibility_force_born]
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
