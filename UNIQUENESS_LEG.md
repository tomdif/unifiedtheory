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

Lean (KFCausalUniquenessLeg.lean, axiom-clean, 58 theorems):
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

## THE DENSITY GLUE FORMALIZED (2026-08-14, fifth pass):
## one generic rotation forces Born, citation-free

The fourth pass cited one classical fact (orbit density of
irrational rotations).  That citation is now a theorem (file at 48):

- `cos_sq_orbit_dense`: for theta/pi irrational, the squared
  cosines {cos^2(k*theta) : k in N} are dense in (0,1).  Proof:
  AddSubgroup.dense_or_cyclic applied to Z*theta + Z*pi — the
  cyclic branch would make theta/pi = m/n rational — plus
  continuity of cos^2 and the pi-periodicity
  cos^2(x + n*pi) = cos^2(x).
- `rotation_block_iterate`: iterating a lossless step whose
  (k1,k2)-block is rotation by theta yields rotation by k*theta on
  the same block (angle addition, induction; the `module` tactic
  closes the vector identity).
- `generic_rotation_forces_born` — END-TO-END, NO CITATIONS
  ANYWHERE IN THE PROOF TREE: a monotone measure Sum f(||.||)
  (f monotone, f(0) = 0, NOTHING else — no continuity, no power
  family, no convexity) lossless under a single real-linear step
  containing one rotation block of irrational angle satisfies
  f(x) = x^2 f(1).

Physics: ALMOST EVERY INTERFERENCE DEVICE — all but a measure-zero
set of angles — FORCES THE BORN RULE BY ITSELF, through its own
iterates.  A world with any monotone notion of probability, one
lossless generic beam splitter, and time to iterate it, has no
choice about how to weigh alternatives.

What now remains of Orlicz-Lamperti, exactly: (a) rational-angle
rotations other than the 50/50 splitter of the third pass (their
iterates close into a finite family, so density fails; only the
two-parameter probe equations remain), and (b) a single mixing step
of arbitrary non-rotation form.  Both are functional-equation
problems with only finitely many splitting relations plus the full
two-parameter family — open, and precisely delimited.

## EXCHANGE TRANSPORT (2026-08-14, sixth pass): every mixing block
## forces continuity — the rational-angle residue breached

The wall's remaining piece was rational-angle rotations, whose
iterates close into a finite family (density fails).  New mechanism,
needing NO iteration (file at 51 theorems):

Subtracting the (s,t) and (s,-t) probes of ONE mixing block cancels
the input measure and leaves the EXCHANGE IDENTITY

  g((u+v)^2) - g((u-v)^2) = g((ku + v/k)^2) - g((ku - v/k)^2),

k = sigma/c: the measure's increment over an interval around u^2
equals its increment over a mirror interval around k^2 u^2.  With
explicit finite brackets (no limits anywhere), this TRANSPORTS
JUMPS: a jump of size J at w is copied IN FULL to k^2 w
(`jump_transport`).  For a lopsided block (c^2 != sigma^2), k^2 < 1
in one of the two directions, and iterated transport lays
infinitely many full-size copies of the jump down the geometric
ladder k^(2N) w; finitely many disjoint copies already exceed the
total variation of a monotone function
(`exchange_descent_no_jump`).  Order kills the jump — third
distinct jump-killing mechanism of the arc (after dense splitting
and the balanced quadratic equation).

`mixing_block_forces_measure_continuity`: a monotone measure
lossless under ONE real-linear step containing a rotation-form
block with c*sigma != 0 and c^2 != sigma^2 — ANY angle, rational or
irrational, and NO normalization of the block required — has no
jumps anywhere.

STATE OF THE WALL after six passes:
  - balanced blocks (c^2 = sigma^2): full Born  [section 18]
  - irrational-angle blocks: full Born          [section 20]
  - every other mixing block: continuity        [this section]
The residue is exactly: CONTINUOUS monotone g under the finite
per-scale constraint family of one rational-angle block.  In angle
variables the constraint reads: K_y(phi) := g(y cos^2 phi)
+ g(y sin^2 phi) is theta-periodic at every scale y.  REGISTERED
ATTACK (harmonic-analytic, not yet formal): the Mellin symbols
Psi_s(phi) = cos^(2s) phi + sin^(2s) phi have Fourier coefficients
with Gamma-function closed forms; for non-integer s no coefficient
vanishes (Gamma poles), and for integer s >= 2 the binomial
coefficients are positive — so joint vanishing of the forbidden
modes happens only at s in {0,1}, which would pin g linear.  The
open lemma is exactly this coefficient nonvanishing plus a Mellin
representation argument for monotone g.

## STABILITY (2026-08-14, seventh pass): the reconstruction becomes
## an experimental inequality

All prior theorems assumed EXACT losslessness — an idealization no
laboratory meets.  Now (file at 53 theorems):

`monotone_quadratic_stability`: a monotone approximate solution of
the quadratic functional equation (defect <= delta) is uniformly
delta/3-close to an exact Born function.  Hyers' geometric sequence
f(2^n x)/4^n provides the limit; crucially its classification uses
OUR monotone rigidity (section 18) rather than the regularity
assumptions of the classical Hyers-Ulam literature — the limit is
monotone because f is, and monotone exact solutions are exactly
x^2 c.

`approximate_beam_splitter_near_born`: if the balanced-splitter
losslessness holds only to precision delta (each probe's measure
balance off by at most delta), the monotone measure is uniformly
within (4/3)*delta of an exact Born function f(x) = c x^2.

PHYSICS: FINITE-PRECISION INTERFERENCE DATA QUANTITATIVELY BOUNDS
BORN-RULE DEVIATIONS.  A laboratory certifying measure balance to
delta across one balanced interferometer's probe family certifies
the Born weighting itself to (4/3)*delta — the measure-calculus
analogue of the Sinha triple-slit bounds on the Sorkin parameter
(those bound third-order interference; this bounds deviations of
the measure function itself, over the entire monotone class, with
no parametric deformation family assumed).  It converts the
no-deformation no-go into an inequality an experiment can consume:
near-losslessness forces near-Born, with an explicit constant.

## THE WALL FALLS (2026-08-15, eighth pass): one mixing block plus a
## dialable phase forces Born on all monotone measures

The Orlicz-Lamperti wall - fought case by case through passes three
to six (balanced / dense-family / irrational-angle / continuity for
the rest) - is DOWN, by an argument simpler than any of the partial
ones (file at 56 theorems):

Every earlier pass probed with REAL amplitudes.  Probing the block
with s*e1 + t*e^(i psi)*e2 leaves the input measure f(s)+f(t)
UNCHANGED while the output argument sweeps the continuous interval
[(cs - sigma t)^2, (cs + sigma t)^2] as the phase psi turns.  So
the level pair-sum g(u) + g(S-u) is constant on a continuum of
overlapping intervals, and chaining them across the level (explicit
ladder with steps mu* = 4PQ/(P+Q)^2, finitely many, no limits)
forces EXACT Pythagorean additivity: `phase_interval_additivity`.
No continuity, no monotonicity, no density, no jump-killing - the
constancy chains by pure logic (two constants agreeing on an
overlap point are equal).

`complex_mixing_block_forces_born`: a monotone measure Sum f(||.||)
(f(0)=0, NOTHING else) lossless under one C-linear step containing
a rotation-form mixing block - ANY angle, balanced or lopsided,
rational or irrational, unnormalized - satisfies f(x) = x^2 f(1).
Monotonicity enters exactly once, at the final monotone-Cauchy
classification.

PHYSICS (final form of the statement this program set out to earn):
ONE INTERFERENCE DEVICE PLUS THE FREEDOM TO DIAL A PHASE forces the
Born rule over the entire monotone measure class.  The rational-
angle residue and its registered Mellin attack are moot - the
missing ingredient was never harmonic analysis, it was the phase
knob every interferometer already has.

Honest scope: sections 18-21 retain independent content (real-probe-
only results; derived-continuity theorems).  Remaining beyond the
theorem: blocks not of rotation form (two arbitrary complex
columns) - and the monotone-measure grand capstone (divisible time
+ phase covariance + change => Born function + unitarity, with the
measure family fully dissolved), now within reach by combining S23
with S16-17.

## THE POSTS LIMIT (same day): bounce suppression is a derived
## number pair, not an exponent

posts_survival.py (registered readings): the survival model
posts(n+1) = posts(n)*s_n + tau_n built from measured one-step
quantities CLOSES for both chains (reading (i)): classical tracks
within ~1% in the tail, quantum within ~10%.  Structure: top
creation tau_n is summable for BOTH laws (classical n^-3.1, quantum
n^-2.7); the separation lives in SURVIVAL: classical posts become
immortal ((1-s_n) ~ n^-3.2), quantum posts keep being killed
((1-s_n) ~ n^-1.5).  Consequence: posts(n) tends to POSITIVE
LIMITS, not power-law zero - classical ~ 0.16, quantum ~ 0.02.
The earlier 'posts exponent' table was a window transient; the
zero-parameter statement is the asymptotic bounce-probability pair
(~0.02 vs ~0.16, a 7-10x suppression), now DERIVED from one-step
law properties.  (Also: the r(n) crossover of the seventh pass is
LAW-VARIANT-DEPENDENT - the min-norm band member shows g(20) =
+0.035 with no crossing - so it is demoted from breakthrough
candidacy; the selection band dominates bulk r at accessible n.)

## THE TERMINAL THEOREM (2026-08-15, ninth pass): quantum mechanics
## from probability + lossless time + gauge + one beam splitter

`quantum_mechanics_from_a_beam_splitter` (machine-checked,
axiom-clean; file at 57 theorems).  Hypotheses, complete:

  * f monotone, f(0) = 0, f not identically zero;
  * F a bare SET-MAP of states: surjective, preserving total
    f-measure and pairwise f-distinguishability, commuting with the
    global quarter-turn phase;
  * one lossless beam-splitter event: a set-map S, lossless for the
    same measure, acting on two-coordinate states as a rotation-form
    gate with dialable input phase (c*sigma != 0, unnormalized).

Conclusion: f(x) = x^2 f(1) with f(1) > 0 - THE BORN RULE - and F
is complex-linear with orthonormal columns - UNITARY QUANTUM
MECHANICS.  Absent from the hypotheses: Hilbert space, amplitudes,
the power family, linearity, complex structure, continuity,
divisibility.  The assembly order matters: the splitter's phase
continuum forces the Born function FIRST (pass eight); the derived
measure is then l^2, so Mazur-Ulam yields linearity RETROACTIVELY;
gauge upgrades to C-linearity; the p = 2 machinery gives
orthonormal columns.  Everything the textbook assumes is here a
theorem.  This is the statement the uniqueness leg set out to earn.

## GENERAL TWO-OVERLAP COLUMNS (same pass, proof on paper - Lean
## formalization registered): Born-or-trivial beyond rotation form

Setting: a lossless C-linear step for monotone f with two columns
u, v of ARBITRARY complex entries sharing support.  Phase probes
give  sum_i g(A_i(psi)) = g(s^2) + g(t^2)  with
A_i = s^2 a_i + t^2 b_i + 2 s t sqrt(a_i b_i) cos(psi + theta_i)
(the amplitude sqrt(a_i b_i) is automatic).  Coordinates supporting
only one column contribute psi-independent terms absorbed by the
column normalizations.  For exactly TWO shared coordinates:

  (1) PHASE DICHOTOMY.  If theta_2 - theta_1 is not exactly pi,
      there is an arc of psi on which both cosines strictly
      decrease (co-phase included), so both g-arguments move down
      while the sum stays constant: monotonicity forces g constant
      on the swept intervals; scaling (s,t) sweeps scaled copies,
      overlap-chaining makes g constant on (0,infinity); the column
      normalization then forces g == 0 - excluded by
      nontriviality.  Hence ANTI-PHASE is forced.
  (2) ANTI-PHASE CASE.  With lambda := sqrt(a_2 b_2 / a_1 b_1),
      the combination lambda*A + B = (lambda a_1 + a_2) x
      + (lambda b_1 + b_2) y =: m is psi-independent.  On each
      level line m = const, the A-intervals overlap-chain exactly
      as in the rotation case, so g(x) + g(y) is constant along
      the line and equals its endpoint value: for all p, q >= 0,
          g(p) + g(q) = g(p + kappa*q),
      kappa = (lambda b_1 + b_2)/(lambda a_1 + a_2).  Setting
      p = 0: g(q) = g(kappa q) for all q, which for kappa != 1
      forces constancy on geometric ladders (trivial again); hence
      kappa = 1 and g is ADDITIVE: Born by monotone Cauchy.

So: any lossless step whose columns overlap in exactly two
coordinates forces Born or triviality - rotation form is NOT
needed.  Registered open: three or more shared coordinates with
phases outside a two-value (anti-phased) set - the multi-term
exchange F(u) = sum g(alpha_i + beta_i u) + sum g(gamma_i -
delta_i u) constant in u - and the Lean formalization of (1)-(2)
(a parameterized variant of `phase_interval_additivity`).

## THE POSTS PAIR IS ENTROPIC ALL THE WAY DOWN (same day)

posts_survival v2 instrumentation: (a) downset counts D_n are
essentially LAW-INDEPENDENT (both chains ~420 at n = 19, growth
~n^2.8-3.1); (b) top-creation is entropic for BOTH laws:
tau_n * D_n ~ const (1.17 classical - exactly uniform up to path
covariance; 1.7-1.9 quantum - the full downset gets ~1.8x the
uniform share); (c) SURVIVAL IS ENTROPIC TOO: the law-weighted
survival s_n matches the count fraction s_count (quantum 0.675 vs
0.666 at n = 19; classical identical by uniformity).  Hence the
entire bounce-suppression pair (~0.02 vs ~0.16) reduces to pure
IDEAL COMBINATORICS of the grown causets: quantum causets simply
have ~3x more post-avoiding ideals (their persistent ~3.1 minima),
and the law's weighting at fixed causet is irrelevant.  The
analytic remainder is a single question: the asymptotics of the
fraction of ideals containing a maximal-above element, for the two
causet ensembles.

## THE DERIVATION SWEEP (2026-08-15, tenth pass): six consequences
## of the terminal theorem

1. MEASURE HOMOGENIZATION [Lean: `master_chaining`, §25].  Two
   sectors carrying arbitrary monotone measure functions g1, g2,
   tied by one interference exchange (physical normalization
   P+Q=1), are forced EQUAL and jointly linear - a common Born
   function.  Not just the same exponent (old no-hybrid) - the same
   FUNCTION, from arbitrary monotone pairs.  Proof: the ladder gives
   the increment law g2(s+m)=g2(s)+g1(m) (m<=s), so g1 is additive
   hence linear; the x=0 probe g1(Px)+g2(Qx)=g1(x) then pins g2 to
   g1's slope with no residual constant (this is where P+Q=1 is
   used).  Physics: a single gravitationally-induced interference
   event (BMV) would force gravity into matter's Born calculus -
   measure-dualism cannot survive one interference event.

2. MASTER CHAINING THEOREM [Lean: `master_chaining`].  The single
   parameterized statement of which section-23 (g1=g2), the two-
   overlap case, and homogenization are all instances.

3. INTERFERENCE EXISTS FROM TIME ALONE [proof on paper].  The
   structure/frozen-measure argument is measure-agnostic: for any
   nontrivial monotone f, a lossless step with pairwise-disjoint
   column supports is a permutation IN MEASURE, hence frozen, hence
   measure-static under divisibility (the n!-Lagrange argument of
   §11-12 uses only the permutation structure, not p=2).
   Contrapositive: monotone measure + divisible lossless time +
   change  ==>  some step has overlapping columns, i.e. INTERFERENCE
   IS DERIVED TO EXIST, not assumed.  Chained with the two-overlap
   Born-or-trivial result: if that mixing overlaps in two
   coordinates (generic), Born follows - the monotone-measure
   divisible-time capstone, with >=3-overlap the sole delimiter.
   (Formalization registered: needs the monotone-f frozen-measure
   theorem, a monotone twin of `real_lossless_frozen_measure`.)

4. ANY-ANGLE STABILITY [proof on paper].  Section 22's approximate-
   Born bound covered only the balanced splitter.  The section-23
   ladder propagates a delta-lossless defect additively over its
   ~1/mu* steps, so a delta-lossless splitter of ANY angle pins f
   within C(c,sigma)*delta of Born, with C = O(1/mu*) =
   O((c^2+sigma^2)^2/(c^2 sigma^2)) - the experimental inequality
   for arbitrary interferometers.  (Formalization registered: a
   Hyers-style version of `phase_interval_additivity`.)

5. THE POSTS FORMULA [numerical, posts_formula.py]: reading (ii).
   The tested factorization s_count = N_below/N_total FAILS; instead
   per-post survival tracks s_naive = (n-1-depth)/(n-1), the
   fraction of strictly-later elements - to ~1% for BOTH chains.  So
   survival is GEOMETRIC IN DEPTH, not an ideal-count ratio: the
   bounce-suppression pair reduces to the DEPTH DISTRIBUTION of
   posts (quantum posts sit deeper -> smaller survival), not to
   ideal combinatorics.  Honest revision of front-5's hypothesis;
   the analytic remainder is now the mean post-depth asymptotics of
   the two ensembles.

6. PAPER P1 SPINE [PAPER_P1_SPINE.md]: the terminal theorem as the
   paper's centerpiece; theorem-to-section map fixed; two assembly
   routes (beam-splitter §24 and divisible-time §11-17) both
   reported; prior-art sweep and honest-scope sections drafted.

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
