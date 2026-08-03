# The history-counting axiom (2026-08-03)

Every kill mechanism in Papers 1-3 runs through transition
multiplicities; the unresolved axiom of the framework is what those
multiplicities count.  This note formulates the axiom, tags the
program's results by their convention-dependence, and reports the
first computation of the dynamics itself under the alternative
convention (orbit_counting_gate.log).

## The positivity principle (thesis of this note, referee-proposed)

Call a kill certificate SIGN-PURE if it is a nonnegative combination
of equation components (in fixed rotated frames) whose surviving
terms all carry one strict sign, so the conclusion has the form "a
sum of nonnegative terms vanishes, hence each vanishes" (or "a
nonpositive sum equals 1").  Multiplicities enter every term as
positive factors, so replacing mu by any positive mu' preserves each
term's sign and the certificate verbatim:

  SIGN-PURE CONCLUSIONS ARE COUNTING-INVARIANT.

One-paragraph proof: a sign-pure certificate asserts
sum_i y_i mu_i (positive frame-component)_i A_i = c with y_i >= 0,
all summands of one sign, and c of the opposite sign or zero; the
map mu -> mu' > 0 multiplies each summand by mu'_i/mu_i > 0,
preserving signs, nonnegativity, and hence the contradiction or the
forced vanishing.  QED.  Conversely, INTERFERENCE structure -
feasibility of cancellations between terms of opposite sign or
different phase - depends on coefficient magnitudes, which the
counting convention rescales.

Instances, from the record: convention-invariant = the phi >= pi/2
dead zone (positive sum times cos phi = 1), Necessity Move 3 (single
term), the dust telescope (all-plus sum) - every invariance observed.
Convention-sensitive = the small-phi band, the quadrature dip, the
653-family - every difference observed.  BOUNDARY CASE marking the
principle's edge: the funding theorem's certificate is NOT sign-pure
(its middle coefficient is a difference of positives), so its
invariance is not automatic - and indeed the orbit version required
re-derivation (hand-check: middle coefficient becomes
sin(delta)sin(gamma-beta), positive again, but by recomputation, not
by the principle).  The principle therefore delimits exactly which
questions the history-counting axiom can ever touch: none in the
positive cone, all in the interference structure.

## The axiom space

A covariant growth dynamics requires a choice of what constitutes a
distinct history:
  L (labeled):  histories are labeled growth sequences; birth order
      is physical; mu(P->C) = #downsets of P yielding C.
      Maxwell-Boltzmann-style counting.
  O (orbit):    histories are unlabeled; birth order is gauge;
      mu'(P->C) = #Aut(P)-orbits of such downsets.  Gibbs-corrected,
      Bose-style counting of histories-as-configurations.
  E (event):    no per-path amplitudes; only the event algebra /
      decoherence functional is physical (measure-level covariance).
All prior gates ran the L dynamics (selection PRINCIPLES were tested
in L/O/E forms on top of it; the dynamics itself had never been run
in O until now).

## Results (depth 6-7, sharp 2D; both spectra measured)

Same 15-phase grid, both conventions (orbit_counting_gate.log,
orbit_pi4_extraction.log, labeled_grid.log):

    phi:        pi/8   pi/6   0.5    pi/4   pi/3  3pi/8 5pi/12  0.9   1.2   >=pi/2
    LABELED:    FULL   FULL   FULL   EMPTY  FULL  FULL  FULL    FULL  FULL  EMPTY
    ORBIT:      p:216  p:231  p:231  p:162  FULL  FULL  FULL    FULL  FULL  EMPTY

  - phi >= pi/2: BOTH empty, convention-independently (the root
    forces A(2ch) = A(2A) = 1/(2cos phi) under any positive counting
    - hand-checkable, mu-blind).  The honest map's "pi/4 is the
    unique dead phase" was always implicitly scoped to phi < pi/2.
  - mid-band (~pi/3 .. ~1.4): both FULL - the conventions agree.
  - SMALL phi: the conventions diverge on a BAND, not a point:
    labeled full, orbit PARTIAL (216/231/231 of 405 at depth 6).
    The earlier "generic-phase robustness" claim was a sampling
    artifact of two phases inside the agreement window - corrected.
  - pi/4: labeled EMPTY, orbit partial:162 - the labeled anomaly
    embeds in the orbit partial band as its MINIMUM (162 < 216, 231,
    231): a quadrature dip persists in the orbit theory, but as
    suppression, not death.
  - resonance eps=1/4 phi=8pi: IDENTICAL under both conventions
    (1081 == hereditary-real), explained by the Necessity Theorem's
    mu-blindness (see its convention-invariance corollary).
  - EXTRACTION (the taxonomy question): the 653-family (depth-7
    orbit-pi/4) is NOT carved by mod-8 congruences - element-jump
    residues span all odd classes (parity theorem) and downset-S
    residues span all of Z/8, so both candidate hereditary
    predicates are vacuous.  Partial support without (simple)
    congruence structure: a provisional FOURTH SECTOR, pending
    richer arithmetic.

## Referee checks (orbit_checks.log, 2026-08-03)

(a) CLOSURE: all four small-phi orbit families are downward closed
(the gate enforces it structurally; verified member-by-member).
Sectorhood is well-posed; the carving-invariant search is legitimate.

(b) SET IDENTITY: pi/6 and 0.5 give the IDENTICAL 231-member set (a
plateau - the support is locally constant in phi, not just its
size); pi/8's 216 is a strict SUBSET of it (nested).  But the
pi/4-family is set-DISTINCT (54-61 members in neither neighbor):
at least two lineages - a nested plateau family and a separate
quadrature family.

(c) ISOLATION: phi = 0.7854 (four decimals from pi/4, but not pi/4)
gives FULL support 405, as do 0.82, 0.87, 0.95, 1.00.  Exact pi/4
gives 162.  THE ORBIT-QUADRATURE FAMILY IS AN ISOLATED-POINT
PHENOMENON inside a locally-full neighborhood - structurally a
resonance (the referee's conjecture vindicated at the level of
phase-topology, even though mod-8 congruences do not carve it).
The dip framing is dead: it is not a minimum of a continuous
profile but an isolated special point, like every other exactly
solved object in this program.

UNVERIFIED AND QUARANTINED: phi = 0.70 and 0.75 returned supports
95 and 90 - non-monotone against the 231-plateau and the full
neighborhood, and unreplicated.  No reading is attached; the queued
integrity check (tightened tolerances, denser grid, exact-arithmetic
spot verification) decides whether these are tolerance artifacts of
near-degenerate cancellations or genuine landscape.  Pre-registered:
artifacts -> the band is plateau/transition/full with isolated
special points; real -> the orbit landscape is wilder than any
current description, and the description waits.

## What this establishes

1. L and O are STRUCTURALLY INEQUIVALENT theories: they differ at
   pi/4 (referee deflations adopted: "spectra" requires both dead
   sets and only the labeled one is measured - the orbit dead-phase
   scan is running; and nothing connects a dead phase to an
   observation - Paper 1's seam sentence applies verbatim).  The
   axiom is not bookkeeping.
2. LOCALIZATION IS DEAD (both-spectra measurement): the conventions
   diverge on the whole small-phi band, not at the quadrature point.
   THE BORING CHECK resolves partially: the labeled pi/4 DEATH was a
   counting artifact (alive under O), but a quadrature DIP survives
   in the orbit theory (162, the band minimum) - the two-anomaly
   question is now "one death artifact + one robust suppression."
   The entanglement framing is replaced by: the counting convention
   reshapes the small-phi phase diagram globally, and quadrature
   remains distinguished (as suppression) in both theories.
3. Convention-tagged ledger: Necessity Theorem, dust telescope
   (positivity-only), and the resonant webs: robust under any
   positive counting.  The pi/4 anomaly: an L-artifact.  The funding
   theorem: a preliminary hand-check suggests the orbit version
   survives with middle coefficient sin(delta)sin(gamma-beta)
   (product-to-sum identity) - full re-derivation queued.  The
   hbar-window law under O: untested, queued.
4. Any future selection principle must SPECIFY the convention, and
   the convention choice is itself the kind of physical postulate
   (a symmetrization postulate for histories) the selection crisis
   was pointing at.

## Queue

Characterize the 653-member orbit-quadrature family; orbit funding
theorem; orbit hbar-window scan; the E-convention dynamics
(decoherence-functional-level gate) - the last untested corner.
