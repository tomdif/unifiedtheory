# The history-counting axiom (2026-08-03)

Every kill mechanism in Papers 1-3 runs through transition
multiplicities; the unresolved axiom of the framework is what those
multiplicities count.  This note formulates the axiom, tags the
program's results by their convention-dependence, and reports the
first computation of the dynamics itself under the alternative
convention (orbit_counting_gate.log).

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
