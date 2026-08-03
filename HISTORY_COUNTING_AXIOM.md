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

## Results (depth 7, sharp 2D and the eps=1/4 resonance)

  generic phases (0.90, pi/3):  FULL support under O, as under L -
      quantum abundance is convention-robust.
  resonance eps=1/4, phi=8pi:  support 1081 == hereditary-real,
      IDENTICAL to L.  Explained, not observed: the Necessity
      Theorem's three moves use only mu > 0, so the resonant sector
      is invariant under ANY positive multiplicity convention.  The
      exactly solved sector is axiom-independent.
  phi = pi/4 (Born quadrature):  DEAD under L (the mu=2 certificate);
      ALIVE under O with partial support 653/2450
      (1,2,5,11,32,109,493 by level) - a new object, neither dead nor
      full, existing only in the orbit theory.

## What this establishes

1. L and O are PHYSICALLY INEQUIVALENT theories, distinguishable
   within the framework by their dead-phase spectra.  The axiom is
   not bookkeeping.
2. The axiom's content is LOCALIZED at exactly the anomalous phases -
   the quadrature point where the probability-from-action reading is
   most literal - and vanishes at resonances.  The textbook-quantum
   phases are the convention-sensitive ones.
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
