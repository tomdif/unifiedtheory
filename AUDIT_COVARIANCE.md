# Covariance / Bell-causality audit of the pi/4 dynamics
# (2026-08-16; the gate for the quantum-CSG claim)

## Verdict in one line

The pi/4 double-conservation dynamics does NOT satisfy the strict
Rideout-Sorkin conditions - and provably CANNOT: strict covariance
is a machine-checked no-go for the entire action-phased class, and
the maxent member violates classical-form Bell causality maximally.
The audit converts the tier-2 claim ("candidate solution of the
quantum-CSG problem") into a sharper contribution: THE RS TEMPLATE
ITSELF IS THE OBSTRUCTION - quantum bi-normalized growth requires
covariance at the class/decoherence level, exactly where its phases
already live.

## 1. Strict covariance: NO-GO (Lean, section 32)

Strict covariance = equal amplitude products along all growth paths
to isomorphic labeled causets = amplitudes of node-weight-ratio
form a = (W(child)/W(parent)) e^{i phi gap}.  Double conservation
then becomes a global system on unlabeled causets.  Levels 1-2
solve exactly (W(A2) = W(C2) = sqrt2/2 - the root pi/4 miracle
again).  Level 3 is contradictory in its LINEAR part alone: the
chain parent forces W(2-chain + point) = 1/2, the antichain parent
forces 1/4.  No Born constraint or positivity needed.  Numerics
confirm (200 restarts, signs free: min residual^2 = 0.05 > 0).
Machine-checked: `covariance_no_go`.  Phases, by contrast, are
EXACTLY covariant (growthAction_iso_invariant): the obstruction is
purely in the magnitudes.

Consequences: (a) Gudder's restriction to uniquely-labelable
c-causets is now explained as NECESSARY, not merely convenient -
on the full tree, per-path covariance is impossible; (b) any
bi-normalized quantum growth must define its measure at the
path-sum (class-amplitude) level - which this program's record/
class machinery already does, and where the phase part is already
label-invariant; (c) the WITHDRAWN claim: this dynamics does not
solve the quantum-CSG problem in RS form - the new claim: NOTHING
in this class can, and the no-go says where covariance must move.

## 2. Bell causality (classical form): MAXIMALLY violated by maxent

Spectator test: 2-chain parent, children with pasts {}, {a}, {a,b}.
The law FORBIDS the 3-chain cap outright (P(past {a,b}) = 0 - a
deterministic interference block: "no third domino").  Adding one
causally DISCONNECTED spectator element resurrects it to 0.0556.
Ratios of unrelated-child probabilities: 1.0000 both ways for
{} vs {a} (Bell causality holds there), but infinity -> 4.0 for
pairs involving the blocked child.  Mechanism: the maxent law is a
global per-parent optimization over the whole gap spectrum;
spectators enrich the spectrum's octant coverage and re-open
blocked channels.  Classical-form Bell causality is violated in
the strongest possible way (zero <-> nonzero).

Registered: assessment against the QUANTUM Bell-causality
proposals (Zalel; Dowker et al.), which are formulated on
decoherence functionals precisely because amplitude-level locality
is too strong for quantum dynamics.  The class-level phases and
record structure are the natural objects for that test.

## 3. Status of the field-problem claim after the audit

  - Solved in RS strict form: NO (provably impossible for the class).
  - New contribution: the no-go theorem + the relocation principle
    (covariance lives at class level; phases already comply).
  - Open gate for a positive claim: formulate the class-level
    (decoherence-functional) covariance + quantum Bell causality
    conditions and test the pi/4 class measure against them.

## PART 2 (same day): class-level covariance PASSES; quantum Bell
## causality is a SECOND magnitude-sector no-go (Lean sec. 33)

CLASS-LEVEL COVARIANCE - the positive half, verified exactly:
  (1) Within-class phase alignment: all labeled representatives of
      each unlabeled class carry the same phase (63/63 classes at
      depth 5; engine = growthAction_iso_invariant): the class
      amplitude is well-defined and relabeling interference is
      never destructive.
  (2) Coherent propagation: the total stem amplitude is exactly
      conserved (sum of class amplitudes = 1 at depths 4 and 5) -
      the Gudder-2.5-style consistency of the class decoherence
      functional, inherited from per-parent coherent sums.
  The class quantum measure mu(C) = |A(C)|^2 is well-defined,
  label-invariant, and consistent.  (Between-class interference is
  large and constructive: total mu = 6.44 at depth 5 - quantum
  measures are not additive; noted, not a defect.)

QUANTUM BELL CAUSALITY (fixed-slot form: D(., S) obeys the
classical ratio condition; with the rank-1 level decoherence
functional this reduces to spectator-independence of complex
amplitude ratios):
  - PHASE PARTS: hold EXACTLY (gap differences are spectator-
    independent - a disjoint spectator changes no k_y in either
    past).
  - MAGNITUDE PARTS: NO-GO (Lean, `bell_causality_no_go`).  At the
    2-antichain parent, the Bell ratios (via the 1-point parent)
    force the three +-1-gap magnitudes equal; the coherent
    imaginary part then forces v3 = -v1; nonnegativity kills it
    immediately, and even with signs free Born normalization fails
    (4 v1^2 = 1/2 != 1).  The chain parent, by contrast, is
    exactly Bell-causal at (sqrt2/2, sqrt2/2, 0) - the maxent
    member's own values.

## FINAL AUDIT VERDICT

Action-phased double conservation:
  - satisfies EVERY phase-level covariance and causality condition
    exactly (class phases label-invariant; phase ratios spectator-
    independent; class measure well-defined and consistent);
  - PROVABLY cannot satisfy either RS-form condition in the
    magnitude sector (two machine-checked no-gos, sections 32-33).
The quantum-CSG problem in Rideout-Sorkin form is UNSOLVABLE in
this class.  The audit's positive content: the phase/interference
sector of the pi/4 dynamics is fully covariant and causal; all
obstructions are classical-probability-sector artifacts of
transplanting RS conditions to amplitudes.  A correctly-stated
quantum problem should impose its conditions where the physics
lives - on the class decoherence functional - and there the pi/4
measure passes every test we can currently formulate.
