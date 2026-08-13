# Prior-art sweep for Paper 1 (fact stability selects Born-normalized
# growth) — 2026-08-13

## The novelty claim, checked

Claim: the DOUBLE-CONSERVATION growth law (sum a = 1 AND sum |a|^2 = 1
per branching) and its selection by a record-stability postulate do
not appear in the prior literature.  Sweep result: SUPPORTED.  Nearest
neighbors and how to cite them:

1. **Complex Sequential Growth (Surya–Zalel, arXiv:2003.11311; also
   Zalel's covtree line, arXiv 2003.11311 / Dowker–Zalel).**  CSG =
   the classical measure complexified: transition amplitudes with the
   COHERENT sum rule only.  Their central problem is extension of the
   quantum measure to the full sigma algebra (bounded-variation /
   Caratheodory–Hahn–Kluvanek), because without extension covariant
   observables ("beables") are unmeasurable; complex percolation
   famously fails to extend.  POSITIONING: our fact-stability
   postulate attacks the same disease at the finite level (record
   probabilities that do not converge) and resolves it by CHANGING THE
   LAW rather than constraining couplings; the DJS/extension question
   reappears in our setting only for the residual coherent channel
   (our open item), while the Born-diagonal channel extends trivially
   (classical measure).  They explicitly name the "post event" (bounce
   beable) and cite stem-event formulations — both objects our
   theorems/numerics address directly.
2. **Sorkin quantal measure theory & preclusion; Dowker–Johnston–
   Sorkin ("Toward a fundamental theorem of quantal measure
   theory").**  Source of the stem-event/covariant-event machinery
   and the measure-extension theorem style.  Our record martingale is
   exactly a finite-horizon stability statement for their stem
   events.
3. **Martin–Sorkin complex percolation.**  The canonical coherent-only
   model whose pathologies (non-extension) motivate both lines.
4. **Barandes (stochastic–quantum correspondence; Born Representation
   / Unistochastic Theorems, arXiv:2309.03085, 2608.04354).**
   ADJACENT, not overlapping: unistochasticity is Born-completeness
   of a unitary's rows; Barandes never imposes the coherent row-sum
   and Born row-sum on the SAME transition data, and has no
   causal-set/growth contact.  Our double conservation is the
   simultaneous pair, equivalent (our KFCausalDoubleConservationLaw /
   RecordedRefinementDilation) to isometry + counitality of the
   recorded refinement — worth one comparison paragraph.
5. **Unitarity/isometry conditions in discrete quantum evolution
   (e.g., quantum cellular automata, staircase unitaries).**  The
   operator form sum K = I, sum K^dagger K = I resembles unital +
   isometric conditions; cite as context, no growth-law selection
   claim found.

## What the sweep did NOT find

- No prior bi-normalized/doubly-normalized sequential-growth proposal
  (search axes: "complex sequential growth" normalization; unistochastic
  causal sets; doubly stochastic amplitudes Born; quantum measure
  martingale records).
- No prior phase-quantization result of the form "Born completeness +
  coherent sum + action phases pins the phase" (our pi/4 theorem).
- No prior record-martingale/fact-stability selection postulate.

## Required citation block for P1 (minimum)

Rideout–Sorkin CSG; Sorkin quantum measure (grades/interference);
DJS fundamental theorem + stem events; Surya–Zalel CSG covariance
criterion; Zalel covtree review; Martin–Sorkin complex percolation;
Dowker–Surya observables; Benincasa–Dowker action (for the action-
phased family); Barandes unistochastic (adjacency); decoherent/
consistent histories (Griffiths, Gell-Mann–Hartle) for the
records-without-collapse contrast.

## Risk register (referee objections + our answers)

- "Phase telescoping is trivial."  Answer: individually yes; its role
  is enabling the accretion theorem and the phase-free covariant
  measure; stated as a lemma, not sold as deep.
- "Why double conservation?"  Answer: THE THEOREM — fact stability
  (no record regression) forces the Born half (dichotomy with explicit
  4/5 -> 4/9 witness); it is a selection result, not an assumption.
- "Toy engine, small n."  Answer: theorems are engine-independent
  (abstract refinement steps); numerics are pre-registered with
  committed logs and scoped claims.
- "Extension to sigma-algebra not addressed."  Answer: correct and
  stated; the Born channel is classical (extends by Kolmogorov); the
  coherent channel's DJS boundary is the named open problem.
