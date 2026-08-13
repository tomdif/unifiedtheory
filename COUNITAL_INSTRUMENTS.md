# Coherent-counital instruments: the double-conservation channel class
# as a quantum-information primitive (2026-08-13)

OBJECT.  A quantum instrument {K_c} satisfying BOTH
    sum_c K_c = I            (coherent counitality)
    sum_c K_c^dag K_c = I    (trace preservation / Born completeness)
- the operator double-conservation law of the bi-normalized growth
program (KFCausalDoubleConservationLaw; recorded-refinement dilation
V = stack(K_c), V^dag V = I, EV = I with E the codiagonal).

WHY IT IS A PRIMITIVE.  This is a measurement that (i) writes a
genuine record (CPTP instrument, outcomes with Born weights), and
(ii) whose COHERENT SUM is the identity: feeding back all branches
coherently recovers the input exactly - "measurement whose average is
doing nothing", the defining aspiration of QND design, here as an
algebraic class rather than an engineered approximation.  The record
martingale theorem gives the operational payoff: monotone record
events have horizon-invariant probabilities - records that never
degrade while system coherence persists.

CHARACTERIZATION (finite dim, sketch).
 1. Dilation form: {K_c} is coherent-counital iff the isometry
    V : H -> H (x) C^m, V = sum_c K_c (x) |c>, satisfies E V = I for
    the counit E = I (x) <u| with u = sum_c |c> (unnormalized).
    Extending V to a unitary U on H (x) C^m: the class corresponds to
    unitaries whose compression to the "flat-record" sector is the
    identity - equivalently, quantum walks on the record register
    that PRESERVE THE FLAT STATE |u>/sqrt(m) jointly with any system
    state, in the sense <u| U |u-column> = I_H.
 2. Scalar case (per-branch amplitudes a_c): the set {sum a = 1,
    sum |a|^2 = 1} is the intersection of a complex hyperplane with
    the unit sphere - a (2m-3)-sphere's worth of laws per branching;
    nonempty for all m >= 1; for m = 2 exactly the circle
    a = (cos t e^{i t'}, ...) with the quadrature constraint (the
    pi/4 quantization of the growth program is the action-phased
    section of this set).
 3. Contrast classes: unital channels (sum K I K^dag = I) and
    unistochastic matrices (|U_ij|^2 bistochastic) each impose ONE of
    the two conditions after squaring; coherent-counitality imposes
    the LINEAR sum condition alongside - strictly stronger than
    unistochasticity of the induced stochastic matrix (which follows:
    rows sum to 1 by trace preservation, columns relate through the
    counit).

OPEN QUESTIONS WORTH A QUANTUM-INFORMATION PAPER:
 A. Full characterization of coherent-counital instrument families on
    C^d for d > 1 (beyond the sharp native resolution K_c = |c><c|
    which the growth program proved unique under locality).
 B. Capacity/disturbance tradeoffs: these instruments extract record
    information with zero coherent-average disturbance - where do
    they sit against information-disturbance bounds (Fuchs-Peres)?
 C. Sampling complexity: growth of flat-preserving quantum walks on
    ideal lattices is EXACTLY classically simulable here (the
    ideal-lattice sampler) because phases telescope; for which
    non-action-phased counital walks does simulability break?  A
    candidate boundary family for quantum-advantage sampling.
 D. Fault tolerance: do coherent-counital record registers give
    decoherence-free record subsystems for free (the record-algebra
    protection of the growth program, ported to circuits)?

STATUS: theory-note grade; A-D are each concrete enough to attempt.
