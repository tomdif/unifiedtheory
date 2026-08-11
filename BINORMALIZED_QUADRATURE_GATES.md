# The two gates of the bi-normalized theory: phase quantization at
# pi/4, and the interference-bounded fact regression (2026-08-11)

After BORN_RECORDS_TEST.md resolved the fact crisis, two gates stood
between the bi-normalized law and physics: (1) does the quantum sector
(the rho e^{iS phi} action-phase structure) survive bi-normalization,
and (2) what observable separates the partially coherent theory
(lambda < 1) from a fully dephased one.  Both were attacked with
pre-registered readings (docstrings of binormalized_phase_diagram.py /
lambda_observable.py, filed before the runs).

## Gate 1: the quantum sector survives — and the phase is QUANTIZED

Sharp form: an ACTION-PHASED bi-normalized law assigns per parent
b_c = rho_c e^{i g_c phi} (rho >= 0, g = integer action gap) with
  sum_c mu_c rho_c e^{i g_c phi} = 1   and   sum_c mu_c rho_c^2 = 1.
This keeps the wave family's amplitude structure (real weight times
action phase) inside the double-conservation law; covariance = weights
depend only on the (parent, child) classes.

RESULT (hand derivation + Lean + scan, binormalized_phase_diagram.log):

1. THE ROOT QUANTIZES THE PHASE.  The physical root (children 2-chain
   and 2-antichain at gaps -1, +1) forces Im: rho1 = rho2, Re:
   2 rho cos phi = 1, Born: 2 rho^2 = 1, hence
       cos phi = sqrt2/2,  rho = sqrt2/2,  phi = pi/4  exactly
   (Lean: root_phase_quantization, root_phase_is_pi_div_four,
   axiom-clean; support-dropping at the root is excluded — either
   child alone forces phi = 0 mod 2pi).  In the coherent-only wave
   family the root merely set the scale 1/(2 cos phi) and phi was a
   free parameter with feasibility windows; the Born half of double
   conservation collapses the window to a POINT.  The two solutions
   +-pi/4 are conjugates — the residual freedom is exactly the
   orientation/arrow Z2.  Note 2 phi = pi/2: the root's branching sits
   exactly at the quadrature condition Delta(S phi) in (Z+1/2) pi that
   `unitarity_quantizes` (KFCausalQuantumMeasure) derived
   independently in the coherent theory.

2. AT pi/4 THE WHOLE TREE IS FEASIBLE.  Scan of all 405 parents
   (n <= 6) over 154 phases: the root is feasible ONLY at pi/4, and
   there ALL 405/405 parents are simultaneously feasible; the
   forbidden-parent closure converges with ZERO exclusions.  An
   explicit law was constructed (QP-argmin-to-vertex bisection per
   parent): double conservation exact to 2e-15, support per level
   {1,2,4,7,15,30,68} — a thin subtree (support is
   construction-dependent; existence at every parent is the invariant
   statement).  Hand-exact anchors: the 2-antichain parent solves in
   Z[sqrt2] with all rho > 0 — gaps (+1,-1,-3), multiplicities
   (1,2,1), rho = ((2+sqrt2)/4, sqrt2/4, (2-sqrt2)/4); the 2-chain
   parent is feasible only with the 3-chain child at weight ZERO —
   support restriction emerges from the Born constraint, echoing the
   hereditary-real structure.

3. RECORDS TEST ON THE pi/4 LAW: X_minus(P) = 0.0000 exactly,
   X_minus(Q) = 0.070, interference retained (max|Q-P| = 0.27).  The
   action-phased bi-normalized theory at its unique phase has stable
   facts and live interference simultaneously.

VERDICT: reading (i), strengthened.  The quantum sector survives
completion #3, and survives RIGIDLY: the phase parameter of the wave
family is not transferred but DERIVED — double conservation + action
phases + the physical root force the Born-quadrature phase pi/4 up to
the arrow mirror.  What the old program scanned as a free coupling,
the new theory pins.

## Gate 2: the lambda-observable — regression bounded by interference

THEOREM (fact_regression_interference_bound +
eventMass_fact_regression_bound, axiom-clean): for
M_lambda = (1-lambda) Q + lambda P with P the Born-diagonal martingale
channel, any monotone record's step regression obeys
    M_{T+1} - M_T  >=  -(1-lambda) (|I_T| + |I_{T+1}|),
I_T = Q_T - P_T the record's own interference.  At lambda = 1 the
right side vanishes (facts exactly stable — recovers the records
theorem); at lambda < 1 the theory PREDICTS record-probability
regressions, bounded linearly by (1-lambda) times measurable
interference.  Standard decoherence-based quantum mechanics predicts
ZERO record regression.  This is the falsifiable separation:

  - measure a record regression EXCEEDING (1-lambda)(|I_T|+|I_{T+1}|)
    => the bi-normalized law is falsified at that lambda; exceeding it
    for all lambda (including the lambda = 1 bound of zero... i.e. any
    regression with zero interference) falsifies the whole family;
  - measure ZERO regression at nonzero interference => consistent with
    lambda = 1 (fully dephased records) or with the bound being slack.

MEASURED (lambda_observable.log, from the three logged laws):
  - bound violations: 0 everywhere (implementation check of the
    theorem);
  - tightness up to 0.83 (maxmin-completed d7) — the bound binds, it
    is not slack bookkeeping;
  - worst single-record regression per growth step at lambda = 0:
    0.037-0.048 across laws and depths, scaling linearly to zero in
    (1-lambda) (0.0476 -> 0.0301 -> 0.0127 -> 0.0023 -> 0);
  - per-step X_minus(Q) by depth: d7 steps (0.006, 0.076); d8 steps
    (0.025, 0.069, 0.041) — fluctuating at the few-percent level, NO
    compounding trend at accessible depth (and bounded by the
    interference bound regardless).

## Honest scope

- The pi/4 scan is floating-point (tolerance 1e-7); the root
  quantization and depth-2 anchors are exact (Lean / Z[sqrt2]).  An
  exact Z[zeta8] certificate for all 405 parents is the natural
  hardening (the program's queued "exact zeta8 gate" now has a target
  worth the effort).
- Feasibility at every parent does not select ONE law: rho choices
  remain per parent (the constructed law is one member of the pi/4
  family).  What is unique is the PHASE.  Selection among pi/4 laws
  (e.g. maximal support, entropy, or a variational rule) is open.
- The lambda parameter itself remains physically uninterpreted (the
  transfer audit's "not yet a laboratory-time collapse law"); the
  gate-2 bound is what makes it measurable in principle.
- Depth 7 for the scan (405 parents); the records test on the pi/4 law
  is depth 7.  Depth-8 confirmation of the pi/4 feasibility sweep is a
  computation away.
- The old wave family's OTHER structures (funding certificates, aging,
  necessity) still await recomputation inside the pi/4 family — but
  the reason to recompute them just changed: there is now exactly ONE
  phase to check, not a window to scan.

## Registered follow-ups

1. Exact Z[zeta8] feasibility certificates at pi/4 (all parents).
2. Selection within the pi/4 family (support-maximal / variational).
3. Depth-8+ pi/4 sweep; aging/necessity analogues inside the pi/4
   family at the pinned phase.
4. Physical interpretation program for lambda (record-dephasing
   strength): what system instantiates the record algebra, and what
   does (1-lambda) x interference evaluate to there.
