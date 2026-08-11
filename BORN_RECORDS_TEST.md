# Completion attempt #3, first records test: the bi-normalized law
# PASSES — facts accrete, never un-happen (2026-08-11)

## What was registered and why

The records test (records-churn-2026-08-03) closed the last arc
negative: stem-event measures churned under the coherent sum(a)=1 wave
family, and SUM_RULE_MOD.md measured that ~86% of the churn was
NORMALIZATION FLOW, retiring all dephasing-style completions.  The
registered next theory (SUM_RULE_MOD verdict; built out in Lean on
08-04/05 as the double-conservation law) was the BI-NORMALIZED growth
law: sum(a) = 1 AND sum|a|^2 = 1 at every parent.  The transfer audit
proved cylinder projectivity for it by theorem but explicitly declined
(open item 3) to claim anything about stem/record events.  That is the
question tested here, with readings registered in born_records_test.py
before the run:

  (i)   X_minus(P) ~ 0 and X_minus(Q) < 0.2 (the measured coherence
        share of the old churn): facts stabilize under the new rule.
  (ii)  X_minus(Q) >= 0.2: facts live only at lambda = 1.
  (iii) Born-shell obstruction on >5% of support parents.

## The sharpened metric (this unit's reframing)

The old churn X = sum_stems sum_T |s_{T+1} - s_T| conflates two things
a martingale lens separates:

  X_minus = sum max(0, s_T - s_{T+1})  -- facts UN-HAPPENING
            (Kolmogorov inconsistency; forbidden for monotone events
            under any Born-complete law, by theorem)
  X_plus  = sum max(0, s_{T+1} - s_T)  -- monotone ACCRETION
            (new histories coming to contain the stem: learning,
            not inconsistency)

The old verdict's physical content was X_minus (s3: 0.963 -> 0.941 ->
0.548 is pure un-happening).  X_plus is not a pathology.

## The construction

Same engine as the records test (unlabeled causet growth tree,
phi = 0.9, W2 = {0:2, 1:-4, 2:2}).  For a wave-family member A, each
parent's labeled relative child amplitudes a_c = e^{i g phi} A_c / A_p
(sum_labeled a = 1 exact) are radially completed onto the Born shell:
b = u + r(a - u), u = 1/K uniform, r fixed by sum_labeled |b|^2 = 1 —
the support-relative least-disturbance rule of
KFCausalBornShellGeneralLaw.lean, applied at every parent of the
physical tree.  Measures by tree DP: coherent Q (final-class
identified), Born diagonal P, and the audit's interpolation
M_lambda = (1-lambda) Q + lambda P.

## Certification of the pipeline

deep member baseline replicates completion_p4_test.log EXACTLY
(X = 1.2203).  The maxmin LP is degenerate: this run's maxmin vertex
differs from the original records-test member (X = 3.26 vs 3.04 at
depth 7; same t* = 0.8044, same scale, same qualitative table) — noted,
and immaterial: both members give the same verdict below.

## Results (born_records_test.log depth 7; born_records_test_d8.log
## depth 8, T = 7 interior — the registered depth-8 follow-up)

Depth 8, churn over T = 5..8 (three horizon steps, all interior):

  member           X        X_minus   X_plus
  old law maxmin   6.4141   2.0810    4.3331
  old law deep     1.6672   0.0866    1.5806
  Q  (maxmin-c)    1.2486   0.1353    1.1132
  Q  (deep-c)      1.6951   0.1082    1.5869
  P  (maxmin-c)    0.6707   0.0000    0.6707
  P  (deep-c)      1.0641   0.0000    1.0641
  M_0.25 / 0.5 / 0.75 (maxmin-c): X_minus = 0.0837 / 0.0417 / 0.0105

  Born-shell obstructions: 0 of 2450 parents (maxmin, FULL support —
  t* = 0.804 > 0, so every parent is completed; reading (iii) is dead:
  the bi-normalized intersection is realized on the ENTIRE physical
  tree at generic phase).

  P(Omega) = 1.000000000000 at every T (maxmin-c; theorem check).

  Past-sector record (stage-4 action sectors), P, maxmin-c: the seven
  sector masses are IDENTICAL TO SIX DECIMALS at T = 4,5,6,7,8.
  The old law's purity corollary ("the universe forgets its own action
  sector", 1.00 -> 0.61) becomes: the past's sector probabilities are
  horizon-invariant exactly; residual purity < 1 is classical mixing
  of the conditional (final-class given sector), not measure
  inconsistency.

  Interference retention: max |Q - P| on stems = 0.30 (maxmin-c),
  0.42 (deep-c) — the completed theory still interferes at lambda < 1;
  M_lambda retains it by the exact factor (1 - lambda).

  Example stems under P (maxmin-c, T = 4..8), monotone and visibly
  stabilizing:
    s0: 0.4156  0.4777  0.4933  0.4993  0.5076
    s3: 0.4572  0.5060  0.5386  0.5430  0.5463

VERDICT: reading (i) at both depths.  X_minus(P) = 0 exactly (both
members, both depths); X_minus(Q) = 0.07-0.08 (depth 7), 0.11-0.14
(depth 8) — below the registered 0.2 threshold; facts stabilize.

## The theorem half (KFCausalBornRecordMartingale.lean, axiom-clean)

The numerical X_minus(P) = 0 is not an observation, it is a theorem,
now formalized (zero sorry, axioms = propext/Classical.choice/
Quot.sound):

  record_transport      Born completeness => the refined measure of the
                        exact lift of ANY past event equals the past
                        event's measure (horizon-invariant facts; total
                        mass conserved — normalization flow is dead
                        identically, not just numerically).
  record_accretion      monotone events (stems: a stem of the parent
                        history is a stem of every child history) can
                        only GAIN measure — facts never un-happen.
  record_measure_converges   bounded monotone record sequences
                        converge: stem probabilities stabilize.
  coherent_record_regression  the CONVERSE witness: a two-stage law
                        with sum(a) = 1 at every parent (amplitudes
                        2, -1 then 1 and 2, -1) whose monotone record
                        falls 4/5 -> 4/9.  Fact-unhappening requires
                        no interference between records: the coherent
                        diagonal spoils itself exactly when
                        sum|a|^2 != 1.
  fact_stability_dichotomy    the packaged pair.

This closes the finite-depth record half of transfer-audit open item 3:
within any finite horizon, records are martingale-stable under the
bi-normalized rule and only under it (the coherent rule has an explicit
regression witness).  The infinite-tail/DJS-boundary half remains open.

## What this changes

1. The fact crisis is RESOLVED IN THE STATED DIRECTION by the sum-rule
   modification the program itself registered: the un-happening of
   facts was entirely the Born defect of the coherent rule.  "Not even
   the recorded moon has a stable probability" was a property of
   sum(a)=1, not of covariant growth.
2. The moon statement now has three grades: cylinder facts have
   horizon-INVARIANT probabilities (theorem); stem records are
   monotone-convergent (theorem + measured); the coherent channel's
   residual inconsistency is small (0.08-0.14) and tunable to zero by
   record dephasing (X_minus(M_lambda) -> 0 as lambda -> 1) WITHOUT
   killing interference at lambda < 1.
3. Anti-decoherence is untouched: class-identified Q(Omega) still
   grows (1 -> 55 by T = 8).  The bi-normalized theory does not
   decohere the coherent channel — it makes records stable DESPITE
   coherence.  Records and interference are now cleanly separated
   instead of mutually destructive.
4. The Born-shell completion is realized with ZERO obstructions on the
   full physical tree — the bi-normalized intersection is not thin
   (its uniform-boundary obstruction never occurs at generic phase).

## Honest scope

- Member identity: the original maxmin vertex was not reproducible
  (degenerate LP); certification rests on the exact deep-member match
  and member-robustness of the verdict.
- The completed law is a DIFFERENT THEORY from the wave family (the
  transfer audit's "second theory"): Born-shell rescales zero-sum
  fluctuations by r with median 0.18-0.23 (quartiles ~0.11-0.52) — not
  a small perturbation of the member.  Which theorems of the coherent
  program survive it is the transfer ledger's still-owed recomputation
  (funding, hbar windows, aging, necessity).
- X_minus(Q) is small but NONZERO and grew 0.08 -> 0.13 from depth 7
  to 8; no claim that it vanishes with depth.  The theorem-backed
  claims are the P channel and the (1-lambda) suppression.
- deep-member run leaks mass (P(Omega) -> 0.967 by T = 8) because
  parents below amplitude 1e-7 are skipped; the full-support maxmin
  run is the clean certificate (P(Omega) = 1 to 12 digits).
- Labeled counting only; the orbit-counting re-measure is registered
  as a follow-up (the history-identity axiom is untouched by
  normalization — audit open item 5).
- Nothing here selects the bi-normalized law microscopically (audit
  open item 1) — this unit shows the law WORKS, not that causal order
  forces it.

## Registered follow-ups

1. Orbit-counting stems under the completed law.
2. Depth-9+ trend of X_minus(Q) (is the coherent floor bounded?).
3. Transfer recomputation: hbar windows / funding under bi-normalized
   equations (does a phase window survive?).
4. Tail events / DJS boundary: promote finite-horizon martingale
   stability to a sigma-additive extension statement.

## Addendum: the double-norm question resolved (same session)

The dangling double_norm_probe.log (08-03, one line, script lost,
"rms 9.167e-04, support 65/87") asked whether the wave family CONTAINS
a bi-normalized member — i.e., whether completion #3 is secretly a
SELECTION principle inside the old theory.  Resolved NEGATIVE with a
sharp formulation (double_norm_resolve.py): parameterize the EXACTLY
coherent nonnegative family (null space of the 49-rank linear system,
38 dims) and minimize the normalized Born defect
(sum_c mu A_c^2 - A_p^2)/(A_p^2 + 1e-4) over it, penalty-escalated
multistart (LP members, zero, 3 scales of random; every start converges
to the same basin).  MINIMUM = 2.146 (raw 2.547), worst parent defect
10.05, optimal support 66-67/87 at levels {1,2,4:12,5:~48}.  The
defect floor is ORDER UNITY, not a near-miss: no bi-normalized member
exists in the depth-5 wave family; the phases must move (as Born-shell
completion moves them).  The bi-normalized law is structurally a SECOND
theory — the transfer audit's "defines a second theory" is now a
quantified geometric separation, and the old probe's 9.2e-4 (whatever
residual it measured; its script is lost) cannot be this object.  Its
support pattern 65/87, however, matches the optimum found here.
