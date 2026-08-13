# Six-direction outside-the-box sweep: verdicts (2026-08-13)

## (6) TRACY-WIDOM: the quantized law is in the KPZ/GUE class - HIT

Height distribution at n = 28, 1200 paths, 2D pi/4 Born chain
(arrow_tw_sampler.log):
    skew = +0.2573 +- 0.071:  z vs TW-GUE (0.2241) = +0.47  ==>
    CONSISTENT WITH TRACY-WIDOM;  z vs Gaussian = +3.64  ==>
    GAUSSIAN EXCLUDED at 3.6 sigma;  ex-kurt +0.04 (TW 0.09, direction
    right, weak).
THE TWIST: the CLASSICAL uniform chain is NOT TW (skew +0.648 +- 0.14,
3 sigma above TW) - quantization RESTORES the KPZ universality class
that classical uniform growth breaks.  Interpretation: the Born
channel's path aggregation reinstates the extremal-path statistics of
the LIS/last-passage family.  Since TW-GUE is the distribution family
conjectured (Montgomery-Odlyzko) to govern Riemann-zero statistics,
the quantum-measure arc and the repo's RH arc now share a
universality class at the level of measured fluctuation statistics.
Hardening path: larger n + full-density KS test vs TW; n = 28 skew
is one moment.

## (1) ARROW OF TIME: H-theorem reframing stands; entropy-minimization
##     is real but subtle

The proven monotones (record accretion, total coherent mass) ARE an
H-theorem - no environment, no coarse-graining ansatz; that reframing
costs nothing and is now on record.  The ideal-count entropy test:
quantum S/n starts ABOVE classical (0.517 vs 0.466 at n = 6), crosses
at n ~ 22-24, and at n = 28 sits BELOW: quantum 0.2658 (SE 0.0005) <
classical 0.2697 (SE 0.0010) < sprinkling 0.2799 (SE 0.0016) - a
small (1.5%) but ~3.5-sigma-by-SE ordering.  Registered reading
partially confirmed: the quantum law tends toward the SMALLEST causal
state-space entropy density at large n, with the crossing structure
as the honest caveat.  The strong claim (extremization) needs larger
n; the H-theorem claim needs nothing more.

## (2) LAMBDA HARDWARE PROTOCOL: validated, one run from a first bound

Sequential-record circuits (1 system + 5 record qubits); ideal
simulator confirms the QM martingale (eps_RR = 0.0035 ~ shot noise);
IBM-class noise gives 95% bound eps_RR < 0.014.  Circuits run
unchanged on IBMQ backends; a hardware run = first experimental bound
on the record-regression parameter.  (lambda_hw_protocol.py)

## (3) c = -2 THEOREM: sketch complete (TWO_ORDERS_C_MINUS_2.md) -
uniform 2-orders = independent coordinate walks = correlation-0
mating = gamma = sqrt2, c = -2; rigorous route via Donsker /
bipolar orientations; short-note grade.

## (4) COHERENT-COUNITAL INSTRUMENTS: primitive named
(COUNITAL_INSTRUMENTS.md) - measurement whose coherent sum is
identity; flat-state-preserving-walk characterization sketch; four
concrete open problems (characterization, information-disturbance,
simulability boundary, record subsystems).

## (5) ENSEMBLE OVERLAP METRIC: validated on real data (vol_cascade)
Broad-support rare-event calls hit 35.3% vs herded 16.0% out of
sample (base rate 7.4%), corr(N_eff, outcome) = +0.28: the
Lean-proven participation bounds work as a tail-herding detector.

## Ranked outcomes
1. TW/GUE class membership (new result, RH-arc contact, hardening path clear)
2. Overlap metric (immediately useful, validated)
3. Lambda protocol (experiment-ready)
4. H-theorem reframing + entropy ordering (conceptual + suggestive data)
5. c=-2 note and counital primitive (write-up-ready seeds)
