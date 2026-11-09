# Twisted-lattice Yang–Mills program

Current frontier: **2026-11-09**. The program studies finite twisted SU(2)
lattices and the estimates needed for a large-volume continuum theory.
**The continuum theory, physical mass gap, and all twelve full-target
requirements remain open.**

## Current result and remaining inputs

[TwistedFluxInduction](TwistedFluxInduction.lean) turns specified transverse
and in-plane inequalities into an iteration and area-type decay statement.
Sufficient inputs for that version are the sector-thermal inequality **(S)** and a uniform
in-plane thermal bound **K-bar**, above an onset length `L0(beta)` and with
renormalization control. See [the band statement](../GAP_BAND_STATEMENT.md)
for the exact route, preregistrations, and numerical verdicts.

[TwistedFluxBasis](TwistedFluxBasis.lean) rewrites the transverse
step algebraically as `y(2t) = 2y/(1+y^2) * K0/Ke`, under its positivity
assumptions. [TwistedSubArea](TwistedSubArea.lean) handles a scale-dependent
log cost `m_j <= A + B q^j` for `0 <= q < 4`. Its area-decay conclusion needs
`u_0 > A/3 + B/(4-q)`. Proving those bounds for the lattice operators is still
required; an arbitrary `o(L^2)` bound alone is not what the theorem proves.

[TwistedSlabCriterion](TwistedSlabCriterion.lean) specializes the recurrence
to `q=2`. Its slab interpretation holds the transverse dimensions fixed;
the physical recurrence identification remains outside the formal theorem,
and the four-dimensional continuum limit does not follow.

[TwistedThermalExcess](TwistedThermalExcess.lean) adds these reductions:

| Declaration | Formal statement and boundary |
|---|---|
| `excess_antitone` | A finite sum of nonnegative-energy Boltzmann weights decreases when nonnegative time doubles. |
| `kper_sandwich` | `0 <= P2 <= P1` implies `1+P1 <= (1+P1)^2/(1+P2) <= (1+P1)^2`. |
| `k_le_two_kper` | The specified in-plane ratio is at most `2 Kper`, under its sign and twist-ratio assumptions. |
| `log_z_telescope` | An exact finite sum identity; convergence of an infinite trace expansion is separate. |
| `flux_projection_le` | A signed sum of nonnegative terms is bounded by the unsigned sum. |
| `kper_flux_split` | Given nonnegative `K0` and `0 <= a,b <= s`, the ratio lies between `K0/(1+s)` and `K0(1+s)^2`. |

Taking `s=7` yields the factors `1/8` and `64` for an eight-sector application.
The physical trace identification, sector positivity, and uniform bound must
still be supplied. These reductions are not a proof of the needed spectral
estimate.

## Numerical tests

The [November 8 transverse scan](../../../../data/yang_mills_twist_transverse_scan_2026_11_08.json)
uses a fixed `8^3` cross-section at beta 2.5 and 2.6. Registered test (16)
holds at the sampled sizes; (17) fails as written. Favorable central values
for the multiplicative step do not prove (S), K-bar, or uniformity in beta.

The [November 9 thermal-excess results](../../../../data/yang_mills_thermal_excess_2026_11_09.json)
give `1.25 ± 0.55` for beta 2.5, L=8: test (18) misses its `< 1.0`
central-value threshold by `0.46 sigma`. Test (19) fails because the L=4
values decrease from beta 2.6 to 3.0 by about `3.93 sigma` under independent
error propagation. The [probe script](../../../../scripts/yang_mills_thermal_excess.py)
then registered test (20). Its
[second batch](../../../../data/yang_mills_thermal_excess_2026_11_09b.json)
misses the beta 2.6, L=12 threshold: `2.78 ± 1.02` versus `< 1.0`.
The [higher-statistics follow-up](../../../../data/yang_mills_thermal_excess_2026_11_09c.json)
misses test (21)'s beta 2.6 threshold on its central value: `1.40 ± 0.58`
versus `< 1.0`, about `0.7 sigma`; the beta 2.5 threshold holds. Earlier
failed boundary, box-matching, and doubling tests remain in the
[band record](../GAP_BAND_STATEMENT.md). Preserve those failures when revising
the route.

The [sector-slab probe](../../../../scripts/yang_mills_sector_slab.py)
records failure of test (22) for transverse-cut sector-difference scaling:
at beta 2.4 the fitted exponent is `2.8 [1.7, 4.1]`, with approximately
volume-like scaling. Beta 2.3 remains undetermined by the noise. See the
[recorded data](../../../../data/yang_mills_sector_slab_2026_11_09.json).

## Supporting formal work

The directory also contains reflection positivity and flat-sector
classification; Hessian/coercivity estimates around the twisted flat field;
transfer and finite-gap results; gauge fixing, small-field localization,
and Gaussian comparison; convex and stochastic-localization inequalities;
and the [thermal flux relation](TwistedFluxThermal.lean).

These results have their stated finite-lattice, local-chart, or conditional
scope. A classical Hessian lower bound does not itself imply a quantum mass
gap. Finite-cutoff estimates require the correct physical scaling, and the
[rate filter](RateFilter.lean) rules out an insufficient deficit scale under
its spacing hypotheses. The [attempt assessment](BEST_ATTEMPT.md) and
[scale-invariant coercivity note](COERCIVITY_SCALE_INVARIANT.md) record the
known obstructions and the estimates still required.

## Verification

From the repository root:

```sh
python3 scripts/audit_repository.py --build --output /tmp/unifiedtheory-audit.json
lake env lean scripts/CheckYangMillsTwisted.lean
python3 scripts/check_yang_mills_requirements.py
```

The first command includes independent modules outside `UnifiedTheory.lean`.
The axiom checker explicitly names the declarations it checks; compilation
and axiom cleanliness certify formal implications, not a continuum physical
theory. [Current repository audit](../../../../data/repository_audit_2026_11_09.json).
