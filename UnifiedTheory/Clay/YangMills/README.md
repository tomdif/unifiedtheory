# Yang–Mills research program

Current review: **2026-11-09**. **A nontrivial continuum Yang–Mills theory and a
positive finite physical mass gap remain unproved.** All twelve full-target
requirements are open in the [requirements ledger](../../../data/yang_mills_requirements.json).

## Current route: flux bootstrap and thermal excess

The active [twisted-lattice program](Twisted/README.md) studies a small twisted
SU(2) torus and the estimates needed to reach large volume and a continuum
limit. The [band statement and numerical record](GAP_BAND_STATEMENT.md)
track the current target and registered tests.

[TwistedFluxInduction](Twisted/TwistedFluxInduction.lean) proves conditional
iteration estimates. Sufficient spectral inputs for that version are (S), the
sector-thermal inequality for the transverse step, and K-bar, a uniform
in-plane thermal bound beyond an onset scale. Both need control along the
renormalization trajectory.

[TwistedFluxBasis](Twisted/TwistedFluxBasis.lean) gives the algebraic
transverse relation through `K0/Ke`. [TwistedSubArea](Twisted/TwistedSubArea.lean)
relaxes the bounded-constant iteration: a log cost `m_j <= A + B q^j`,
`0 <= q < 4`, suffices with initial margin `u_0 > A/3 + B/(4-q)`.
The corresponding lattice estimates, initial margin, and renormalization
control remain open. This is a specific growth condition, not a theorem for
every `o(L^2)` cost.
[TwistedSlabCriterion](Twisted/TwistedSlabCriterion.lean) specializes this
recurrence to `q=2`. Its physical interpretation keeps two transverse
directions fixed and does not provide the four-dimensional continuum limit.

[TwistedThermalExcess](Twisted/TwistedThermalExcess.lean), updated November 9,
proves a finite thermal-excess sandwich, a finite logarithmic telescoping
identity, and conditional flux-sector bounds. The eight-sector application
bounds `Kper` by the zero-flux ratio within factors `1/8` and `64`, provided
the required sector positivity and normalized-sum bounds hold. This reduces
the analytic target; it does not establish the uniform thermal bound or the
physical trace correspondence.

The November 8 transverse scan supports registered test (16) on the sampled
boxes and fails test (17) as written. Its fixed cross-section and two couplings
do not establish a large-volume or continuum theorem. The November 9
[thermal-excess results](../../../data/yang_mills_thermal_excess_2026_11_09.json)
miss test (18)'s central-value threshold, though by less than half a reported
standard error, and fail test (19)'s monotonicity requirement. The
[thermal-excess script](../../../scripts/yang_mills_thermal_excess.py)
subsequently registered test (20), which the
[second batch](../../../data/yang_mills_thermal_excess_2026_11_09b.json)
misses as written: beta 2.6, L=12 gives `2.78 ± 1.02` versus `< 1.0`.
The [higher-statistics follow-up](../../../data/yang_mills_thermal_excess_2026_11_09c.json)
misses test (21)'s beta 2.6 threshold on its central value: `1.40 ± 0.58`
versus `< 1.0`, about `0.7 sigma`; the beta 2.5 threshold holds.
The [sector-slab probe](../../../scripts/yang_mills_sector_slab.py) records
failure of test (22)'s subarea criterion at beta 2.4; beta 2.3 remains
undetermined by the noise.

## Earlier constructions and limits

The Wilson/OS modules in this directory retain finite-regulator transfer,
positivity, spectral, and reconstruction results. They include a bare scalar
Wilson limit, OS Hilbert/time-generator constructions, and conditional
renormalized candidates. The analytic hypotheses needed for a nonzero
physical branch and the field identifications remain open; a particular
explicit branch is proved to collapse.

The all-input distant-covariance premise is challenged by the
[pi-flux input experiment](../../../data/yang_mills_pi_flux_input_2026_10_30.json).
It is numerical evidence against that uniform premise, not a proof against
all weighted/integrated alternatives. These negative findings remain relevant
to choosing a viable route. The [current attempt assessment](Twisted/BEST_ATTEMPT.md)
and [coercivity analysis](Twisted/COERCIVITY_SCALE_INVARIANT.md) record further
obstructions and conditional alternatives.

## Full-target obligations

| ID | Obligation still open |
|---|---|
| YM01 | Required compact simple gauge groups |
| YM02 | Nontrivial continuum theory in four dimensions |
| YM03 | Renormalized physical Yang–Mills observables |
| YM04 | Physical fields, Hilbert space, common domains, and adjoints |
| YM05 | Full strongly continuous Poincaré covariance |
| YM06 | Physical translation generators and forward-cone spectrum |
| YM07 | Vacuum uniqueness and full-space cyclicity |
| YM08 | Spacelike locality of physical observables |
| YM09 | Complete adequate quantum-field axioms |
| YM10 | Required ultraviolet behavior and physical operator structure |
| YM11 | Positive spectral gap of the physical Hamiltonian |
| YM12 | Finite nonzero excitation scale |

Each row must refer to the same compatible candidate. A finite-volume gap,
a scalar limit, and a conditional field construction cannot be assembled
into a physical certificate without identification theorems. The ledger's
RG01–RG04 packages describe this repository's chosen strategy.

## Verification

From the repository root:

```sh
python3 scripts/check_yang_mills_requirements.py
python3 scripts/audit_repository.py --build --output /tmp/unifiedtheory-audit.json
lake env lean scripts/CheckYangMillsTwisted.lean
```

The ledger checker verifies references and open-target consistency. The
repository audit requests all library modules, including the modules omitted
by the top-level root imports. The Twisted checker inspects the axiom
dependencies of its explicitly listed declarations. Historical reports under
`data/yang_mills_*_audit.json` retain their original snapshot semantics.
See the [repository status](../../../STATUS.md) for current audit outcomes.
