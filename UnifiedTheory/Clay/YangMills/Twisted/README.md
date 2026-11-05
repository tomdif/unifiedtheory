# Twisted small-volume program

This directory starts a different route to the Yang–Mills target: control a
small twisted torus first, and treat the passage to large volume as a separate
problem. **Nothing here proves the Clay statement, a continuum limit, or a
quantum gap. All twelve full-target requirements remain open.**

## Why this route

A one-step estimate cannot give a physical gap unless its deficit is at least
as large as the lattice spacing. Under asymptotic freedom the spacing behaves
like `exp(-(6π²/11)β)` up to powers of β, in this repo's normalization
(`β_std = 2β`). `RateFilter.energyBound_tendsto_zero` proves the implication,
taking the spacing as a hypothesis. `volume_deficit_filtered` applies it to the
existing `exp(-24βV)` deficit: on any trajectory with spacing at least
`exp(-κβ)`, `κ < 24`, its physical bound tends to zero. So the proof has to be
multi-scale.

## Proved in Lean (axioms: propext, Classical.choice, Quot.sound)

| Module | Result |
|---|---|
| `TwistedReflection` | The law with real coefficients `z_p` on the even periodic lattice is reflection positive whenever `z` is reflection invariant (`reflection_positive`). Invariant Z2 coefficients have trivial flux through every temporal 2-torus (`temporalFlux_eq_one`). The spatial twist is invariant (`spatialTwist_invariant`). |
| `TwistedRectangle` | Discrete Stokes: winding holonomies commute up to the total central power over the 2-torus (`winding`). |
| `TwistedFlat` | A unit quaternion commuting with two anticommuting ones is ±1. Every zero-action field of the `n₁₂ = 1` SU(2) law has `W₁W₂ = -W₂W₁` and `W₀, W₃ ∈ {±1}` (`wind_classification_of_action_zero`). An explicit zero-action field exists (`action_flatConfiguration`). |
| `RateFilter` | The filter above. |
| `CommutingShifts` | Lattice Weitzenböck identity for commuting orthogonal shifts, and the bound `\|Tx - x\|² ≥ 4 sin²(π/2N) \|x\|²` when `T^N = -1`. |
| `TwistedHessian` | The adjoint action of the flat field is diagonal, one flat Z2 bundle per colour (`ad_flatLink`). On the gauge-orthogonal complement the form is at least `8 sin²(π/2N)` (`hessian_coercive`), so there are no zero modes (`no_zero_modes`). |
| `TwistedActionJet` | That form is the second derivative at `t = 0` of the actual twisted action along `exp(tξ) · flatLink` (`second_derivative`). |
| `TwistedTransfer` | Twisted transfer operator on the slice: literal kernel (`twistedKernel_eq`), compact, self-adjoint, positive, nonzero, attained top eigenvector, commuting center flips. `TargetAGap` states the open gap as a Lean `Prop`. |
| `TwistedVacuum` | At each cutoff the top eigenvector is unique and invariant under every flip (`neutral_vacuum`), so the neutral sector is well posed. |
| `TwistedSmallField` | Beyond second order. With every link rotation at most `r ≤ 1`, the actual action is at least `(λ/2 - 384 r²)‖Ω‖² - ½‖div‖²`, where `λ = 4 sin²(π/2N) ≥ 4/N²`. A divergence-free perturbation with `r ≤ 1/(20N)` has action at least `‖Ω‖²/N²` (`action_coercive_coulomb`). |
| `TwistedLocalization` | **Quantum measure.** `S ≤ 24·dist²` to the flat field, so `Z` is at least an exact product of Haar Gaussian masses (`partition_lower`). Hence `P(S ≥ s) ≤ exp(-βs)·cap(24β)^links` (`action_tail`), and the winding relations fail at scale `ε` with at most that probability at `s = ε²` (`localization`). |
| `TwistedLandau` | A gauge-orbit minimizer of the distance to `flatLink` exists, and its stationarity is exactly vanishing colour divergence of `Im(U F⁻¹)` (`div_imPart`). If the orbit of `L` comes within `1/(32N)` of the flat field, its closest representative has `dist²/N² ≤ S(L) ≤ 24 dist²` (`orbit_quadratic`). |
| `TwistedAxial` | Every link field is gauge equivalent to an exact axial form, with links equal to one away from a seam, on successive slabs (`exists_axial`). |
| `TwistedFrame` | A nearly anticommuting pair of unit quaternions is rotated by one element to within a fixed multiple of the error of `i, j` (`align`). |
| `TwistedSeams` | In axial gauge with plaquette defects at most `ε`, off-seam links are near one and seam links near four constants obeying the twisted relations, all at scale `N(ε + Nε)`. |
| `TwistedNearFlat` | **Removes the hypothesis of `orbit_quadratic`.** If `S(L) ≤ (1/(1408 N⁵))²`, some center class and gauge have `dist² ≤ N² S(L)` to the flat field (`near_flat`). Under the law, leaving that `N²σ` neighbourhood has probability at most `exp(-βσ)·cap(24β)^links` (`measure_near_flat`). |
| `TwistedGaussianCompare` | For divergence-free `Ω` with rotations at most `r` and `10Nr ≤ 1`, the action is the curl energy up to relative error `30Nr` (`gaussian_comparison`). A sharper `δ`-family is `action_two_sided`. |
| `TwistedMehler` | Free one-mode kernel. Gaussian and Gaussian times `x` are eigenfunctions with ratio `ρ`, `ρ + 1/ρ = κ + 2`, independent of `β` (`eigen_ground`, `eigen_excited`), i.e. `4 sinh²(ω/2) = κ` (`dispersion`). At the lowest twisted stiffness, `√2/N ≤ ω ≤ π/N` (`window`). |
| `TwistedCollatz` | For any positive continuous `ψ`, `m ψ ≤ Tψ ≤ M ψ` implies `m ≤ ‖T‖ ≤ M` for the actual twisted operator (`collatz_wielandt`). |
| `TwistedTreeGauge` | The coordinate-tree gauge is an exact measure-preserving change of variables on a slice, with no Jacobian (`sliceMap_preserving`). Gauge-invariant integrals, inner products and the twisted transfer form reduce to off-tree links (`integral_invariant`, `inner_reduction`, `form_reduction`). |
| `TwistedSliceLift` | A slice lifts to a static 4D field. `holo`, the real part of `W₃`, is gauge invariant, odd under the center flip, Lipschitz against the kinetic action, and satisfies `holo² ≥ 1/2` when the twisted potential is below `1/(16 n⁴)`. |
| `TwistedNormLower` | `‖T‖ ≥ mass(24β)^{7n³}`, a loss polynomial in `β` per link, from Gaussian integrals around the flat slice (`norm_lower'`). |
| `TwistedFluxSector` | **A spectral statement about the actual `T`.** By the ground-state identity, `holo · Ω` is flip-odd, orthogonal to the vacuum, and contracted by at most `1 - 2(n+4)t` under explicit conditions (`flux_near_degenerate_explicit`). For fixed `n` and any `ε`, this holds with `1 - ε` at all large `β` (`flux_gap_vanishes`). So a uniform gap can only hold in the neutral sector. |
| `TwistedFiniteGap` | At each cutoff, `T` contracts the whole complement of the neutral vacuum by some `ρ < 1`, with no control of `ρ` (`finite_gap`). So Target A concerns uniformity in `n`, not existence of a gap. |
| `TwistedHessianField` | The action's second derivative along `exp(tX)·U` at a general background, in exact form (`second_derivative_field`). With every link within chord `r` of flat it is at least `β(Σ curl energy - (3072 r² + 192 r)‖X‖²)` (`hessian_field_lower`). For flat-divergence-free `X` and `r ≤ 1/(100N²)` this gives `≥ (2β/N²)‖X‖²` (`hessian_field_coercive`). The whole `near_flat` region qualifies after its gauge and center shift (`near_flat_coercive`). This is pointwise and along geodesics. It is not convexity of a reduced potential, and it says nothing about the measure or the ground state. |
| `BlockShifts` | The smooth part of a block average has gradient at most `2/L + 3Lκ` times the field, and never more than the field's own gradient up to `4Lκ` (`smooth_grad`, in covariant form `cov_split`). For orthogonal shifts that need not commute: a Weitzenböck inequality whose error is `4κ‖ω‖²`, with `κ` the commutator bound (`weitzenbock_le`), a block Poincaré inequality `‖x‖² ≤ 2‖A_L x‖² + 8L²Σ‖D_ν x‖²` for ordered running averages (`block_poincare`), and their combination (`block_coercive`). No spectral gap and no lattice size enter. |
| `TwistedCovariant` | **The first bound here uniform in `N`.** With `U`-covariant shifts, the commutator is at most twice the sup plaquette defect (`cov_comm`), and the Hessian is bounded by the covariant curl up to `(192δ²+48δ)‖X‖²` (`hessian_cov_lower`). If all defects are at most `1/(1000L²)`, then Hessian + `β‖div_U X‖²` + `(β/4L²)Σ‖A_U X_μ‖²` ≥ `(β/16L²)‖X‖²` (`cov_block_coercive`). Neither constant nor condition involves `N` or the distance from flat. `measure_smallDefects` is the matching tail, from the global action tail only. |
| `TwistedBadSet` | The covariant bound with its hypothesis localized. On directions vanishing on the links of plaquettes with defect above `1/(1000L²)`, the same `β/(16L²)` holds, with nothing assumed on the bad plaquettes (`block_coercive_avoids`). At most `4` links per bad plaquette are removed (`card_badLinks_le`). Except on an event of probability `exp(-t·links)`, the number of bad plaquettes per link is below `(log cap(24β)+t)/(βδ²)`, with no volume dependence (`measure_bad_density`). |
| `TwistedBlockMap` | A factor-2 block-spin map on the group: the projection of the line plus `α` times six staples, with center signs so the twist does not cancel the sum. Gauge covariant (`blockLink_act`), equal to the line on the flat field (`blockLink_flat`), within `4δ` of the line for every `α ≥ 0` when the nearby defects are at most `δ < 1/2` (`blockLink_close`), and blocked plaquette defect at most `20δ` (`blocked_defect`). A worst-case bound with local hypotheses. It says nothing about the law of the blocked field. |
| `TwistedBlockLaw` | The first statement about the blocked field's law. Except with probability `exp(-t·links)`, the number of blocked links that may fail to be within `4δ` of their line is at most `8(log cap(24β)+t)·links/(βδ²)`, uniformly in the volume (`measure_blocked_links`, `close_of_not_notGood`). It says where the field lies, not what its density is, and it inherits worst-case constants. |
| `TwistedIBP` | **An exact identity for the actual measure.** Haar measure is invariant under the flow `U ↦ exp(tX)·U`, so `E[(∂_X S)²] = E[∂²_X S]` for every direction `X`, every `β ≥ 0` and every lattice size, with no smallness and no Gaussian approximation (`gibbs_ibp`). Hence `E[(∂_X S)²] ≤ 48β‖X‖²` (`force_bound`). It controls the force along `X`, not each plaquette's defect. With an observable it gives the exact plaquette equation `2β Σ_q E[A_q A_p] = -E[B_p]` (`plaquette_ibp`), and a volume-free local bound conditional on nonnegative cross terms (`own_le_of_cross`, hypothesis open). |
| `TwistedSlice` | **Reflection positivity on the plaquette rates.** For `X` on the fixed time slices, `E[(T₊ - T₊∘θ)²] ≤ E[T²]` (`slice_le_force`), and `E[T²] ≤ Σ_p (Σ_{e∈p}‖X_e‖)²/(2β)` (`force_sq_le`). For one link of the slice `t = 0`, the plaquette above and its mirror image satisfy `E[A_p A_p'] ≥ 0` (`opposite_nonneg`) and `E[(A_p - A_p')²] ≤ 12‖X‖²/β` (`single_link_bound`), with no volume factor. This proves only the opposite-plaquette sign, in the time direction. |
| `TwistedPoincare` | The ground-state identity turns the transfer form into a Dirichlet form (`ground_state_identity`). A neutral Poincaré inequality with constant `C` gives contraction `1 - 1/C` on the neutral complement (`gap_of_poincare`), and `C = n/c` gives exactly the `exp(-c/n)` of `TargetAGap` (`exp_of_poincare`). The inequality itself is open. |
| `TwistedStability` | Stokes with errors. If the total twisted action satisfies `S ≤ 1`, some base point has `W₁, W₂` anticommuting to within `√S`, and `W₀, W₃` within `(8/3)√S` of `±1`, with no lattice-size factor (`action_stability`). |

Check: `lake env lean scripts/CheckYangMillsTwisted.lean`, 142 key declarations. These modules are not
imported from the root `UnifiedTheory.lean` and not yet in the audit chain.

Limits of these results:

- The temporal-flux theorem rules out reflection-invariant coefficients. It does
  not prove reflection positivity fails for a temporal twist, and invariance of
  the flux under center gauge changes is not formalized.
- The classification is classical and concerns holonomies only. It is not a
  statement about the quantum theory.
- The 4D Lean law has equal time and space extent. The transfer operator does not
  depend on the time extent. `Tr T^t` is now identified with the 4D law (`law_partition_trace`, `chainZ_trace`), at any `T ≥ 2` through `chainLaw`.
- The Hessian bound is sharp numerically (below). Sharpness is not proved in Lean.
- `action_stability` needs `S ≤ 1`. A typical quantum field at finite β has `S` of
  order `N⁴/β`, so it applies to smooth or blocked fields, not raw sampled fields.
- The Hessian bound controls only the second derivative at the flat field. There is
  no Taylor-remainder or small-field estimate yet.
- `TwistedMehler` is a one-mode model. It does not show its eigenvalues are the top two, handle
  many modes, or connect to the Wilson operator. `collatz_wielandt` is exact but needs a trial
  function accurate pointwise, including far from the flat field, and none is constructed.
- `gaussian_comparison` is in Coulomb coordinates, while `form_reduction` is in tree coordinates. They
  are not connected, and tree-gauge coordinates lose powers of N against the curl energy. The temporal
  Haar average inside the kernel has not been evaluated semiclassically either.
- `TwistedFluxSector` bounds a gap from above, in the flux-odd sector only. It gives no lower bound on
  any gap and says nothing about the neutral sector, whose gap is the one Target A wants. Its thresholds
  grow like `n⁷ log n`. They are far above the physical trajectory.
- `near_flat` needs `S ≲ N⁻¹⁰`, so `measure_near_flat` only says something when β exceeds about
  `N¹⁴ log N` with a large constant: about `1.4×10¹⁷` at `N = 4` and `5.5×10²⁵` at `N = 16`, by an
  asymptotic estimate of `cap`. Its limit theory is free.
- `localization` is useful only when `β ε²` exceeds about `4N⁴ · log cap(24β)`. At `ε = 1`
  that is `β ≈ 2×10⁴` at `N = 4` and `3×10⁹` at `N = 64`, against an asymptotic-freedom
  increment of `0.186 log N`. These thresholds use the asymptotic Gaussian mass, not a
  formal evaluation of `cap`. Monte Carlo at `N = 8`, `β = 16` already shows `|tr W₃| ≈ 1.8`,
  so the bound is far from sharp: it charges fluctuations by `L¹` Stokes and ignores cancellation.
- The top-eigenvector theorem gives no uniform gap. `NeutralWindow` now holds at each cutoff with `β > 0` (`exists_neutralWindow`), with no control of its level.

## Numerical checks (not proofs)

Exact lattice Hessian at the flat twisted field,
`scripts/yang_mills_twisted_hessian_probe.py`, N = 3, 4, 5:

| | Nullity | Physical zero modes | Lowest nonzero eigenvalue |
|---|---|---|---|
| untwisted | 3N⁴ + 9 | 9 | `8 sin²(π/N)` |
| `n₁₂ = 1` | 3N⁴ | 0 | `8 sin²(π/2N)` |

Heat bath of the full twisted law, `scripts/yang_mills_twisted_spectrum_probe.c`.
Effective masses at the start of the plateau, compared with tree level, T = 3L,
β = 16 in repo units:

| Channel | N=6 measured | N=6 tree | N=8 measured | N=8 tree |
|---|---|---|---|---|
| one gluon, flux-carrying | 0.517(8), 0.522(14) | 0.512 | 0.392(9), 0.412(14) | 0.388 |
| neutral, zero momentum | 1.019(26), 0.938(69) | 1.024 | 0.795(27), 0.748(44) | 0.775 |

Runs at T = L gave neutral masses that were too low, apparently from flux states
wrapping around time, so only T = 3L should be compared. β = 8 broadly agrees, with
some N = 8 one-gluon points about 2σ low. `trW₃` stayed in one sign valley at every coupling run, so tunneling
was not observed and its splitting was not measured. This is a deep perturbative
regime: it validates the setup, not the hard part of any proof.

## Target A: the first real theorem (open)

Fix SU(2) and the twist `n₁₂ = 1`, with time extent T ≥ L, `a = L/N`. Let `u` be
the twisted gradient-flow coupling at flow time proportional to L².

There is `u* > 0` such that for each `u ∈ (0, u*)`, on a trajectory `β_N → ∞`
holding `u` fixed:

1. Schwinger functions of flowed gauge-invariant observables at positive flow
   time are bounded uniformly in N and converge.
2. The limit is nontrivial: a connected separated two-point function is nonzero.
3. Reflection positivity survives, inherited from `reflection_positive` once the
   lattice allows T ≠ L.
4. The transfer operator restricted to the neutral sector has
   `E₁(N) ≥ c/L`, with `c > 0` independent of N. The expected leading value is
   `c → 2π` as `u → 0`. Neutral means invariant under the Z2³ sign flips of link
   slabs, which preserve every plaquette; that symmetry is not yet formalized.

Target A deliberately excludes the zero-flow local field identification, the
large-volume limit, and Poincaré invariance. It would not solve the Clay problem.

The gap half is the Lean `Prop` `TwistedTransfer.TargetAGap b`: for all `n ≥ 2` and
`β ≥ b log n + β₀`, the neutral window holds with ratios `exp(-c/n)` and `exp(-C/n)`.
The asymptotic-freedom slope in this normalization is `b = 11/(6π²)`, which is a
perturbative input, not proved. Two-loop running may require a `log log n` term at that
exact slope, so the statement is safest for `b` strictly above it. Those trajectories
reach a shrinking physical volume and a theory that becomes free in the limit.

## Next steps, in order

1. **Milestone A₀, a semiclassical gap.** Prove the window for `β ≥ n^p` with some
   explicit `p`, by harmonic approximation around the flat classes. This needs no RG,
   and would be the first cutoff-uniform physical gap here on a trajectory with
   `β → ∞`. It is a large, unstarted project. The limit theory is free, so this is a
   test of the machinery, not of the hard physics.
2. (Done: `near_flat`, `gaussian_comparison`, the free mode, tree-gauge reduction.) A₀ still lacks its
   analysis: a neutral Poincaré inequality with constant about `n`, which `exp_of_poincare` shows is
   sufficient. The route through it is the Laplace evaluation of the temporal Haar average, comparing the
   reduced operator to the many-mode Gaussian operator,
   and a sector-resolved spectral bound at accuracy `1/N`. Possible tool, untested: Schur or
   Collatz-Wielandt bounds in flux-odd sectors, where the odd kernel may be positive on a
   fundamental domain.
3. Identify `Tr T^t` with the 4D twisted law, and build the twisted Gaussian covariance
   and its decay on the block scale.
4. Do one Bałaban-style block step, retaining sources and large-field terms. The linear estimate exists now
   (`cov_block_coercive`). Missing: a block-spin constraint on the group, a localized form of the defect
   hypothesis, a volume-uniform local tail (chessboard), pointwise propagator decay, and the effective action.

## Crossover scan (numerics, not proofs)

`scripts/yang_mills_twisted_spectrum_probe.c`, spatial size L = 6, 8, 10, T = 3L, 40 bins,
`β_std = 2β` from 2.2 to 6. Analysis: `scripts/yang_mills_twisted_scan_analysis.py`.

- **One-gluon `E·L`** stays near π from `β_std = 6` down to about 2.6. At 2.4 it grows with L:
  about 3.5, 5, 10 at L = 6, 8, 10, noisy.
- **Neutral `E·L`** stays near 6 for `β_std ≥ 3`, consistent with 2π, with no visible dip through
  the scanned range. Below that it rises but is poorly resolved, with errors from about 1 to
  well above the value. Whether it dips below 2π at a finer scale is not settled.
- **`e₃` flux `E·L`** rises with L at each coupling where `⟨tr W₃⟩ ≈ 0` so both valleys are sampled.
  At 2.4 the plateau is about 1.7, 4, 6, roughly σ L² with σ ≈ 0.05-0.06. At 2.2 and L = 6 it is about
  8-11. These sizes resemble string tensions I recall for SU(2), about 0.07 and 0.22, which I did not
  look up. This is a sanity check, not a measurement of σ.
- **At weak coupling the `e₃` channel is not measured.** For `β_std ≥ 3` and L = 6 at 2.6, one
  valley dominates, so the correlator is close to constant and tunneling is absent.

A finer scan used L = 6, 8, 10, 12 at `β_std` = 2.3, 2.4, 2.5, 2.6:

- **`e₃` flux `E·L`** rises with L at all four couplings, roughly at 2.4: 1.45, 3-4, 7, then too noisy
  at L = 12 (about 10 ± 8). At 2.6: 0.3, 0.6, 1.2, about 2-3. The L = 6 values at 2.5 and 2.6 have partial
  valley trapping, with `⟨tr W₃⟩` 0.07 and 0.25.
- **Neutral `E·L`** shows no resolved dip below 2π: at 2.6 about 6.5, 8-9, then errors comparable to
  the value. The signal is lost beyond about L = 8, so this is weak evidence.
- **One-gluon `E·L`** at 2.6 sits near 2.7 at L = 6, 8, below the tree value 3.1 by a few errors, while
  the effective mass is still drifting. At 2.4 it grows with L.

Candidate for the bridge, as a conjecture only: `L·E_{e₃}(L)` increases with L at fixed coupling.
The evidence is now four sizes at four couplings, with large errors at the largest size, and I have no
proof of monotonicity.

## Convexity check (numerics, not proofs)

Candidate route to the neutral Poincaré inequality: the Brascamp-Lieb mechanism, in which a transfer
operator with uniformly convex action has a log-concave ground state and a gap at least the harmonic one,
with no direct knowledge of the ground state. It can only apply where the action is convex in
gauge-orthogonal directions, so this was tested first with `scripts/yang_mills_twisted_convexity_probe.py`.

Smallest gauge-orthogonal eigenvalue of the second-order form of the twisted slice potential on fields
sampled from the twisted law, divided by the flat value `4 sin²(π/2N)`. Repo `β`, few configurations
(6, 4, 2 for N = 4, 6, 8; at β = 4 only N = 4 was run):

| β | N = 4 | N = 6 | N = 8 |
|---|---|---|---|
| 4 | -0.47 | | |
| 16 | +0.57 | +0.26 | -0.06 |
| 64 | +0.85 | +0.77 | +0.70 |
| 256 | +0.93 | +0.90 | +0.89 |
| 1024 | +0.97 | +0.96 | +0.96 |

The zero crossing moves roughly as `N^1` to `N^1.5` on three sizes: about β = 6, 12, 17. That is far below
the proved thresholds (`N⁷`, `N¹⁴`) but still grows as a power, so at the bare lattice scale it cannot
reach a `log N` trajectory. Positivity at typical fields is necessary for the route, not sufficient. It
has to hold on all relevant fields, and the Brascamp-Lieb argument still has to be adapted to a curved
group with a temporal gauge average. None of that is done.

### What the proved region reaches, and the decision on Brascamp-Lieb

`near_flat_coercive` is the rigorous counterpart of the probe above. Its region carries the measure only
through `measure_near_flat`, which needs `β ≳ N¹⁴ log N`: about 1.4×10¹⁷ at N = 4 and 5.5×10²⁵ at N = 16.
A physical trajectory needs `β` growing like `log N`.

So the planned next steps, a flat-space Brascamp-Lieb toy and its adaptation to the group, are **not being
pursued as a route to Target A**, for these reasons:

- Even the empirical convexity threshold grows as a power of `N`, so no sharpening of these constants
  reaches `log N` at the bare scale. Convexity could only apply after RG blocking, which does not exist here.
- The toy's real content is Prékopa's theorem, which Mathlib lacks, and it needs convexity on all of the
  relevant space. The action here is not globally convex: it has center-related minima and a degenerate
  flux-odd sector (`flux_gap_vanishes`).
- At best it would contribute to A₀, the semiclassical gap, whose limit theory is free.

The obstruction is now specific: any neutral Poincaré proof must work outside the convex region, or start
from a blocked effective action. This is an assessment of the route, not a theorem.

## Covariant block bound

`TwistedHessianField` measures distance from the flat field, which is why its condition is `r ≲ 1/N²`.
`TwistedCovariant` replaces that with the local gauge-invariant plaquette defect and adds a block penalty,
so the fluctuation covariance norm is bounded by `16L²/β` in place of `N²/(8β)`. This is the linear
estimate a block RG step needs, in its weakest form: an `L²` operator bound, not the pointwise decay of
Bałaban's propagators. It has no block-spin constraint on the group, and it gives no effective action.

Coupling needed for `δ ≤ 1/(1000L²)` on all plaquettes (estimate from `measure_smallDefects`, solving
`β δ² = L_links · log(K(24β)^1.5) + 1` with the asymptotic cap estimate; not formal):

| | N = 4 | N = 16 | N = 64 |
|---|---|---|---|
| `L = 1` | 4.5×10¹⁰ | 1.4×10¹³ | 4.1×10¹⁵ |
| `L = 2` | 7.8×10¹¹ | 2.4×10¹⁴ | 7.0×10¹⁶ |
| `L = 4` | 1.4×10¹³ | 4.1×10¹⁵ | 1.2×10¹⁸ |
| `near_flat`, for comparison | 1.4×10¹⁷ | 5.5×10²⁵ | 1.9×10³⁴ |

The power of `N` in `β` drops from 14 to 4. The remaining `N⁴` comes only from using a global tail. A local
tail, uniform in volume, would give about `10⁶ L⁴ log N`. Chessboard estimates from reflection positivity are
the natural tool. That is not done, and it would not reach a physical trajectory:

- The constant is too large. `log N` has the right form, but the asymptotic-freedom slope is about 0.19, not 10⁶.
- More basically, on a trajectory `β ~ 0.19 log N` one expects some plaquettes among `N⁴` to have large
  defects at any `N`, so a hypothesis on **all** plaquettes should fail. This is a heuristic, not a measurement.
  It is why Bałaban separates small-field and large-field regions, and a usable version must localize the
  hypothesis in the same way.

Numerics (`scripts/yang_mills_twisted_block_fluct_probe.py`, lowest eigenvalue of the form at `β = 1`,
`N ≤ 8`, data in `data/yang_mills_twisted_block_fluct_2026_10_30.json`). Flat background, unblocked, then
`L = 2`: 0.586, 0.639 at N = 4; 0.268, 0.326 at N = 6; 0.152, 0.212 at N = 8. The difference tends to
`1/(4L²) = 0.0625`, as a low mode with `A_L ≈ 1` would give, above the proved floor `1/(16L²) = 0.0156`. A gauge
transform of flat at chord distance about 2 reproduces the flat spectrum to many digits (earlier run, penalty
`1/L²`), so chord distance is not the controlling quantity. Fields with small noise (defect about 0.15 to 0.19)
stay above the floor, though they are outside the theorem's hypothesis.

The test failed to cover the interesting case. My "smooth" non-gauge backgrounds had defects from 1.2 to 2.0,
because they are not smooth across the twist seam, and gave large negative eigenvalues. So a non-gauge
background far from flat with small defects has **not** been tested numerically. The theorem covers it, but
the numerics give no independent confirmation. `N ≤ 8` also cannot show the uniformity, since the unblocked
value still dominates at these sizes. The uniformity is from the proof.

### Localizing the hypothesis

`TwistedBadSet` removes the all-plaquette hypothesis without a chessboard estimate. The global tail already
bounds the **density** of bad plaquettes uniformly in the volume, and the commutator error in the Weitzenböck
step is local, so a direction vanishing on bad links never sees a bad plaquette. The result: with probability
at least `1 - exp(-t·links)`, the form is at least `β/(16L²)` on a subspace whose codimension is a fraction
at most `4(log cap(24β)+t)/(βδ²)` of all directions, for every `N`.

Coupling for that fraction, `t = 1`, asymptotic cap estimate, not formal:

| | fraction 0.1 | fraction 0.01 |
|---|---|---|
| `L = 1` | 1.6e+09 | 1.7e+10 |
| `L = 2` | 2.8e+10 | 3.0e+11 |
| `L = 4` | 4.9e+11 | 5.3e+12 |

These do not depend on `N`. For comparison, the all-plaquette version of this at `L = 1` needed 1.4×10¹³ at
`N = 16` and grows as `N⁴`. Any trajectory with `β → ∞` eventually enters this regime for fixed `L`.

What this does not give:

- The excluded directions can be negative, and at a large-field plaquette they should be expected to be. The
  action is not convex on the full space, so this is not a Poincaré inequality, and a measure argument must
  still treat the excluded directions.
- It holds at fixed `L`, with bare defects about `1/√β`. Reaching physical scale `L ~ e^{cβ}` needs defects below
  `1/L²`, which bare fields do not have, so iterating needs a blocked effective action with its own defects.
- The constant `1000` is crude. A noisy field with sup defect about 0.43 at `N = 4` stays positive for `L = 2` in
  the earlier probe, which suggests a threshold nearer 0.5 for the form. That is a single sample, not a test.

So the remaining gap is the nonlinear part of a block step, which is the bulk of the hard work.

## Which block map (numerics, not proofs)

Before formalizing a map, `scripts/yang_mills_block_map_probe.py` measured `e_j = <2 - 2 Re P>` at blocking level
`j`, and `scripts/yang_mills_block_map_free.py` computed the exact weak-coupling limit `c_j = lim β e_j`. Data are in
`data/yang_mills_block_map_2026_10_30.json`. Heatbath runs are untwisted single runs with no error bars computed.

Exact free ratios `c_{j+1}/c_j`, N = 32:

| α | level 0→1 | 1→2 | 2→3 |
|---|---|---|---|
| 0 (path product) | 2.74 | 2.38 | 2.20 |
| 0.1 | 1.18 | 1.18 | 1.13 |
| 0.15 | 0.91 | 1.02 | 1.01 |
| 0.25 | 0.66 | 0.88 | 0.93 |
| 1 | 0.45 | 0.70 | 0.86 |

- **The path product is unusable.** Its ratio tends to 2, the perimeter law for an unsmeared loop, so its defects
  double every step even at zero coupling. The heatbath agrees at `β_std = 64`: 0.0235, 0.0639, 0.1496 against
  predicted 0.0234, 0.0642, 0.1529. A bound on this map could not be iterated, so the Lean map averages.
- **Transverse averaging fixes it.** With `α > 0` the ratios appear to approach 1. That is expected, since a smeared
  `F` is scale invariant in 4D free theory. I have not proved this limit, and `N ≤ 32` shows only the trend.
- **`blocked_defect` cannot see this.** A smooth field scales its defect by 4 under any such map, so worst-case
  bounds never give stability. The stability above is a statement about Gaussian noise. A proof has to separate noise
  from smooth background, which is what Bałaban's small-field expansion does.

**Effective coupling.** With `β_eff(j) = c_j / e_j` at matching N, `β - β_eff`, repo units, N = 24:

| β_std | α | j = 0 | 1 | 2 | 3 |
|---|---|---|---|---|---|
| 8 | 0.25 | 0.114 | 0.632 | 0.861 | 0.955 |
| 16 | 0.25 | 0.108 | 0.644 | 0.864 | 0.824 |
| 8 | 1 | 0.114 | 0.709 | 0.919 | 0.974 |
| 16 | 1 | 0.108 | 0.716 | 0.919 | 0.945 |

The shift is positive and, through `j = 2`, the same at both couplings, the shape a one-loop effect should have. The
**slope is not confirmed**. Asymptotic freedom predicts about 0.129 per doubling. The step from level 1 to 2 is about 0.2
to 0.23, and the step from 2 to 3 ranges from -0.04 to 0.09, on a coarse lattice of side 3 where finite-volume effects
and zero modes are not under control. The larger `β_std = 64` values at N = 16 drift upward with level, probably from
slow thermalization of long modes, and I do not trust them. This is a check of sign and form only.

## Step scaling of the blocked coupling (numerics, not proofs)

The effective-coupling table above was muddied by zero modes and by changing coarse volume, so
`scripts/yang_mills_twisted_step_scaling.py` redoes it on the twisted lattice, with no zero modes, with the same signed
map as `TwistedBlockMap`, the exact twisted free values, and jackknife errors. Data are in
`data/yang_mills_twisted_step_scaling_2026_10_30.json`. At fixed coarse side, doubling `N` at fixed bare `β` doubles the
physical size, so `β_eff(N) - β_eff(2N)` should tend to `ln 2 · 11/(6π²) = 0.129`, repo units, a value stated before
the `N = 32` run. At `β_std = 8`, coarse side 4:

| α | N = 8 → 16 (levels 1 → 2) | N = 16 → 32 (levels 2 → 3) |
|---|---|---|
| 0.25 | 0.252 ± 0.012 | 0.135 ± 0.018 |
| 1 | 0.232 ± 0.013 | 0.118 ± 0.020 |

The last step agrees with the one-loop value at both weights. The sign, size and independence of `α` are what
asymptotic freedom predicts for this map. At `β_std = 8` and 16, the shift through level 2 also matches between
couplings within errors, as a one-loop effect should (`β_std = 16` has no `N = 32` point).

Limits of this check:

- One step is in agreement, from a run of 30 measurements, and the jackknife is unbinned, so true errors may be larger.
- The earlier step is about twice the prediction. The level-dependent excess falls quickly (level steps 0.52, 0.23, 0.14 at
  `N = 32`, `α = 0.25`), but I cannot rule out that it keeps falling past 0.129. `N = 64` would test this and needs
  about 2 GB for the links alone, over the working limit here.
- This shows the map tracks the expected flow. It proves nothing, and no theorem here uses it.

## Integration by parts (proved; numerical check is not a proof)

`gibbs_ibp` is the first statement here about the measure that does not come from a worst-case bound or a global tail. It
needs only Haar invariance and the exact second derivative. `scripts/yang_mills_twisted_ibp_check.py` compares both sides by
finite differences of the action on a twisted heatbath at `N = 4` (4000 samples, data in
`data/yang_mills_twisted_ibp_check_2026_10_30.json`), per unit `‖X‖²`, with `S` the full action:

| β_std | X | E[S₁²] | E[S₂] | proved bound 48β |
|---|---|---|---|---|
| 2 | one link | 6.18 ± 0.13 | 5.99 ± 0.03 | 48 |
| 2 | random field | 6.21 ± 0.14 | 6.00 ± 0.00 | 48 |
| 4 | one link | 19.44 ± 0.43 | 19.17 ± 0.03 | 96 |
| 4 | random field | 19.89 ± 0.44 | 19.19 ± 0.01 | 96 |
| 8 | one link | 43.88 ± 0.96 | 43.40 ± 0.03 | 192 |
| 8 | random field | 43.20 ± 0.97 | 43.37 ± 0.01 | 192 |

The sides agree within errors, at about 2% precision, with differences up to 1.6σ. The proved bound holds and is loose by a factor of
4 to 8, since the value tracks `12β⟨Re zP⟩`. That form is a hand calculation for a single link, not in Lean.

What it does not give: the force at a link is a sum over its six plaquettes, so small force does not mean small defects, and
turning this into a gap is open. The natural next statement is the same flow applied with an observable,
`E[∂_X S · O] = E[∂_X O]`, which gives exact relations for correlators of blocked fields.

### The plaquette equation and an open sign question

`plaquette_ibp` is an exact lattice loop equation. For `X` a single link `ℓ` and summed over colours it reads, by hand from the
Lean form, `2β Σ_{q∋ℓ} E⟨Im c_p, Im c_q⟩ = 3 E[Re c_p]`, with `c_q` the plaquettes through `ℓ` in the frame at its tail.
`scripts/yang_mills_twisted_loop_eq_probe.py` measured this at `N = 8` (data in `data/yang_mills_twisted_loop_eq_2026_10_30.json`):

| β_std | own | opposite | other planes | 2β × sum | 3 Re c |
|---|---|---|---|---|---|
| 1 | 0.7198 | -0.00012 ± 0.00011 | 0.00228 | 0.729 | 0.730 |
| 2 | 0.6129 | 0.00713 | 0.03293 | 1.504 | 1.505 |
| 2.5 | 0.5026 | 0.03061 | 0.06247 | 1.958 | 1.957 |
| 4 | 0.3354 | 0.03361 | 0.05774 | 2.400 | 2.399 |
| 8 | 0.1776 | 0.02151 | 0.03495 | 2.711 | 2.711 |
| 16 | 0.0912 | 0.01186 | 0.01885 | 2.855 | 2.858 |

**Open conjecture.** If every cross term is nonnegative, then `E‖Im c_p‖² ≤ 3/(2β)`: a local bound with no log and no volume
dependence, which would replace the global tail. The measured `2β × own` is 0.72 to 1.46, below 3. Evidence:

- For `β_std ≥ 2`, all 120 pairs are positive, by margins of many standard errors.
- At `β_std = 1`, 12 of 120 pairs are negative, the worst -0.0014 ± 0.0005, about 2.6σ. With a class mean of
  -0.00012 ± 0.00011 and 120 comparisons this may be noise, but it is **not** resolved, and the conjecture could fail at strong coupling.
- These averages sum over colours and over sites, at one size. The theorem's hypothesis is per colour direction, so this tests
  a weaker statement. `N = 8` is the only size measured.

Possible proof of one class: the opposite plaquette is the mirror image of `p` in a plane through `ℓ`, so a site reflection positivity
statement could give that sign. I have not checked that the repo's reflection covers it, or the twist. I know no argument for
the other-plane class, and correlation inequalities of GKS type are not available for SU(2).

Even if true, the bound gives `‖Im c_p‖`, which is also small for `c_p` near `-1`, so it does not exclude large defects by itself.

## After Target A

Steps 2 and 3 of the attack remain: a finite-box mixing criterion for generated
blocked actions, and a bridge from small to large volume. No argument for the
bridge exists here, and it is the Clay problem in substance.

## Literature (checked 2026-10-30, by search results rather than full reading)

- [Ramos, twisted gradient-flow coupling](https://arxiv.org/abs/1409.1445), cited through
  [later TGF work](https://arxiv.org/pdf/1412.0941) and
  [perturbative TGF results](https://ar5iv.arxiv.org/html/1810.12822).
- [Magnen–Rivasseau–Sénéor, YM₄ with an infrared cutoff](https://typeset.io/pdf/construction-of-ym-4-with-an-infrared-cutoff-ih1ve3998t.pdf):
  SU(2) Schwinger functions with a fixed infrared cutoff, in axial gauge. This is
  an alternative base for Target A and should be read before Bałaban step 4.
- [A Perspective on Constructive Quantum Field Theory](https://arxiv.org/pdf/1203.3991)
  on Bałaban's lattice ultraviolet stability.

The search found no established work on this twisted route, which is weak evidence
at best. It also surfaced several unrefereed claimed full solutions; none is used.

## Reflection positivity on the rates (`TwistedSlice`)

Write `T = T₊ + T₊∘θ + R` for the rate of the action along a slice-carried `X`, with `R` the part in the fixed slices, which `θ` fixes. Reflection positivity applied to `F = 2T₊ + R` and the pointwise identity `T² = (F∘θ)F + (T₊ - T₊∘θ)²` give `slice_le_force`. No measure invariance or conditional expectation is used.

For one link, `A_p - A_p'` is the lattice second time difference of the field and `T` is the lattice Yang-Mills equation of motion, so this is an `L²` estimate of one component of the equation by the whole. It bounds a difference and not `A_p` itself: `E[A_p²] - E[A_p A_p']` is controlled, and `E[A_p A_p']`, the squared mean of `A_p` given the slice, is not.

Scope: the reflection is in time only. A reflection in direction 1 or 2 does not preserve the twist (`not_invariant_of_temporalFlux`). Direction 3 and other time slices should follow from symmetry and translation, and are not formalized. Nothing here reaches the different-plane cross terms. A diagonal reflection does not fix its second hyperplane pointwise on this torus, so it gives no square.

Comparison at `N = 8` (`data/yang_mills_twisted_loop_eq_2026_10_30.json`), summed over colours, averaged over sites and all directions, hand-derived forms:

| `β_std` | `2(own - opp)` | `E‖Im W‖²` | `9/β` (`force_sq_le`) | `36/β` (`single_link_bound`) |
|---|---|---|---|---|
| 4 | 0.604 | 3.598 | 4.5 | 18 |
| 8 | 0.312 | 2.033 | 2.25 | 9 |
| 16 | 0.159 | 1.072 | 1.125 | 4.5 |

The force bound is nearly sharp and the slice estimate is loose by a factor of about 6.5. The left column cannot exceed 4, so `single_link_bound` says something only for `β_std > 18`, and the sharper form for `β_std > 4.5`.

Sign data at `N = 6`, 6000 sweeps, 50 bins, 60 pairs (`data/yang_mills_twisted_cross_sign_2026_10_31.json`):

| `β_std` | opposite, time | opposite, twist plane | other planes | negative pairs | worst `z` |
|---|---|---|---|---|---|
| 0.5 | 0.00011 ± 0.00007 | 0.00001 ± 0.00008 | 0.00015 ± 0.00003 | 10 | -1.27 |
| 1 | 0.00006 ± 0.00006 | 0.00006 ± 0.00006 | 0.00242 ± 0.00003 | 3 | -1.46 |
| 1.5 | 0.00074 ± 0.00007 | 0.00066 ± 0.00006 | 0.0107 ± 0.00003 | 0 | 2.45 |
| 2 | 0.00714 ± 0.00006 | 0.00713 ± 0.00006 | 0.0329 ± 0.00005 | 0 | 51.7 |

No pair is significantly negative. The opposite terms at `β_std ≤ 1` are consistent with zero, and a hand expansion gives a cancellation at order `β²`. The other-plane column is a rounded mean of two classes. This does not prove the sign for different planes.

## Modules added 2026-10-31 (proved in Lean unless marked; nothing here is uniform on a physical trajectory)

All twelve Clay requirements, all four Target A items and Milestone A0 stay open. Each module went through attack, skeptic, repair and a second skeptic. Check: `lake env lean scripts/CheckYangMillsTwistedSwarm.lean`, which walks every declaration. None of them is imported by the root.

| Module | Holds up | Known defects, unfixed unless stated |
|---|---|---|
| `TwistedNeutral` | For `β > 0`, `T` is injective on gauge-invariant vectors, all eight flux sectors have a positive top eigenvalue, and a first excited neutral level exists (`neutral_level`, `exists_neutralWindow`). `chainLaw` gives the law at any `T`, reflection positive at even `T`. | The header says no quantitative bound exists. A scratch derivation from `gap_explicit` gives `neutralLevel ≤ 1 - exp(-72βn³)`, useless at large `β`. `TargetAGap` is joint in `n` and `β`, not only uniformity in `n`. |
| `TwistedTraceLaw` | Slice observables as operator traces under the actual law. | `law_connected_of_targetAGap` beats the Cauchy-Schwarz bound at no known point with `T = L`. |
| `TwistedSemiclassical` | Free many-mode spectral theorem (`free_spectral`), `haar_gnomonic`, `pi_near`, `offError_le_of_budget`. | `valleyGap_explicit` and `valleyGap_at_threshold` have no gap content, since their level holds with no orthogonality constraint. `integral_frame` has an undischarged lower bound on `frameWeight`. `ValleyGap` against `η` is essentially the conclusion, and `ValleyChart` has no instance. |
| `TwistedCovarianceDecay` | Pointwise bounds free of `L` and `N` at small-defect backgrounds (`cov_decay_unif`, `hess_decay_unif`), and the discrete Sobolev inequality. | A linear form at a fixed background, not the measure. The rate comes from a hand-added penalty, and the bound says nothing below `d ≈ 22L` or `69L`. At `d ~ L` it is about `1200 L²` above the flat-field value. |
| `TwistedFlow` | The Wilson flow exists globally, with covariance, energy and Bochner identities. `force_static`, `flow_locality`, decay below `S ≤ (1408 N⁵)⁻²`. | `law_action_wf_decay_from` assumes what it needs. The claim in its numerics that local Metropolis does not leave the sector is wrong. |
| `TwistedLocalTail` | Translation up to center flips, and a second-moment bound per plaquette with no volume factor. | `energy_ge` is vacuous. The tail is Chebyshev only, so a union over plaquettes still costs `N⁴`. |
| `TwistedBlockStep` | The blocked law as a push-forward, exact gauge covariance, exact descent of the twist, reflection positivity on the closed half for maps with no time staples. | No map has everything: see the synthesis. Tails are empty below explicit volume-dependent thresholds. |
| `TwistedBridge` | `BoxCriterionOn` implies mixing and covariance decay, conditionally. It holds at strong coupling. | `star_no_go` is worst case over boundaries, including ones of very low weight, so it does not bear on typical boundaries. No bridge from small to large volume exists. |
| `TwistedLimit` | Compactness and reflection positivity of limits, and collapse to constants at `β → ∞` for plaquettes and slice-flowed labels. `link_floor`, a volume-free lower bound on the plaquette energy. | `SliceLoopConnected` has no separation condition and reduces to a variance. `polyakov_connected_tendsto` is about flip-odd unflowed loops, and does not establish a correction to Target A item 2. |

`scripts/yang_mills_twisted_spectrum_probe.c` has a phase one site off, confirmed by review. The table above was only retested at `N = 8`, `β_std = 64`, one-gluon channel, so its values at `β_std = 32` and `N = 6` are suspect until rerun.

## Gap numerics (not proofs)

`scripts/yang_mills_target_a_gap_numerics.py`, `data/yang_mills_target_a_gap_2026_10_31.json`. On `T = 3L`, one `e₃` valley, `N ≤ 12`, the lowest fit values at `τ ≥ L/4` are about 5.8-6.4 at `u ≤ 1`, 5.4-5.6 at `u ≈ 2` and 4.4-4.65 at `u ≈ 3.4`. None of the failure criteria written before the runs fired, and operators now cover all 20 states of the tree-level multiplet. `N = 16` is too noisy to use. This is not an upper bound on `c(u)` in general, establishes no plateau, and gives no lower bound on any level.

`T = L` masses look low because neutral operators pick up a constant in time from flux states wrapping time. A constant-free estimator agrees with `T = 3L`, resolved only at `τ` of about 1-2.

## Scale-correlation recursion: closed (numerics, not proofs)

The idea was a one-variable recursion on `r(L)`, the correlation of separated flowed action-density blocks on the original measure, with `r(2L) ≤ F(r(L))`. Scripts `yang_mills_scale_corr_*`, `yang_mills_u1_photon_check.py`. Compact `U(1)` was the built-in control, since it has a massless phase. On `N = 32` at `β = 1.1`, `ρ(L) = r/r_free` is 1.03, 0.07, 0.00, -0.01 at `L = 1, 2, 4, 8`. There `G(k)` is flat from hot and cold starts, which supports a massless photon, though the confined control at `β = 0.9` separates less cleanly than wanted. The block variance is about 290 times free while the covariance is above free, so short-range noise in the denominator hides the long-range signal. Small `r` therefore does not imply a gap, and removing the normalization returns the plain two-point function, which is the original question. `F(r) < r` was also too weak on its face: a power law has `F(r) = r/16`.

## Crossover ideas under test (numerics, not proofs)

- `yang_mills_t2r2_gap.py`: the neutral gap with the twist on `T²(L)`, the other two directions `3L`, the setup of Tanizaki and Ünsal (arXiv:2201.06166), who conjecture continuity to `R⁴`. The control passes at `β_std = 32`, and the criterion written first did not fire: no `E/√σ` below 1. It has little power. Signal survives only to `τ ≈ 2`, values at `L√σ ≳ 1.5` show excited contamination rising with `L`, and masses are upper bounds. `√σ` values are recalled.
- `yang_mills_loop_bootstrap.py`: rigorous plaquette bounds from loop equations and positivity, as in Kazakov and Zheng (arXiv:2404.16925). The equations hold on Monte Carlo, after a bug that confused distinct links with the same direction. At `D = 4`, `β_std = 2.3` the bounds contain the Monte Carlo value but are wide: `[0, 0.849]` at length 12 and 14, with no gain from the longer equations. Positivity at path length 5 exceeds 1.5 GB without symmetry reduction, so the published reach is not reproduced here. A connected correlator would need a width far below its size.
- `yang_mills_twist_free_energy.py`: `z(L) = Z_twisted / Z`, with the Tomboulis-Yaffe bound on Wilson loops. It bounds Wilson loops, not the gap.

## Twist free energy result and the flux-sector recursion (2026-10-31)

`data/yang_mills_twist_free_energy_2026_10_31.json`. log z at L = 4, 6, 8. U(1) beta 1.5: -5.86, -5.88, -5.88. beta 1.1: -3.50, -3.52, -3.52. beta 0.9: -0.01, -0.01, +0.01. SU(2) beta_std 2.3: -0.80, -0.05, -0.05 (each ±0.11). beta_std 2.5: -1.98, -1.96, -1.06 (±0.11, 0.23, 0.29). The pre-registered kill did not fire. z separates the U(1) phases where r did not. The rise at 2.5 is about 2 sigma, and beta 0.9 is a weak control because it is already 0 at L = 4.

With time along direction 1, Z_tw = Tr(Omega T^t) for the periodic T and the center operator Omega. So y = (1-z)/(1+z) = Z_1/Z_0 is a ratio of sector traces of a positive operator, and y(2L1,2L2) <= K3 y(L1,L2)^4 with K3 = K1^2 K2 and K = Z_0(t)^2/Z_0(2t). This uses T >= 0 only, not reflection positivity of the twisted law, which fails in direction 1.

- `TwistedFluxRecursion` has the abstract inequalities (`sectorTrace_double`, `one_step`, `four_step`, `iterate_bound`). The link to the lattice traces is not formalized and is by hand. Not imported by root.
- `scripts/yang_mills_flux_recursion_2d.py` checks it on exact 2D SU(2) sums: 0 violations.
- Open: a uniform bound on K3 in L, and y below K3^(-1/3) at some L for every beta. The second is the crossover restated. The conclusion would be an area law through Tomboulis-Yaffe, not a gap.
- `scripts/yang_mills_flux_recursion_K.py` measures K3, data `data/yang_mills_flux_recursion_K_L{4,6}_2026_10_31.json`. log K3 at L = 4, then L = 6: beta_std 2.3: 3.34(64), 0.95(24). 2.4: 4.40(69), 2.39(40). 2.5: 5.16(70), 3.98(44). y on the base lattice, L = 4 then 6: 0.41, 0.02. 0.66, 0.35. 0.74, 0.69. Contraction (y < K3^(-1/3)) starts near beta_std 2.2-2.3 at L = 4 and near 2.4 at L = 6 (the latter about 1 sigma), which tracks the N_t deconfinement couplings. The pre-registered rule keeps the recursion alive. Errors are statistical. The 0.1 grid does not resolve the rise in the integrand and adds an unquantified systematic.
- **Defect in that test.** The inequality doubles L1 and L2 only. The next step of a chain starts from (L, 2L, 2L, L), so K3 at the isotropic base L = 6 is not the constant of any chain that starts at L = 4. Doubling L0 and L3 has no inequality: -log z(2t) = -2 log z(t) + log K_tw - log K_per is an identity, with K_tw the same ratio for Z_tw, and using it needs K_tw/K_per = 1 to the precision of y. Nothing here bounds that. At fixed L0, L3 the chain gives at most decay at fixed transverse size, not an infinite-volume area law. The numbers do not establish a recursion on L^4.
- Not compared against the step Ito and Seiler dispute in Tomboulis 0707.2179.

## Fixed-n inputs (2026-11-01)

`TwistedFixedN`: `frameWeight_lower` (frame weight at least `ballMass ε₁` for fields within `ε` of a rotated reference, `ε + 2ε₁ < √2`, free of `β` and `n`), `integral_tree_chart_of_close` (the chart identity with closeness in place of the frame-weight hypothesis), `energy_no_log`. Axioms: propext, Classical.choice, Quot.sound. Not imported by root and not in the swarm audit script. Closeness on the valley in tree gauge is not proved, so the chart identity is still conditional. No limit of `neutralLevel` follows.

## Valley chart (2026-11-02)

`TwistedValleyChart.lean` (Lean, standard axioms only; not imported by the root file or covered by the audit script):
- `slice_near_flat`: a slice with twisted potential at most `ε²` is, after a slice gauge and possibly the center flip, within
  `11 · scale n ε` of the flat slice on every link. This applies `axial_near_flat` to the static lift.
- `treeGauge_close`, `treeGauge_gauge`: the coordinate-tree gauge is Lipschitz with constant `6n + 1`, and a gauge
  transformation acts on it as one global rotation.
- `valley_close`: on `valley n σ` with `√σ ≤ 1/(308 n³)`, the off-tree links in tree gauge are within `1/2` of one
  rotated reference, the flat slice in tree gauge. `holo > 0` excludes the flipped class.
- `integral_valley_chart`: the chart identity `integral_tree_chart` for gauge-invariant functions supported in that
  valley, with no open hypothesis.

Limits: fixed `n` only. The valley size `σ ~ n⁻⁶` is far below the `1/(16 n⁴)` used by `kernel_off`, so the chart covers
a smaller valley than the gap reduction uses. The frame directions remain in the coordinates, and the kernel has not
been evaluated. This does nothing for the trajectory `β ~ log n`.

## Sharp top level at fixed n (2026-11-02)

`TwistedNormSharp.lean` (Lean, standard axioms only; not imported by the root file or covered by the audit script):
- `potential_shift`: `V(v) ≤ (1 + θ) V(u) + 16 (1 + θ⁻¹) Σ_e d(u_e, v_e)²`.
- `jensen_partition`: `Z(s) ≤ Z(s')^(s/s')` for `Z(s) = ∫ exp(-s V)`, by Hölder.
- `norm_lower_sharp`: the gauge-invariant trial function `exp(-aβV)` gives
  `mass(β(1 + (a + 1/2)·16(1 + θ⁻¹)))^links · (mass(16 s')^links)^η ≤ ‖T‖`, with `s' = (2a + 1 + θ(a + 1/2))β` and
  `η = (1 + θ(a + 1/2))/(2a + 1 + θ(a + 1/2))`.

Together with `norm_le_mass` (`‖T‖ ≤ mass(β)^links`) the exponent of the top level is pinned to `links` up to the factor
`1 + η`, and `η → 0` as `a → ∞` with `θ = 1/a`. Before this, the lower exponent was `2·links + sites = 7n³`, against
`links = 3n³` in the upper bound. The comparison with powers of `β` uses the scaling of `mass(s)` like `s^(-3/2)`, which
is not formalized here. The result concerns the top level at fixed `n` only, not the neutral level, and nothing in it is
uniform in `n`.

## Where the chart route can reach (2026-11-02, by hand, not formalized)

`ValleyChart` asks for a pointwise relative kernel bound `|Kt - c K₀| ≤ δ c K₀`, with `δ` below the free gap `r` of
order `1/n` (`free_gap_lattice`). Two requirements pull against each other:
- `offError ≤ ε ‖T‖` needs `β σ / 2` above the logarithm of `1/‖T‖`. Even with `norm_lower_sharp` that is of order
  `n³ log β`, so `σ ≳ n³ log β / β`.
- On a valley of level `σ` the field deviations reach `|x| ~ √σ`, and the ratio `Kt / c K₀` contains
  `exp(-β (V - V₂))`, where `V₂` is the quadratic part of the potential and `V - V₂` is cubic. So `δ ≳ β σ^(3/2)` at
  best. The valley-to-tree-gauge bound actually proved (`valley_close`) loses a further `n³` in `|x|`.

Together: `δ ≳ (n³ log β)^(3/2) / β^(1/2)`, and `δ ≲ 1/n` needs `β ≳ n¹¹ log³ β`. So the chart route is a statement
about `β` polynomially large in `n`. It cannot reach the trajectory `β ~ log n`, whatever the chart. That matches the
physics: at `β ~ log n` the long modes are not Gaussian, and a single-valley Gaussian comparison cannot see the running
coupling. Finishing the fixed-`n` limit (frame slice, Faddeev-Popov Jacobian, cubic kernel bound) would formalize known
semiclassics. It would not advance step 4 as stated in `BEST_ATTEMPT.md`.

## Preconditioned convexity for step 4 (2026-11-02, numerics, negative)

Idea: get the 1/n gap without a multi-scale flow from a Helffer-Sjöstrand / Brascamp-Lieb covariance bound. That
needs a lemma L1: `Hess U + Ric ≥ c β_std Δ₀` on horizontal directions, at typical configurations. Here `Δ₀` is the twisted
flat Hodge Laplacian, lowest eigenvalue `4 sin²(π/2n)`, so Combes-Thomas decay at rate about `1/n`, and `Ric = 2` per link
(SU(2) = unit S³). The deviation is critical in 4D, of order `g √log n` or `g² log n` by power counting. That is small
on `β = b log n`, the TargetAGap regime. A separate large-field lemma L2 would also be needed; it was not tested.

Test: `scripts/yang_mills_preconditioned_hessian.py`. It computes the smallest generalized eigenvalue `λ` of
`Hess U + K β_std D D^T (+ 2I)` against `β_std Δ₀`. Configurations are heatbath SU(2) with twist, in background Landau
gauge to a cooled flat vacuum, best of four center sectors. `K → ∞` restricts to horizontal directions and has converged
by `K = 100`. The Hessian matches finite differences, and the bug check (`λ = 1 + 2/(β_std λ_max(Δ₀))` at the vacuum)
holds to 1e-7 at n = 4, 6, 8. Predictions were written before the runs.

Horizontal (`K = 100`), one or two configurations per point:

| β_std | n | λ | λ without Ric |
|---|---|---|---|
| 16 | 4 | 0.195 | 0.064 |
| 16 | 6 | 0.061 | -0.187 |
| 16 | 8 | -0.120 | -0.504 |
| 8 | 6 | -0.239 | -0.666 |
| 8 | 8 | -0.447 | -1.031 |

With `K = 1` (n = 4, 6, 8):
- 1 − λ, without the Ricci term, is about `3.5/√β_std` at n = 4 (β_std = 8 to 64).
- At fixed β_std it grows by a factor of about 1.3 per step from n = 4 to 6 to 8.
- That fits roughly `n^0.65`. The 6 → 8 step is faster than the factor of 1.16 that `log n` would give.

At n = 4 and 6 the minimizing direction is long-wavelength and spread out:
- Its `Δ₀` value is within a factor of 2 of the bottom of the band.
- Its participation ratio is about 0.82.
- Its absolute Hessian value is negative, and grows in size with n.

So the bare action at a typical configuration has collective long-wavelength directions of negative curvature. The
cause is lattice-scale fluctuations adding up coherently on the long modes. No preconditioner can repair that, because it
is the sign of `Hess U` itself.

Verdict: L1 fails. At the measured growth it holds only for `β ≳ n^(1.2-1.6)`. That is polynomial, like the chart route
(`n¹¹`) but much milder, and not `log n`. Convexity at the long scales belongs to the effective action after the short
modes are integrated out, not to the bare action. So this route returns to a renormalization step. It is closed for step
4 as stated.

### Convexity scale (2026-11-02, numerics)

`scripts/yang_mills_convexity_scale.py` repeats the test above with fluctuations restricted to blocks of side `l`
(Dirichlet), on one n = 8 configuration per coupling, minimized over 3 blocks. It is horizontal (`K = 100`) and has no
Ricci term. The 20 points cover l = 2-5 and β_std = 8-128. For β_std ≥ 32 they fit

`1 - λ ≈ 0.41 · l^0.92 · β_std^(-0.51)` (rms 1.7% in log), that is, `1 - λ ∝ l g`.

So the bare action is convex in the preconditioned sense (λ ≥ 1/2) only on blocks up to `l* ≈ 1.2 √β_std`, about 1/g in
lattice units. On `β ~ b log n` that is `l* ~ √log n`. Any multiscale convexity scheme, such as a Polchinski flow with
Bakry-Émery at each scale, could start from bare convexity at `l*`. It must still carry the effective action from `l*`
to `n`, which is nearly all of the `log n` scales. The pointwise softening grows like `l g`, a power law, while the true
running of the coupling is logarithmic. A pointwise Hessian cannot track that running. Only the averaged one can:
`E[Hess U | coarse] - Cov(∇U | coarse)` for the coarse marginal.

### Averaged long-wavelength stiffness (2026-11-02, numerics)

`scripts/yang_mills_ir_stiffness.py` measures `r = β_std q Var⟨v, a⟩` on the lowest horizontal Δ₀ modes. Here
`a = log(U V⁻¹)` is the gauge field in background Landau gauge, the modes form a 12-fold degenerate group, and the free
field has r = 1. If the coarse marginal is convex (`Hess U_eff ≥ c β Δ₀`), Brascamp-Lieb gives `r ≤ 1/c`. Calibration:
r = 1.05 ± 0.08 at β_std = 128, n = 4.

| β_std | n = 4 | n = 6 | n = 8 |
|---|---|---|---|
| 8  | 1.20 ± 0.08 | 1.22 ± 0.08 | 0.98 ± 0.08 |
| 16 | 1.07 ± 0.07 | 1.10 ± 0.07 | 1.11 ± 0.09 |
| 32 | 1.08 ± 0.07 | 1.08 ± 0.07 | 1.03 ± 0.09 |

(40 configurations at n = 4, 6 and 24 at n = 8, 20 updates apart. The errors ignore autocorrelation.)

r is flat in n within errors. Over the same range, the pointwise preconditioned Hessian went from λ ≈ 0 to λ ≈ -0.5. So
the averaged long-wavelength stiffness is that of a free field, to about 10%. Only the pointwise Hessian is soft at long
wavelengths. This is consistent with a convex coarse marginal, the hypothesis of a multiscale Bakry-Émery / Polchinski
scheme. It is only a necessary condition, and it does not test convexity of `U_eff` at non-typical coarse fields.

Where step 4 now stands. Pointwise convexity holds up to `l* ~ 1/g`, and the averaged stiffness is free-like at every
scale tested. What is missing is a theorem carrying convexity of the coarse marginal from `l*` to `n`. That would be a
gauge-covariant version of the Bauerschmidt-Bodineau multiscale Bakry-Émery criterion, with the large-field region
handled at each scale. I know of no such result.

### Large fields along the lowest mode (2026-11-02, numerics, classical)

`scripts/yang_mills_mode_barrier.py` computes `S_min(t)`: the action `Σ_p (1 - z P0)` minimized over `U = exp(a) V`,
with `a` in the linear background Landau slice `D_Vᵀ a = 0` and `⟨v, a⟩ = t/√q` for the lowest horizontal Δ₀ mode `v`.
The weight is `exp(-β_std S)`, and the free value is `t²/2`. L-BFGS with autograd, warm-started along t.

| t | n = 4 | n = 6 | n = 8 | free |
|---|---|---|---|---|
| 1 | 0.486 | 0.490 | 0.487 | 0.5 |
| 2 | 1.77 | 1.83 | 1.79 | 2 |
| 3 | 3.33 | 3.60 | 3.44 | 4.5 |
| 4 | 4.49 | 4.84 | 4.65 | 8 |
| max before the drop | 4.92 (t = 5.5) | ≥ 4.84 | 4.89 (t = 4.5) | |

- The profile is n-independent to a few percent: the classical action is scale invariant.
- Convexity in t fails at `t ≈ 2.5`, where `S ≈ 2.6`.
- At `t ≈ 5`, S drops to 0: the path reaches another flat vacuum in the slice, a center copy or a Gribov copy. The
  barrier along the mode is about 4.9.
- In the center quotient used for the neutral sector, these are copies of the same vacuum, so this is wrapping, not
  metastability.

Consequence, classical only (no entropy, no running coupling). The non-convex large-field region of the coarse mode is
suppressed by about `exp(-2.6 β_std)`. On `β_std = b' log n` that is `n^(-2.6 b')`, below the 1/n accuracy TargetAGap
needs once `b' > 0.4`. This is the mechanism by which the `b log n` in TargetAGap could control coarse large fields. One
mode was studied. A proof needs every coarse mode, the entropy factor, and the effective rather than the bare coupling.

### Cheapest large-field direction (2026-11-02, numerics, classical)

`scripts/yang_mills_sphere_barrier.py` minimizes the action on energy spheres `⟨a, Δ₀ a⟩ = R²` in the Landau slice, over
all directions (best of 3 random starts, warm-started in R). The free value is `R²/2`.

| R | n = 4 | n = 6 | n = 8 |
|---|---|---|---|
| 1 | 0.420 | 0.418 | 0.417 |
| 3 | 2.52 | 2.50 | 2.49 |
| 5 | 4.32 | 4.30 | 4.29 |
| 6 | 4.75 | 4.75 | 4.74 |

- n-independent to 1%.
- The minimizer is collective (participation ratio about 0.91), and `max|a|·n` is constant.
- At R = 1 it sits 16% below free: the cubic term, set by `|a| n`, which is scale invariant.
- Convexity in R ends near S ≈ 2.5. The barrier is about 4.75 (between R = 6 and 8), and then the path descends to
  another vacuum copy.
- No lattice-scale lump below that was found up to R = 12. The search was limited to 3 random starts.

Comparison with Lean: `near_flat_coercive` needs `actionL ≤ (1/(1408 (2n)⁵))²`, about `n⁻¹⁰`. The true coercive region
is `S ≲ 2.5`, uniform in n. A scale-invariant version would follow from:
- (i) In the Landau slice, `S ≥ E/2 - C E^(3/2)`. This uses the 4D lattice Sobolev bound `‖a‖₄ ≤ C ⟨a, Δ₀ a⟩^(1/2)`,
  uniform in n because the twist removes zero modes.
- (ii) A lattice Uhlenbeck gauge: action below an n-independent `ε₀` gives a Landau gauge with `E ≤ C S`.
(ii) is the hard part.

### Lattice Uhlenbeck gauge, uniformity in n (2026-11-02, numerics)

`scripts/yang_mills_uhlenbeck_test.py` cools heatbath configurations (β_std = 8) step by step. Whenever the action
`S < 3`, it gauge-fixes to background Landau (best center sector) and records `E = ⟨a, Δ₀ a⟩`, where E = 2S at linear
order. The largest E/S observed:

| S range | n = 4 | n = 6 | n = 8 (2 paths, 60 points) |
|---|---|---|---|
| 0-0.25 | 2.12 | 2.07 | |
| 0.25-1 | 2.36 | 2.10 | |
| 1-3 | 2.41 | 2.10 | |
| all | | | 2.11 |

The ratio does not grow with n, and it moves toward the linear value 2. This supports claim (ii) (small action gives a
Landau gauge with `E ≤ C S`, `C ≈ 2.5`, uniform in n) on cooling paths. Cooling paths are a special family: worst-case
small-action configurations, for example thin vortices, were not searched. Together with (i), this indicates a
scale-invariant classical coercivity, `S ≥ c E` for `S ≲ 2.5`, uniform in n. That is n¹⁰ better than the hypothesis of
`near_flat_coercive`.

### Plaquette value bound in Lean (2026-11-02)

`TwistedPlaquetteValue.lean` uses only the standard axioms and has no sorry:
- `plaquette_value_lower`: for imaginary quaternions `A B C D` with `s = Σ‖·‖ ≤ 1/2`,
  `((‖A+B+C+D‖ − 5 s²)₊)² / 2 ≤ 1 − Re(e^A e^B e^C e^D)`. It goes via `1 − Re q = ‖q − 1‖²/2` for unit `q` and
  `‖e^A e^B e^C e^D − 1 − (A+B+C+D)‖ ≤ 5 s²` (`exp_four_le`). There is no logarithm and no BCH series.
- `sum_value_lower`: over any finite family of plaquettes,
  `(1−δ)/2 · Σ ‖c_p‖² − 25/(2δ) · Σ s_p⁴ ≤ Σ (1 − Re P_p)`.

This is the per-plaquette core of the scale-invariant coercivity in `COERCIVITY_SCALE_INVARIANT.md`. With
`U = exp(a) V`, it gives `S ≥ (1−δ)/2 · ‖d_V a‖² − (25·384/(2δ)) ‖a‖₄⁴`. A discrete Sobolev bound then makes this
`S ≥ c₁E − c₂E²` uniformly in n. Unlike `near_flat_coercive`, it needs only `max |a_e| ≤ 1/8`, a pointwise bound
independent of n, and not closeness at scale `n⁻⁵`. Still missing in Lean:
- the link to the lattice types (`Section`, `flatLink`, the twist sign `z_p`);
- the discrete Sobolev inequality (S1);
- the Landau slice.

### Constant-flux saddle (2026-11-02)

`scripts/yang_mills_constant_flux.py` builds the lattice 't Hooft constant-curvature configuration in the twisted box.
- **Construction.** Links are abelian, `U = exp(iσ₃θ)`. Every twisted (1,2)-plaquette has `z P = exp(iσ₃ π/n²)`: the
  plaquette angles in a (1,2)-plane add to 0 mod 2π, and the twist supplies the missing π, spread evenly.
- **Critical point.** It is an exact critical point of the SU(2) action, since abelian with `d*F = 0` implies the gradient
  vanishes in the off-diagonal directions.
- **Action.** `S = n⁴(1 − cos(π/n²)) → π²/2 = 4.935`, n-independent.

| n | S | `‖∇S‖` | negative eigenvalues | `n²·|λ₋|` | horizontal zeros |
|---|---|---|---|---|---|
| 3 | 4.8849 | | −0.7496 (×2) | 6.75 | 4 |
| 4 | 4.9190 | 6e-15 | −0.41034 (×2) | 6.565 | 4 |
| 6 | 4.9317 | 9e-15 | −0.17820 (×2) | 6.415 | 4 |
| 8 | 4.9338 | 1.5e-14 | −0.099355 (×2) | 6.359 | 4 |

The n = 3 and n = 4 rows are dense full spectra. The n = 6 and n = 8 rows use shift-invert on `H + DDᵀ`, which leaves the
horizontal spectrum unchanged at a critical point.

- **Morse index exactly 2.** The two negative modes are the lowest Landau level of the charged (W) fluctuation in the field
  `f = 2π/n²`. That level has eigenvalue `f − 2f = −f` and is twofold, since the charged field is complex and sees one
  flux quantum. Extrapolating n = 6, 8 in `1/n²` gives `n²|λ₋| → 6.286`, against 2π = 6.283.
- **Zero modes.** They are the gauge orbit (`3n⁴ − 1`, since the stabilizer is U(1)) plus 4 abelian holonomy moduli.
- **Connection between vacua.** Sliding the θ₀ and θ₃ moduli turns the Polyakov loops in those directions from +1 to −1
  at constant action. So the saddle joins the four center-related vacua (`c₀, c₃ = ±1`).

Consequences:
- **Upper bound on the action gap.** (ii') can hold only with `ε₀ < n⁴(1 − cos(π/n²)) < π²/2`. Numerics put the true
  lowest non-vacuum critical value between 4.75 (sphere barrier, not itself a critical value) and 4.935. Whether an
  index-1 saddle lies below this one is open.
- **Continuum Weitzenböck arguments fail on T⁴.** The Bourguignon-Lawson energy-gap argument
  (`0 = ‖∇_A F‖² + ⟨F, [F, F]⟩`) is blind here, because `∇_A F = 0` and `[F, F] = 0` for this solution. A proof of (ii')
  must therefore be quantitative, comparing the action with π²/2. It cannot be a pure smallness argument.
- **Large-field weight.** The saddle's weight is `exp(−β_std π²/2)` times a polynomial from the compact moduli. On
  `β_std = b' log n` that is `n^(−4.93 b′)`, the same order as the barrier exponent already in `BEST_ATTEMPT.md`.

## The neutral window as a two-sided Poincaré statement (2026-11-02, Lean)

`TwistedSlowObservable.lean` (axioms propext, Classical.choice, Quot.sound; no sorry; not imported by root):
- `slow_lower`: if `g` is continuous and flip invariant, has mean zero and positive variance under `η²`, and its
  Dirichlet form satisfies `dirichlet η g ≤ 2(1 − ρ) ‖T‖ E[g²]`, then `g η` is a nonzero neutral vector orthogonal to the
  vacuum with `‖T(gη)‖ ≥ ρ ‖T‖ ‖gη‖`. The proof uses the ground-state identity, then Cauchy-Schwarz.
- `window_of_two_sided`: `NeutralPoincare η (n/c)` together with one such `g` for `ρ = e^{−C/n}` gives
  `NeutralWindow n β (e^{−c/n}) (e^{−C/n})`.

So `TargetAGap b` follows from two inequalities, uniform over `n ≥ 2` and `β ≥ b log n + β₀`. Both are about the
stationary chain of consecutive time slices `(u₀, u₁)` of the twisted Euclidean measure, with marginal `η²`:
- **(P) Poincaré, every neutral observable:** `E[(g(u₁) − g(u₀))²] ≥ (2c/n) Var g`. Open; this is the hard half.
- **(S) One slow neutral observable:** `E[(g(u₁) − g(u₀))²] ≤ 2(1 − e^{−C/n}) Var g`.

Both are statements about the measure alone, with no operator theory left. (S) is the easier half, since a trial
function suffices. The natural trial is a gradient-flowed, flip-invariant observable at flow time of order `n²`,
built from a lowest twisted mode. For it, (S) splits into two parts:
- a **kinetic increment bound**, `E[(Δ_t g)²] ≲ E|∇g|²/β`;
- a **variance lower bound**, `Var g ≳ n E|∇g|²/β`. By the inverse Poincaré inequality, this is
  `Var g ≥ (E|∇g|²)² / E[Γ₂(g)]` with `Γ₂ = ‖∇²g‖² + (Ric + β Hess S)(∇g, ∇g)`.

The variance lower bound needs only an upper bound on the averaged Hessian along `∇g`. There, the long-wavelength
softness of the bare Hessian found above helps rather than hurts. The obstacle is the UV part. Pointwise, the commutator
terms in `Hess S(∇g, ∇g)` are of order `g ‖∇g‖²` against a free value of order `‖∇g‖²/n²`. They cancel only on
average, by the Ward identity (no gluon mass). None of this is proved.

### Kinetic increment bound by Gaussian domination in time (2026-11-02, by hand, not formalized)

This is the first half of (S), proved by hand for every `n` and `β`, with no convexity assumption.

**Setup.** Write `K₀(u, v) = wt(u) exp(−β Σ_e |u_e − v_e|²) wt(v)`, the twisted kernel before the temporal Haar
average. `kinetic_term` gives `2 − Re χ(a⁻¹b) = |a − b|²` in the `R⁴` embedding of SU(2). Then
`K(u, v) = ∫ dh K₀(u, h·v)` (`twistedKernel_eq`, `temporalAction_eq`).
1. **Gauge-invariant observables see `K₀`** (in Lean as `avg_integral_invariant`, `TwistedSemiclassical`, with `kinW` the
   kernel without the temporal average). For gauge-invariant `g`, `η`, the substitution `v → h⁻¹v` (Haar
   invariance, `wt_gauge`) gives `K₀ η = ‖T‖ η` and `dirichlet_K η g = dirichlet_{K₀} η g`. `K₀` is a positive kernel and
   `η > 0`, so `η` is its Perron eigenfunction. So (S) concerns the temporal-gauge chain `(u₀, u₁)` with transition
   `K₀ η / (‖T‖ η)` and stationary law `η²`.
2. **That chain has a Gaussian time coupling.**
   - `|u|² = #links` is constant on the group, so `exp(−β|u_t − u_{t+1}|²) ∝ exp(2β u_t·u_{t+1})`. That is a ferromagnetic
     quadratic coupling of the slice vectors `σ_t ∈ (R⁴)^links`, with arbitrary single-slice weight `wt²`.
   - On a periodic chain of even length, Fröhlich-Simon-Spencer Gaussian domination gives `Z(h) ≤ Z(0)` for every bond
     field `h`, by reflection positivity in bond planes.
   - With `h` on one bond, let the length go to infinity, which is valid at fixed `n` because the Perron eigenvalue is
     simple. Expanding to second order, with `E Δ = 0` by stationarity:
     **`E exp(2β h·(u₁ − u₀)) ≤ exp(β|h|²)`, hence `E[(h·(u₁ − u₀))²] ≤ |h|²/(2β)`,**
     for every deterministic `h ∈ (R⁴)^links`.

This is the kinetic bound `E[(Δ_t g)²] ≲ |∇g|²/β`, exactly, uniform in `n`, but only for observables linear in
temporal-gauge coordinates. Those are not gauge invariant.

**Remaining gap.** A gauge-invariant `g` linearizes to `∇g(u₀)·Δ`, whose direction is random. The natural choice is a
Landau-gauge linear functional, `g(u) = ⟨w, Ω*(u)u⟩` with `w` transverse and slow. Its gauge-fixing correction is first
order in `d*w = 0`, so `Δg ≈ ⟨Ω*(u₀)ᵀ w, Δ⟩`, with a direction measurable in `u₀`. Gaussian domination does not cover
such directions. A conditional version, `Cov(u₁ | u₀) ≲ 1/β` in slow directions, would need the conditional law
`∝ e^{−β|u₀−v|²} wt(v) η(v)` to be log-concave up to `o(β)` in those directions. The kinetic factor supplies curvature `2β`,
far more than the measured long-wavelength softness of `V` (about `β n^0.65 / (√β n²)`). But `η` enters, and a naive
bootstrap of `Hess log η` (`η = wt · (e^{−β|·|²} ∗ wt η) / ‖T‖`) has no fixed point once `V` is non-convex anywhere. Large
fields therefore have to be cut off first. This is open.

### Even-odd reduction of the kinetic half for gauge-invariant observables (2026-11-02, by hand)

This removes the configuration-dependent direction problem of the previous section. Work in the `K₀` chain
`(u₀, u₁, u₂)`, which is stationary and reversible.

**Fact 1: the middle slice has an explicit law.** Given its two neighbours, the middle slice has law
`ν_{u₀,u₂}(du) ∝ exp(2β u·(u₀ + u₂)) wt(u)² du`, because the three-slice density is `η(u₀) K₀(u₀,u₁) K₀(u₁,u₂) η(u₂)`.
The ground state `η` drops out. Per link the kinetic factor is a von Mises-Fisher weight centred at the geodesic
midpoint `ŵ_e = (u₀ₑ + u₂ₑ)/|u₀ₑ + u₂ₑ|`, with sphere Hessian `2β (u·(u₀+u₂)) ≈ 4β`. The Bakry-Émery curvature of `ν` is
therefore `4β + 2 (Ric) + β Hess V`.
- On the event that all plaquettes of `u₀, u₂` lie within `δ` of 1 and that `|u₀ₑ − u₂ₑ| ≤ δ`, this is at least
  `β(4 − Cδ)`. Restricting `ν` to the product of geodesic balls of radius `r` around `ŵ` keeps it geodesically convex.
- The event has probability at least `1 − n⁴ e^{−cβδ²}`, which is `1 − n^{4 − c b δ²}` on the trajectory.
- The mass of `ν` outside the balls is at most `n³ e^{−cβr²}`.

Brascamp-Lieb then gives the conditional variance bound
**`A := E Var_ν(g) ≤ E|∇g|² / ((4 − Cδ) β)`, up to these exponentially small corrections.** The bound is gauge
invariant, because `|∇g|` is.

**Fact 2: a spectral inequality.** `K₀` is a positive operator, so `1 − a² ≤ 2(1 − a)` on its spectrum, and
`D₂ ≤ 2 D₁` with `D_k = E(g(u_k) − g(u₀))²`.

**Reduction.** Let `M = E[g(u₁) | u₀, u₂]` and let `R = M − ½(g(u₀) + g(u₂))` be the midpoint defect.
- Then `D₁ = A + E(M − g₀)²`, and `E(M − g₀)² ≤ (3/2)·D₂/4 + 3 E R²`.
- With Fact 2:
  **`D₁ ≤ 4A + 12 E R²`.**

**Free-field check.** For an AR(1) mode with `a = e^{−ω}`, `R = −(g₀+g₂)(1−a)²/(2(1+a²))`, so `E R² ~ ω³/β`, while
`A ~ 1/β`. The bound is consistent with the target `D₁ ≲ 1/β`.

**What is left of the kinetic half: (K2), the midpoint-force bound** `E R² ≲ E|∇g|²/β` for the slow trial `g`. By
Taylor expansion around `ŵ`, `R` equals the `ν`-averaged force on `g`, `−¼ ∂_{∇g}V`, plus `O(‖∇²g‖ (|u₂ − u₀|² + 1/β))`.
- An integration by parts under `ν` bounds the full force: `E_ν[(∂_{∇g}W)²] ≤ E_ν[Hess W(∇g, ∇g)]/β` plus lower-order
  terms. Here `W` includes the kinetic part, so only the crude bound `Hess V ≤ C` is needed, and the UV problem does not
  appear.
- But that bounds the force with its kinetic part, `∂_{∇g}V − 2∇g·(u₀ + u₂ − 2u)`. Separating out the potential part
  needs `E[(E_ν ∂_{∇g}V)²] ≤ C E|∇g|²/β`, with any `C` independent of `n`. (Correction, 2026-11-02: an earlier version
  of this line asked for the free value `ω³ Var g`, which is far more than the reduction uses.) The crude Cauchy-Schwarz
  bound `|∂_{∇g}V| ≤ ‖curl_U ∇g‖ ‖Im P‖` gives only `C ~ n`. The missing factor is the decorrelation of field strengths
  along a slow covariant direction. Open; numerics in the next section.

### Slow-force numerics for (K2) (2026-11-02, numerics, not a proof)

`scripts/yang_mills_slow_force.py`, data `data/yang_mills_slow_force{,_seed1,_n10}_2026_11_02.json`.
- **Observable.** `g = Σ_x cos(2πx₃/n) s(x)`, with `s` the slice plaquette density after 3D Wilson flow to
  `t = n²/32`. It is gauge invariant and flip invariant.
- **Measured.** `F = ⟨∇g, ∇S₃⟩` on time slices of the 4D twisted heatbath, and
  `r = β_std E[F²] / E|∇g|²`. Since `E[F²] ≥ E[(E_ν F)²]`, this is conservative for (K2).

| β_std | n = 4 | n = 6 | n = 8 | n = 10 |
|---|---|---|---|---|
| 8   | 3.31 ± 1.23 | 1.32 ± 0.30 | 0.45 ± 0.06 | 0.21 ± 0.05 |
| 16  | 2.96 ± 0.63 | 0.88 ± 0.18 | 0.26 ± 0.05 (seed 1) | |
| 32  | 3.14 ± 0.58 | 1.05 ± 0.20 | 0.42 ± 0.07 | 0.21 ± 0.04 |
| 128 | 3.00 ± 0.72 | 0.76 ± 0.15 | 0.47 ± 0.08 | |

The first seed at n = 8, β_std = 16 gave 2.4 ± 2.1, from a heavy-tailed sample. Its raw samples were not saved; the
rerun with seed 1 is shown. Errors ignore autocorrelation.

- **Scaling.** `r·n²` goes 48-53, 27-48, 17-30, 21 at n = 4, 6, 8, 10. So `r` falls at least as fast as `1/n²`, with no
  β dependence. The kill criterion (growth of `r` with n) did not fire. The prediction `r ≤ 1` failed at n = 4
  (`r ≈ 3`), which is harmless, since (K2) allows any n-independent constant.
- **Comparison.** The crude Cauchy-Schwarz bound allows `r ~ n`, so the slow force decorrelates by about `n³` better
  than it. This supports (K2) and hence the kinetic half of (S), `D₁ ≲ E|∇g|²/β`.
- **What is still unproved.** The variance lower bound `Var g ≳ n E|∇g|²/β` (the other half of (S)) and (P).

### Variance half of (S), and (S) at long lag (2026-11-03)

**Numerics** (`scripts/yang_mills_slow_variance.py`, data `data/yang_mills_slow_variance_2026_11_03.json`; numerics,
not a proof). Same `g` as above, evaluated on every time slice of 40 heatbath configurations. Here `q = β_std Var g /
E|∇g|²` (the reduction needs `q ≳ n`), and `ρ₁` is the lag-one Euclidean autocorrelation of `g`.

| β_std | quantity | n = 4 | n = 6 | n = 8 | n = 10 |
|---|---|---|---|---|---|
| 8   | q/n         | 0.046 | 0.036 | 0.054 | 0.049 |
| 8   | n(1 − ρ₁)   | 3.5 | 4.7 | 5.7 | 6.2 |
| 32  | q/n         | 0.044 | 0.041 | 0.049 | (frozen) |
| 32  | n(1 − ρ₁)   | 3.9 | 4.3 | 5.2 | (frozen) |
| 128 | q/n         | 0.037 | 0.040 | 0.036 | 0.045 |
| 128 | n(1 − ρ₁)   | 3.3 | 5.1 | 5.9 | 7.0 |

- **q/n is flat, at about 0.045.** So the variance lower bound `Var g ≳ n E|∇g|²/β` holds numerically, with no β
  dependence.
- **n(1 − ρ₁) is not settled.** It still rises at n = 10, and 1 − ρ₁ itself stays at 0.6-0.7. The data cannot tell a
  plateau (`c/n` with `c ≈ 7-10`) from a floor (`1 − ρ₁ → a ≈ 0.45`). At lag one, `g` is mostly fast content.
- **The frozen point.** At n = 10, β_std = 32, all 40 configurations carry the same `⟨g⟩ ≈ −0.14`, with `g(t)` peaked
  at t ≈ 0. A lump localized in t and x₃ (presumably a trapped fractional instanton) never moved. That is a failure of
  the heatbath to sample the measure, not a property of the measure, so the point is excluded.

**Lean.** `TwistedSlowObservable` adds three lemmas (axioms: propext, Classical.choice, Quot.sound):
- **`slow_lower_lag`.** Gives the lower half of `NeutralWindow` from `C(2k+1) ≥ ρ‖T‖ C(2k)` at one lag.
- **`slow_lower_corr`.** Gives it from `C(2k) ≥ (ρ‖T‖)^{2k} C(0)`. Here `C(t) = ⟨F, Tᵗ F⟩` for a neutral
  `F = gη ⊥ Ω`. The proof telescopes the step ratios `‖T^{j+1}F‖/‖TʲF‖`, so positivity of `T` is not needed.
- **`neutral_pow`, `orth_pow`, `inner_pow_pow`.** Helper lemmas.

So the lag-one condition in (S) can be dropped. The lower half of `NeutralWindow` with `ρ₂ = e^{−C/n}` follows from
one neutral observable whose normalized connected Euclidean correlator at lag `2k ≈ n` keeps a fixed fraction `δ` of
its variance (`C = log(1/δ)`). That is an O(1) statement with no small parameter. The fast part of `g`, which dominates
`1 − ρ₁` above, is irrelevant to it. The lower half of step 4 is now **a lower bound on one neutral correlator at
distance ≈ n**. The upper half (P) is the matching upper bound on all of them.

### A neutral correlator at lag ≈ n/3 (2026-11-03, numerics, not a proof)

`scripts/yang_mills_slow_polyakov.py`, data `data/yang_mills_slow_polyakov_2026_11_03.json`.

**Setup.**
- Time extent `L_t = 3n`, so that lags of order n see the vacuum and not the wraparound.
- Every chain starts from the flat twist-eating configuration: `U₁ = iσ₁` on `x₁ = 0`, `U₂ = iσ₂` on `x₂ = 0`.
- **Why the start matters.** `U = 1` is not a vacuum of the twisted action. From that cold start, chains at `L_t = 3n`
  trapped lumps localized in t and x₃ (`⟨g⟩ ≠ 0` in every configuration, variance about 100× too large). That run
  was discarded.
- **Observable.** `g = Σ_{x₂,x₃} P₁(x₂,x₃)²` (pooled with `P₂²`), where `P₁` is the trace of the straight line in twisted
  direction 1 of the 3D-flowed slice (`t = n²/32`). A flip in direction 1 changes the sign of every `P₁`, so `g` is
  neutral, and `P₁` is linear in the fluctuation around the traceless holonomy `iσ₁`.
- **Free prediction.** The lowest neutral pair has momenta `±π/n` along the antiperiodic direction, with energy `2π/n`.
- **Errors.** Blocked jackknife (blocks of 6 configurations) over 60 configurations.

| n | β_std | C(1)/C(0) | C(≈n/3)/C(0) | C(n/2)/C(0) |
|---|---|---|---|---|
| 6  | 8  | 0.39 ± 0.02 | 0.154 ± 0.038 (t=2) | 0.083 ± 0.039 |
| 6  | 32 | 0.32 ± 0.03 | 0.114 ± 0.028 (t=2) | 0.045 ± 0.026 |
| 8  | 8  | 0.44 ± 0.02 | 0.066 ± 0.013 (t=3) | 0.031 ± 0.013 |
| 8  | 32 | 0.44 ± 0.02 | 0.111 ± 0.030 (t=3) | 0.065 ± 0.029 |
| 10 | 8  | 0.53 ± 0.02 | 0.137 ± 0.025 (t=3) | 0.053 ± 0.019 |
| 10 | 32 | 0.53 ± 0.02 | 0.103 ± 0.033 (t=3) | 0.012 ± 0.025 |

- **C(≈n/3)/C(0) stays at 0.07-0.15 for n = 6-10 at both couplings, with no fall in n.** The kill criterion did not fire.
  Through `slow_lower_corr` this is the hypothesis with `δ ≈ 0.1` at `2k ≈ n/3`, which would give
  `ρ₂ ≈ δ^{3/n} ≈ e^{−7/n}`: the lower half of the window, at the order 1/n step 4 needs.
- **The late decay is about 2π/n.** Measured per step: about 1.0 at n = 6 and 0.5-0.75 at n = 8, against
  `2π/n` = 1.05 and 0.79.
- **C(1)/C(0) rises with n (0.39 → 0.53).** The weight shifts toward slow states as n grows, as predicted.
- **Lag n/2 is at the noise floor.** Long-lag tails go negative by 0.03-0.05, which is the sample-mean subtraction
  combined with Monte Carlo autocorrelation. So `C(n/2)` (0.01-0.08) is not resolved.
- **Status.** This supports, but does not prove, a uniform δ. The proof target is now one Euclidean inequality:
  `⟨g; g_t⟩ ≥ δ Var g` at `t = n/3` for this `g`, uniformly along `β ≥ b log n + β₀`. At small coupling this is a
  lower bound for a nearly Gaussian (perturbative) correlator around an isolated vacuum.

### Leading order of the correlator, exactly (2026-11-03)

`scripts/yang_mills_polyakov_free.py` evaluates the leading order by exact finite sums, with no sampling.
- **Free fields.** Around the twist-eating vacuum the quadratic action is three free lattice Maxwell fields. The color
  component `a¹` is periodic in 1, 3 and t, and antiperiodic in 2.
- **The observable at linear order.** `δP₁ ∝ Σ_{x₁} A¹₁`, which is linearized-gauge invariant. Wick's theorem gives
  `C(t)/C(0) = Σ_k G_k(t)² f_k / Σ_k G_k(0)² f_k`, with:
  - `G_k(t) = e^{−ω t}/(2 sinh ω)` and `2 cosh ω − 2 = k̂²`;
  - `k = (π(2m+1)/n, 2πm'/n)`;
  - flow factor `f_k = e^{−4 t_f k̂²}`.

  The ratio is independent of β.

| n | free C(1)/C(0) | free C(t*)/C(0) | free C(n/2)/C(0) | MC C(1)/C(0) (β_std 8, 32) | MC C(t*)/C(0) (β_std 8, 32) |
|---|---|---|---|---|---|
| 6  | 0.358 | 0.129 (t*=2) | 0.046 | 0.39, 0.32 | 0.154 ± 0.038, 0.114 ± 0.028 |
| 8  | 0.460 | 0.097 (t*=3) | 0.045 | 0.44, 0.44 | 0.066 ± 0.013, 0.111 ± 0.030 |
| 10 | 0.535 | 0.154 (t*=3) | 0.044 | 0.53, 0.53 | 0.137 ± 0.025, 0.103 ± 0.033 |
| 16 | 0.675 | 0.124 (exact n/3) | 0.044 | | |
| 128 | 0.952 | 0.123 (exact n/3) | 0.043 | | |

- **The Monte Carlo agrees with the free values at every point, within errors.** This includes the dip at n = 8, which
  the free sum reproduces because there `t* = 3 = 0.375 n`. At these couplings the correlator is perturbative.
- **With flow, the free ratio is n-independent.** It tends to 0.123 at t = n/3 and 0.043 at t = n/2. In scaled
  momenta `κ = n k`, the ratio converges to a fixed discrete sum over `κ ∈ (π(2m+1), 2πm')`, namely
  `Σ e^{−2|κ|/3 − |κ|²/8}/|κ|² / Σ e^{−|κ|²/8}/|κ|²`.
- **Without flow, it decays like 1/log n.** The free values are 0.071 → 0.030 for n = 6 → 128, because
  `Σ 1/|κ|²` diverges logarithmically. The flow at radius ∝ n is therefore necessary, not cosmetic.
- **Consequence.** At leading order the hypothesis of `slow_lower_corr` holds with `δ = 0.12` at `2k = n/3`, uniformly in
  n, so `ρ₂ = e^{−6.3/n}`.
- **What remains for the lower half.** The interaction corrections to this Gaussian correlator have to be bounded
  uniformly along `β ≥ b log n + β₀`. Their natural size is the running coupling at scale n, which stays small when `b`
  exceeds the one-loop coefficient.

**(P) at leading order.** A gauge-invariant functional is linear in the fluctuation only through a line with a nontrivial
holonomy. Every such line (in a twisted direction, or along the diagonal (1,1)) is odd under some center flip. So in the
Gaussian theory there are no neutral one-gluon states. The lowest neutral states are pairs of `a¹` (or `a²`) quanta with
momenta `±π/n` along their antiperiodic direction, at energy `2ω_min`, where `2 cosh ω_min − 2 = 4 sin²(π/2n)`. That is
`n · 2ω_min → 2π`, and 6.16 at n = 6. At leading order both halves of the window therefore sit at the same scale, `2π/n`:
(P) with constant `n/2π`, and the lower half with `δ ≈ 0.12` at `n/3`. What remains of step 4 is the uniform control of
interaction corrections along `β ≥ b log n + β₀`.

**Size of the corrections, n = 6, 300 configurations** (`data/yang_mills_slow_polyakov_beta_n6_2026_11_03.json`; errors
from a jackknife over blocks of 20 configurations). Free values: `C(1), C(2), C(3) = 0.358, 0.129, 0.046`.
- β_std = 8: 0.357 ± 0.012, 0.147 ± 0.014, 0.065 ± 0.012.
- β_std = 16: 0.355 ± 0.015, 0.120 ± 0.013, 0.039 ± 0.011.
- β_std = 32: 0.385 ± 0.011, 0.131 ± 0.016, 0.056 ± 0.012.
- β_std = 64: 0.363 ± 0.014, 0.120 ± 0.019, 0.049 ± 0.015.
- β_std = 128: 0.332 ± 0.012, 0.121 ± 0.014, 0.064 ± 0.011.

**n = 8, 200 configurations** (`..._beta_n8_...json`). Free values: `C(1), C(3), C(4) = 0.460, 0.097, 0.045`.
- β_std = 8: 0.481 ± 0.014, 0.118 ± 0.018, 0.055 ± 0.014.
- β_std = 32: 0.457 ± 0.011, 0.067 ± 0.013, 0.027 ± 0.010.

**Reading.** The deviations scatter in both directions, up to about 2.4σ, with no trend in β or n. The blocked errors
are probably somewhat small. Interaction corrections are below about 3% of `C(0)` over β_std = 8-128 and n = 6, 8.
That is invisible against `δ ≈ 0.1`. The sign of a correction is not resolved, so these data cannot say whether the
interaction raises or lowers `δ`.

**Stronger coupling** (`..._strong_2026_11_03.json`, 200 configurations; MC with free value in brackets).

| n | β_std | C(1)/C(0) | C(n/3)/C(0) | C(n/2)/C(0) |
|---|---|---|---|---|
| 6 | 3 | 0.374 ± 0.014 [0.358] | 0.161 ± 0.014 [0.129] | 0.077 ± 0.016 [0.046] |
| 6 | 4 | 0.359 ± 0.016 [0.358] | 0.126 ± 0.016 [0.129] | 0.050 ± 0.014 [0.046] |
| 8 | 3 | 0.504 ± 0.019 [0.460] | 0.151 ± 0.023 [0.097] | 0.090 ± 0.020 [0.045] |
| 8 | 4 | 0.490 ± 0.010 [0.460] | 0.120 ± 0.018 [0.097] | 0.062 ± 0.017 [0.045] |

- **The interaction becomes visible below β_std ≈ 4.** The deviation grows as β falls, and at fixed β it grows with n.
  At β_std = 3 the excess at n/2 is ×1.7 at n = 6 and ×2.0 at n = 8. That is the running-coupling pattern.
- **Its sign is positive.** The interaction slows the long-lag decay, so `δ` grows. The prediction made before the run
  (that `C(n/3)/C(0)` would fall with n) was wrong.
- **These boxes are still small.** In standard SU(2) units, β_std = 3 has `a ≈ 0.02-0.03` fm, so `L ≲ 0.25` fm at n = 8.
  The large-volume regime, where the neutral gap becomes the glueball mass and the lower half must fail for `b < b*`,
  needs β_std ≈ 2.3-2.5 with n ≥ 8. It was not reached.
- **The trajectory.** `TargetAGap` is stated with `b*` = 11/(6π²) (repo normalization). For `b ≥ b*` and large `β₀`,
  the window is a small-physical-volume, weak-running-coupling statement.

**Large-volume control** (`..._largevol_2026_11_03.json`, β_std = 2.4, 100 configurations; free values in brackets).
Prediction made before the run: at n = 12 (about 1.3 fm), `C(4)/C(0)` falls clearly below the free 0.124.

| n | C(1)/C(0) | C(n/3)/C(0) | C(n/2)/C(0) |
|---|---|---|---|
| 8  | 0.231 ± 0.020 [0.460] | 0.028 ± 0.013 [0.097] | −0.003 ± 0.014 [0.045] |
| 12 | 0.148 ± 0.016 [0.593] | −0.004 ± 0.013 [0.124] | 0.004 ± 0.006 [0.044] |

- **The prediction was confirmed, already at n = 8.** At confining coupling the correlator dies within 2-3 steps, and
  `C(1)/C(0)` falls with n, where the free values rise. The neutral gap is set by the confinement scale, not by `1/L`,
  so `n · m_eff` grows with n and the lower half of the window fails.
- **This is the expected failure.** It is the case `b < b*`, where the box grows in physical units. It shows that the
  observable can tell the two regimes apart. The weak-coupling agreement with the free `2π/n` correlator is therefore a
  real test, not a property of the observable.
- **The b-threshold is real.** `TargetAGap b` can hold only for `b ≥ b*`, the small-physical-volume side, and what
  remains there is the uniform control of interaction corrections.

## One RG step as a Schur complement (2026-11-03, by hand; numerics below)

**The inequality.** Split the (gauge-fixed) field into fine `x` and coarse `y`. Let the coarse marginal be
`e^{−U_eff(y)} = ∫ e^{−U(x,y)} dx`, and write `H = Hess U` in blocks.
1. Differentiating twice gives the exact identity `Hess U_eff(y) = E[H_yy | y] − Cov(∇_y U | y)`.
2. Suppose `x ↦ U(x,y)` is strictly convex for this `y`. Brascamp-Lieb for the conditional law, applied to
   `w·∇_y U`, gives `Var(w·∇_y U | y) ≤ E[wᵀ H_yx H_xx⁻¹ H_xy w | y]`.
3. Hence `Hess U_eff(y) ≥ E[S_H(y) | y]`, with `S_H = H_yy − H_yx H_xx⁻¹ H_xy` the Schur complement.

**Iteration.**
- `S_H(y) = min_x Q_H(x + y)` (minimizing the quadratic form over the fine block), so the Schur complement is monotone
  in the Loewner order: `A ≥ B` (with `B_xx > 0`) implies `S_A ≥ S_B`.
- A lower bound on `Hess U_eff` at one scale can therefore be fed into the next step: integrate out the next fine block
  and average again.
- Over dyadic scales, convexity of the coarse marginal at scale `2ᵏ` follows from nested conditional averages of Schur
  complements.

**What each step needs.**
- (a) Convexity of the current fine block **at every fine configuration**, which Brascamp-Lieb requires. On a group
  this is Bakry-Émery: `Hess + Ric`, with `Ric = 2` per link for SU(2).
- (b) Positivity of the **averaged** Schur complement on the coarse space.

(a) is where large fields enter: it fails where some plaquette in the block is far from flat. So the scheme puts
the large-field problem in a precise place, and (b) is a statement about averages, which can hold where pointwise
bounds fail. This is a sketch: the inequality is standard, but the gauge fixing, the Faddeev-Popov factor and (a) at
all fine configurations are not handled.

**Numerics, first block step** (`scripts/yang_mills_schur_block.py`, data `data/yang_mills_schur_block{,_ir}_2026_11_03.json`).
- **Split.** Blocks of side 2. Coarse fields are constant on each block in the adjoint frame transported by the flat
  twisted vacuum V; fine fields have zero block mean.
- **Gauge.** Background Landau gauge to V, enforced by a penalty on V's gauge directions. No Ricci term.
- **Normalization.** Everything is relative to the same Schur complement at U = V, so the free field gives 1.
- **Two statistics for (b).** σ_av is λ_min of the configuration-averaged Schur complement over the whole coarse space.
  It is biased low at small samples, and more so at n = 6, where the coarse space has 972 dimensions against 192:
  σ_av at n = 4, β_std = 32 is 0.68, 0.72 and 0.77 with 3, 6 and 12 configurations. So the primary statistic is σ_ir,
  the same quantity on the 12 lowest free-Schur (longest-wavelength) modes, with a jackknife error.

| n | β_std | μ_f (fine block, (a)) | σ_pt mean | σ_ir (12 configurations) |
|---|---|---|---|---|
| 4 | 32 | 0.74 | 0.54 | 0.79 ± 0.025 |
| 6 | 32 | 0.75 | 0.36 | 0.64 ± 0.017 |
| 4 | 16 | 0.62 | 0.26 | 0.65 ± 0.018 |
| 6 | 16 | 0.61 | −0.09 | 0.31 ± 0.021 |

- **(a) holds and is n-independent.** The fine block of a side-2 step stays convex, as a local UV property should.
- **(b) fails in this frame.** Averaging helps a lot over single configurations (σ_ir is well above σ_pt), but σ_ir
  falls with n: by 5σ at β_std = 32, and it halves at β_std = 16. The kill criterion fired.
- **The directly measured long-wavelength stiffness does not fall** (section "Averaged long-wavelength stiffness"). So the
  loss is in the bound, not in the measure. Brascamp-Lieb bounds `Cov(∇_y U | y)` by `E[H_yx H_xx⁻¹ H_xy]`, and that
  bound grows with n on long modes.
- **Suspected cause.** The coarse variables are defined with the transport of the fixed background V rather than of
  U. The difference between the two transports is UV noise, which then enters `H_xy` directly and is summed without the
  cancellations gauge covariance should give. Bałaban's block variables are covariant with respect to U for this
  reason. Next test: block frames from U's own transport (`COV=1`).

**Covariant block frames** (`COV=1`, data `data/yang_mills_schur_block_cov_2026_11_03.json`). Same as above, but each
configuration's block frames come from its own (gauge-fixed) transport, not from V's.

| n | β_std | σ_ir, V frames | σ_ir, covariant frames |
|---|---|---|---|
| 4 | 32 | 0.79 ± 0.025 | 0.985 ± 0.014 |
| 6 | 32 | 0.64 ± 0.017 | 1.088 ± 0.011 |
| 4 | 16 | 0.65 ± 0.018 | 1.002 ± 0.035 |
| 6 | 16 | 0.31 ± 0.021 | 1.071 ± 0.032 |

- **With covariant block variables the averaged one-step bound on long modes no longer falls with n.** It sits at the free
  value, at both couplings. The prediction made before the run (σ_ir rises and its n-dependence weakens) holds.
- **Not a penalty artifact.** Varying the gauge penalty K at n = 4, β_std = 16 gives σ_ir = 0.89 ± 0.05, 1.00 ± 0.035
  and 0.95 ± 0.04 at K = 10, 100 and 1000.
- **But the full-coarse-space σ_av is K-dependent**: 0.68, 0.50 and 0.08 at the same three K. Its soft directions come
  from the mismatch between U-frames and the V-based gauge slice, at the short-wavelength end of the coarse space.
- **The reported μ_f (0.02-0.05) compares fine blocks in different frames, so it is not meaningful here.** The fine block
  itself was positive definite at every configuration, which is what (a) needs.

**Caveat, and the precise remaining gap.** The frames here are frozen at the configuration: the Hessian is rotated by
`T_U` as if `T_U` were constant. A genuine covariant block variable `Y(U)` is a nonlinear function of the field. Its
marginal's Hessian therefore carries second-fundamental-form terms `⟨∇U, ∂²φ⟩` from the frame's own dependence on U, and
these are proportional to the force, which is UV noise. So the numerics support this statement: **with covariant block
variables, the first RG step preserves long-wavelength convexity on average, uniformly in n = 4, 6, up to the frame
curvature terms.**

What remains for one step, in this form:
1. Bound the frame-curvature terms, presumably through the Ward identity (integration by parts against the force,
   `gibbs_ibp`).
2. Prove (a) at all fine configurations, including large fields.
3. Prove the averaged Schur positivity itself.

Iterating then needs the same at each of the `log₂ n` scales, with the coupling running.

**Frame-curvature correction** (`scripts/yang_mills_frame_curvature.py`, data `data/yang_mills_frame_curvature_2026_11_03.json`,
12 configurations).
- **The dropped term.** Along the vector field `Z = T_U w`, the second derivative of the action is
  `⟨Z, HZ⟩ + ⟨∇S, ∇_Z Z⟩`, and the covariant run kept only the first part. The second part is computed here as a
  12×12 matrix on the long modes: `∇_Z Z` by centred differences of the frames, `∇S` by autograd. In these units the
  free Schur value is 1.
- **Prediction made before the run:** the averaged matrix has eigenvalues of size ≤ 0.1, roughly flat in n.

| n | β_std | averaged matrix, eigenvalue range | single configuration, mean λ_min | rms entry |
|---|---|---|---|---|
| 4 | 32 | ±0.030 | −0.111 | 0.019 |
| 6 | 32 | ±0.030 | −0.103 | 0.018 |
| 4 | 16 | ±0.045 | −0.154 | 0.026 |
| 6 | 16 | ±0.045 | −0.152 | 0.026 |

- **Small, independent of n, and of order g** (×√2 from β_std = 32 to 16).
- **Its average is consistent with zero.** The spectrum is exactly ± (the frame derivative is a rotation generator). The
  averaged range is ±0.064 at n = 4, β_std = 32 with 2 configurations and ±0.030 with 12, shrinking as sampling noise
  does. Integration by parts (`gibbs_ibp`) would give `E[⟨∇S, Y⟩] = E[div Y]/β`, which is O(1/β), not O(g).
- **So the covariant one-step result `σ_ir ≈ 1.0-1.09` survives the frame correction.** The one-step bound on long modes
  is at least about 0.95 of free, uniformly in n = 4, 6, at β_std = 16 and 32.

**What one RG step still lacks for a proof:**
1. Turn the averaged Schur positivity and the vanishing of the frame term into inequalities. The latter is a Ward
   identity: a divergence computation, which is formalizable.
2. Prove (a), fine-block convexity, at all fine configurations. This is the large-field problem, now localized to
   single side-2 blocks.
3. Handle the gauge fixing and the Faddeev-Popov determinant, which are not in the numerics.

**And for the whole step:** iterate over `log₂ n` scales, with the effective action of each step feeding the next
through Schur monotonicity.

### Literature check (2026-11-03)

**Piazza-Shen, arXiv:2610.35286 (26 Oct 2026): a log-Sobolev inequality for 2D SU(N) lattice Yang-Mills at every β,
uniform in volume.** This is the first lattice gauge-theory functional inequality beyond strong coupling, and it is the
same architecture as the one-step Schur scheme above.
- **Disintegration.** Blocks of side m; integrate the interior edges crossing an axial plaquette tree. In 2D this gives
  the n-fold convolution `w^{*n}` evaluated on the block boundary word.
- **Marginal.** `Hess` of `H̄ = Σ_B log w^{*n}(W_∂B)` is bounded by
  `4√n (‖∇ψ‖∞ + ‖Hess ψ‖∞)`. The convolution contracts by `rⁿ⁻¹`, so for large m, `Ric_G − Hess H̄ ≥ g/2` (Bakry-Émery).
- **The frame-curvature term appears there too.** Their (4.1),
  `Hess(ψ∘W)(X,X) = Hess ψ(ċ,ċ) + ⟨∇ψ, ∇_ċ ċ⟩`, is the same term measured in "Frame-curvature correction". They bound
  it pointwise by `P ‖∇ψ‖∞`, which is affordable in 2D because ψ is β-independent after convolution.
- **Fine blocks.** Holley-Stroock (oscillation `4tn`) handles the conditional laws, and an Otto-Reznikoff / GOVW-type
  gradient lemma glues the two scales.
- **Why it is 2D-only.** "In higher dimensions, conditional integrations would naturally produce nonlocal, larger Wilson
  loops." In 2D the fine variables are independent across blocks given the boundaries. In 4D they are not, which is the
  regime the covariant Schur numerics above probe.
- **A cautionary result (their §7).** A non-minimizing critical point with vanishing Hessian forces `C_LS ≥ c β^{1/3}`,
  and such points exist for SU(4k) (`U_p = iI`). So LSI constants uniform in β are false in general.
  - For SU(2), `iI ∉ SU(2)`, so their example does not apply.
  - Our constant-flux saddle is nondegenerate, with index 2, so it is not a trap of their type.
  - TargetAGap asks for a 1/n transfer gap, not a β-uniform LSI. Still, any route through a β-uniform functional
    inequality must check for degenerate critical points.

**Other recent rigorous work, none of which covers 4D continuous groups at weak coupling.**
- Adhikari-Cao (Ann. Probab. 53, 2025): exponential decay for finite gauge groups at weak coupling in 4D.
- Cao-Nissim-Sheffield, arXiv:2509.04688: area law in the 't Hooft regime, by the dynamical method of SZZ23.
- Brennecke, arXiv:2511.07297: an explicit leading-order free energy.
- Chevyrev-Shen (2026): 3D Yang-Mills-Higgs renormalisation uniqueness.
- Claimed full solutions (Faizal-Shabir, arXiv:2606.19362, and several Zenodo records) are unverified. They do not
  change the picture.

**Composition across scales** (`scripts/yang_mills_schur_ir.py`, matrix-free: 12 CG solves per configuration, so n = 8
fits in about 200 MB; β_std = 16, 8 configurations, covariant tree-transport frames).
- **Why block side stands in for steps.** Schur complements compose exactly: integrating out nested fine spaces in two
  steps or at once gives the same complement.
- **And it is a pessimistic proxy.** The Schur complement is concave, so averaging between steps gives at least the
  one-shot value: `S₂(E[S₁]) ≥ E[S₂(S₁)]`.

| n | block side l | K | σ_ir | single-configuration mean |
|---|---|---|---|---|
| 6 | 2 | 100 | 1.06 ± 0.04 | 0.86 |
| 6 | 3 | 100 | 0.96 ± 0.07 | 0.74 |
| 8 | 2 | 100 | 1.19 ± 0.03 | 1.02 |
| 8 | 2 | 10  | 0.93 ± 0.02 | 0.76 |
| 8 | 4 | 100 | 0.52 ± 0.07 | 0.19 |

- **The gauge penalty inflates σ_ir, and more so at larger n.** At n = 8, l = 2 the value drops from 1.19 at K = 100 to
  0.93 at K = 10. Compared at fixed K = 10, l = 2 gives 0.89 at n = 4 and 0.93 at n = 8: flat, at about 90% of free.
  Comparisons must hold K fixed, and the spread over K is a systematic.
- **Composition holds to l = 3 and fails at l = 4.** The kill threshold of 0.9 was set before the run.
- **Suspected cause: the transport.** Single tree paths reach 12 links in a 4⁴ block, and UV noise accumulates along
  them. This is the vacuum-frame failure one scale up. Bałaban uses averaged transport. Next test: frames from a
  covariantly smeared copy of U (`SMEAR=3`). Smearing leaves the flat vacuum fixed to 3e-9, so the normalization is
  unchanged.
- **Smeared frames falsify that suspicion.** n = 8, l = 4, K = 100, frames from 3 covariant smearing steps gives
  σ_ir = −0.14 ± 0.03 (single configurations −0.29), worse than tree transport (0.52). The prediction made before the
  run (≥ 0.85) failed.
  - Frames from a smeared copy no longer match U's own transport. The block-constant fields then carry curvature
    relative to U, which enters the fine-coarse coupling.
  - The other candidate cause is lost scale separation: at l = n/2 the fine space holds modes almost as long as the
    coarse ones (the defect of the crude 12-mode split). The matrix-free script does not check fine convexity, so this
    is not ruled out.
  - Telling these apart needs `l ≪ n` (n = 16, l = 4) or the true two-step scheme with averaging between steps, and
    both are well beyond this machine's budget.
  - **Status.** Covariant side-2 blocks hold, at about 90% of free, flat for n = 4-8 at fixed K. Side 3 holds at
    n = 6. Side 4 at n = 8 fails, cause unresolved.
- **Resolved: the l = 4 failure is the convexity scale.** n = 8, l = 4, tree frames, K = 100, at β_std = 64 gives
  σ_ir = 0.97 ± 0.05 (single configurations 0.86), against 0.52 at β_std = 16. The prediction made before the run
  (≥ 0.85) holds.
  - The bare fine block of side l is convex only up to `l* ≈ 1.2 √β_std` (section "Convexity scale"). At β_std = 16,
    `l* ≈ 4.8`, so side 4 sits at the edge and the Brascamp-Lieb subtraction blows up. At β_std = 64, `l* ≈ 9.6`.
  - **Rule for the scheme.** One step may integrate out at most scale `l*` of the current effective coupling. Dyadic
    steps (`l = 2` in coarse units) then need `β_std,eff ≳ 3` at every scale. Along `β ≥ b log n + β₀` with
    `b ≥ b*`, the running coupling stays at least `β₀`, so a large `β₀` meets this at all `log₂ n` scales. This is the
    same condition as TargetAGap's.
  - **Covariant side-2 steps hold at about 90% of free, flat in n.** Larger one-shot steps hold exactly when
    `l ≲ l*(β)`. Both facts are numerics for one step, n ≤ 8.

**Lean: `TwistedSchurStep` (2026-11-03; axioms propext, Classical.choice, Quot.sound; covered by
`scripts/CheckYangMillsTwisted.lean`, 156 checks).** This is the linear algebra of the one-step scheme, for a block form
`Q(x,y) = xᵀAx + 2xᵀBy + yᵀDy` with A symmetric and invertible.
- **`complete_square`.** `Q(x,y) = (x + A⁻¹By)ᵀA(x + A⁻¹By) + yᵀSy`, with `S = D − BᵀA⁻¹B`.
- **`schur_le`, `schur_attained`.** With A positive semidefinite, `yᵀSy` is the minimum of `Q(·,y)`, attained at
  `−A⁻¹By`.
- **`schur_mono`.** A pointwise larger form has a larger Schur complement. Only the smaller form's A needs to be PSD.
  This is the Loewner monotonicity that lets a lower bound on `Hess U_eff` feed the next step.
- **`Q_combo`, `schur_concave`.** The Schur complement of a convex combination of forms is at least the combination of
  their Schur complements. So averaging between steps is at least the one-shot value used in "Composition across scales".

Not formalized: the Brascamp-Lieb step `Hess U_eff ≥ E[S_H | y]`, which needs a variance inequality for the conditional
law. Everything about the Yang-Mills measure is also outside this module.

### Large fields in hypothesis (a): how often is a fine block non-convex? (2026-11-03, numerics)

`scripts/yang_mills_block_convexity.py`, data `data/yang_mills_block_convexity_2026_11_03.json`.
- **What is measured.** For every side-2 block, the lowest eigenvalue of the action Hessian restricted to that block's
  zero-mean (fine) directions, with all other links held fixed (covariant frames, background-gauge penalty), in units
  of β_std. Only its sign matters for (a).
- **Sample.** n = 6, 20 configurations, 1620 blocks per coupling.

| β_std | non-convex fraction | fraction below 0.25 β | lowest | median |
|---|---|---|---|---|
| 2.25 | 0.224 | 0.288 | −3.16 | 0.86 |
| 2.5  | 0.040 | 0.062 | −2.66 | 1.88 |
| 2.75 | 0.0074 | 0.017 | −1.41 | 2.58 |
| 3    | 0 | 0.0031 | 0.12 | 3.00 |
| 3.5  | 0 | 0 | 0.27 | 3.63 |
| 4    | 0 | 0 | 1.43 | 4.06 |

Also: n = 4, β_std = 64: all blocks convex, lowest 6.4.

- **The tail is exponential.** `p(β) ≈ e^{−cβ_std}` with `c = 6.8` (non-convex fraction, 2.25-2.75) or `c = 6.0`
  (fraction below 0.25 β, 2.25-3). The fit predicts 2.2 non-convex blocks at β_std = 3 and 0 were seen
  (Poisson probability 0.11), so the decay may be a little faster.
- **Consequence for the trajectory.** All `(n/2)⁴` blocks are convex with high probability when
  `β_std ≳ (4/c) log n`, a slope of 0.59-0.67 in standard units (0.29-0.34 in repo units).
  - That is above the asymptotic-freedom slope `b*` = 0.371 standard (0.186 repo).
  - So on the critical trajectory `b = b*`, the expected number of non-convex blocks grows like
    `e^{−cβ₀} n^{4 − c b*} ≈ e^{−cβ₀} n^{1.5}`. **Large-field blocks are unavoidable at the critical slope**, and the
    scheme needs a separate large-field treatment there (as in Bałaban).
  - For `b ≳ 0.3` (repo units), a shrinking-volume trajectory that `TargetAGap b` also covers, (a) holds at every
    block with high probability. No large-field analysis is needed for that weaker statement.
- **Prediction made before the run.** It was "convex at ≥ 8, steep below 4-5, 4/c > 0.371". The 4/c part holds. The
  transition sits lower than predicted, at about 2.5-3.
- **Caveats.**
  - The rate is fitted in the strong-coupling window 2.25-3, so extrapolating it to large β is an assumption
    (semiclassically a block needs a lump of several plaquettes far from flat, so a rate of a few β per event is
    plausible).
  - This is the first step only. At coarse step k, the count of `(n/2ᵏ)⁴` blocks and the effective coupling both
    enter, and the first step dominates the sum.
  - Raw per-block eigenvalues were not saved. A follow-up should save them, to fit the tail directly.

**Semiclassical rate** (`scripts/yang_mills_block_nonconvex_action.py`, data
`data/yang_mills_block_nonconvex_action_allsite_2026_11_03.json`). At large β, `p(β) ~ e^{−β_std ΔS_min}`, where `ΔS_min`
is the least action above the vacuum of any configuration whose side-2 fine-block Hessian has a non-positive eigenvalue.
- **Method.** n = 4 twisted lattice. Minimize `S + κ relu(λ_min + 0.05)²` with Adam from four large-field starts, 400 steps
  each. The block Hessian comes from autodiff, with a gauge penalty on the fine projections of all block sites' gauge
  generators (the slice the Monte Carlo test used).
- **Gauge artifacts.** With a penalty on one site only, the optimizer found "non-convex" blocks at `ΔS` = 1.6-3.9 whose
  lowest eigenvector was 63-90% gauge. Those runs are discarded. With the full penalty, every result has gauge fraction
  ≤ 5e-4.

| start | best ΔS (non-convex) | lump: largest plaquette actions |
|---|---|---|
| 0 | 7.42 | 1.40, 1.15, 1.01, 0.64, 0.51, … |
| 1 | 6.25 | 1.44, 1.31, 1.10, 0.74, 0.73, 0.68 |
| 2 | 6.04 | 1.95, 0.38, 0.37, 0.35, 0.34, … |
| 3 | 6.20 | 1.56, 1.23, 1.16, 0.81, 0.81, 0.69 |

- **Result.** `ΔS_min ≲ 6.0`. This is an upper bound from local optimization, and two starts were still descending at the
  last step.
- **Two lump types.** One has six plaquettes (three near angle 90-110°, three near 70°). The other is a single nearly
  flipped plaquette (about 167°) with a halo.
- **Agreement.** This matches the strong-coupling Monte Carlo rate `c ≈ 6-7`.
- **Conclusion (prediction made before the run: 3-10, below 10.8; it holds).**
  - Large-field blocks are not suppressed fast enough on the asymptotic-freedom trajectory: their expected number grows
    like `n^{4 − 6.0·0.371} ≈ n^{1.8}`.
  - A proof of step 4 at `b = b*` must handle them (Bałaban's large-field regions).
  - For `b ≳ 0.33` (repo units, `β_std ≳ 0.67 log n`), which is shrinking volume, they are absent with high
    probability, so hypothesis (a) holds at every block.

**Small-field threshold ε\*** (2026-11-04; same script with `OBJ=lam`; data
`data/yang_mills_block_eps_star_{coarse,fine,long}_2026_11_04.json`).
- **Question.** Bałaban's small-field region is defined by a bound on every plaquette, `1 − ½ tr P_p < ε`. Hypothesis (a)
  holds inside it only if `ε` is below the threshold `ε*` where a side-2 block can first become non-convex.
- **Method.** For a cap `ε`, minimize `λ_min` (block fine Hessian, all-site gauge penalty, as above) subject to every
  plaquette action ≤ ε, via the penalty `10³ Σ relu(a_p − ε)²`. Adam, lr 0.02. `Λ(ε)` is the least `λ_min` reached with
  `max a_p ≤ 1.02 ε`; the threshold `ε*` is the zero of `Λ`.
- **Optimizer behavior.** Descent is slow: `λ_min` crosses zero at ε = 0.3 only after about 480 steps. lr 0.04
  stalls at `λ ≈ 2.1`. The first ε = 0.3 runs (350 steps) ended at `+0.26` and `+0.33`, still descending.

| ε | steps | Λ(ε) (upper bound) | gauge fraction of lowest mode |
|---|---|---|---|
| 0.25 | 1000 | +0.56 (plateau ≈ 0.6-1.1 from step 400) | 2e-4 |
| 0.30 | 1000 | −0.85 (first negative at step 480, max a_p = 0.3025) | 2e-4 |
| 0.35 | 350 | −0.12 | 3e-4 |
| 0.50 | 200 | −0.62, −0.69 (two starts) | ≤ 4e-4 |

- **Result.** `ε* ≤ 0.30`, which is a plaquette angle of about 46°. This is an explicit non-convex configuration with no
  gauge component, so it is an upper bound. ε = 0.25 stayed convex for 1000 steps, which suggests `ε* ≈ 0.25-0.30`, but a
  local optimizer cannot prove the lower side.
- **Shape.** Non-convexity at the threshold does not come from one large plaquette. It is a coherent configuration whose
  top eight plaquettes all sit at the cap.
- **Comparison with the least-action lumps.** The least-action non-convex lumps above carry single plaquettes at 1.4-1.95.
  So bounding the largest plaquette and bounding the total action select very different configurations.
- **Prediction made before the run: ε\* between 0.3 and 1.0.** It is at or below the low end.
- **Consequence for a proof.**
  - Any small-field region on which (a) is proved by a pointwise Hessian bound must use `ε ≲ 0.25-0.3`, which is
    `|1 − P_p| ≲ 0.75`.
  - An analytic perturbation bound (Hessian = covariant flat form + O(sin θ_p) commutator terms + O(1 − cos θ_p)
    terms, each link in 6 plaquettes) will give a smaller ε, since it ignores cancellations.
  - The large-field regions are then the plaquettes with `a_p ≥ ε*`. Their density at weak coupling is set by the
    least action of a configuration containing such a plaquette, not by `ΔS_min`.

**Cost of one large plaquette** (2026-11-04; `scripts/yang_mills_large_field_plaquette.py`, data
`data/yang_mills_large_field_plaquette_2026_11_04.json`).
- **Least action.** `ΔS₁(ε)` is the least action above the twisted vacuum with one chosen plaquette held at `a_p ≥ ε`.
  To quadratic order it equals `ε / G`, where `G = ⟨e_p, P_exact e_p⟩ = (3V − 3)/(6V) → 1/2` is the overlap of a plaquette
  with the exact 2-forms. So `ΔS₁ = 2ε`. Adam, 3000 steps:

| ε | 0.1 | 0.2 | 0.27 | 0.35 | 0.5 |
|---|---|---|---|---|---|
| ΔS₁/ε, n = 4 | 2.003 | 2.020 | 2.033 | 2.048 | — |
| ΔS₁/ε, n = 6 | 2.016 | 2.032 | 2.045 | 2.060 | 2.090 |

  The flux of the forced plaquette spreads evenly over the rest of the lattice, at `≈ 0.05 ε` per plaquette.
- **Monte Carlo frequency.** `f(ε)` is the fraction of plaquettes with `a_p ≥ ε`. n = 6, heat bath, 200 configurations
  per β_std:

| β_std | mean a_p | f(0.27) | f(0.5) | local rate for 0.27, from the previous β |
|---|---|---|---|---|
| 3 | 0.277 | 0.41 | 0.14 | — |
| 4 | 0.200 | 0.26 | 0.055 | 0.46 |
| 6 | 0.130 | 0.100 | 0.0080 | 0.48 |
| 8 | 0.097 | 0.037 | 0.0012 | 0.49 |
| 10 | 0.077 | 0.013 | 1.6e-4 | 0.51 |
| 12 | 0.064 | 0.0048 | 2.1e-5 | 0.51 |

  The rate approaches `2ε = 0.54`. The deficit matches the `χ²₃` prefactor, `−1/(2β)`. For ε = 0.5 the 10→12 rate is
  1.02, against a prediction of 1.0.
- **Prediction made before the run.** I predicted `ΔS₁(0.27)` between 0.45 and 0.6 (Gaussian 0.54), with the
  nonlinearity lowering it slightly. The value is 0.55: the nonlinearity raises it slightly.
- **Consequence.**
  - With `ε* ≈ 0.27`, the density of plaquettes outside the small-field region is `≈ e^{−0.54 β_std}`.
  - On the asymptotic-freedom trajectory `β_std = 0.371 log n + β₀`, that density falls like `n^{−0.20}`, so about
    `n^{3.8}` such plaquettes are present.
  - No fixed small-field cutoff can make them absent: that would need `2ε · 0.371 > 4`, and `a_p ≤ 2`.
  - The global requirement "no large-field region anywhere", which needs β_std ∝ log n with slope 4/rate, is
    therefore the wrong criterion at `b*`.
  - The right requirement is local: the large-field density `e^{−0.54 β_std}` must be below the convergence threshold
    of a polymer (cluster) expansion of large-field regions, which does not depend on the volume. Along any trajectory
    with `b > 0`, `β_std → ∞`, so this holds for all large n.
  - What a proof needs at b* is therefore Bałaban's large-field polymer expansion, with the convexity estimate (a) used
    only inside small-field regions, plus a decoupling estimate showing the polymers do not shift the neutral gap at
    order 1/n.
  - The coherent non-convex configurations of the previous paragraph (`ΔS_min ≈ 6`) are about 11 times more costly
    than a single plaquette crossing ε* (6 vs 0.54). So most large-field plaquettes do not break convexity; the
    pointwise small-field criterion is conservative by that factor in the exponent.

**Decoupling test: admissibility** (2026-11-04; `scripts/yang_mills_slow_polyakov.py` with `ADM=ε`; data
`data/yang_mills_slow_polyakov_{adm027,adm05,wilson6}_2026_11_04.json`; the Wilson value at β_std = 4 is from the
strong-coupling run of 2026-11-03).
- **Question.** Large-field plaquettes are present everywhere at `b*` (above). The question is whether they carry the
  slow neutral weight.
- **Method.**
  - Lüscher's admissible measure: the Wilson measure restricted to every plaquette `a_p < ε`.
  - Each link update (heat bath or overrelaxation) is accepted only if all six of the link's plaquettes stay below ε.
    This is exact Metropolis, since same-direction, same-parity links share no plaquette.
  - Check: the max plaquette stays at or below 0.2700, with acceptance 65% (β_std = 4) and 80% (β_std = 6).
- **Measurement.** n = 6, Lt = 18, flow `t = n²/32`, 200 configurations. The table gives `C(n/3)/C(0)` of `ΣP_m²`
  averaged over the three directions; the error is the jackknife error of the average. The free value is 0.123.

| β_std | Wilson | a_p < 0.5 | a_p < 0.27 |
|---|---|---|---|
| 4 | 0.124 ± 0.012 | 0.137 ± 0.013 | 0.134 ± 0.012 |
| 6 | 0.118 ± 0.013 | 0.150 ± 0.016 | 0.140 ± 0.012 |

- **Result.** At β_std = 4, 26% of Wilson plaquettes have `a_p ≥ 0.27`, so the constraint removes a lot of the
  configuration space. Yet `C(n/3)/C(0)` does not drop.
  - All four constrained values are slightly higher. The mean shift is `+0.019 ± 0.009`, about 2σ. The two Wilson
    references are shared, so the four differences are correlated.
  - The shift is the sign that helps the lower bound. It is consistent with the small coupling shift that admissibility
    causes.
- **Prediction made before the run: agreement within 0.03.** It holds, except for `a_p < 0.5` at β_std = 6 (+0.032,
  1.6σ).
- **Reading.** Removing the large-field region does not remove the slow neutral weight, so that weight lives in small
  fields. This supports a proof structure in which the lower half of the window is carried by the small-field
  (convex, Schur) analysis, and large-field polymers enter only as a perturbation that does not decrease
  `C(n/3)/C(0)`.
- **n = 8, β_std = 4, a_p < 0.27** (`data/yang_mills_slow_polyakov_adm027_n8_2026_11_04.json`): 0.103 ± 0.013, against
  Wilson 0.115 ± 0.012. The difference is −0.012 ± 0.018, so the positive shift seen at n = 6 does not persist. Over
  all five pairs the mean shift is `+0.013 ± 0.008`, consistent with zero at 1.6σ. There is still no sign that large
  fields carry slow weight at n = 8.
- **Not tested.** n ≥ 10; a matched-coupling comparison, in which the admissible β is tuned to the same renormalized
  coupling; the upper half of the window.
- **Caveat: the hard admissible kernel is not reflection positive** (2026-11-04, quadrature).
  - Test: the character coefficients `c_j ∝ ∫ e^{β_std cos θ} 1(1 − cos θ < ε) χ_j dU` of one plaquette factor must
    all be non-negative for the kernel to be of positive type.
  - With the constraint, some are negative. The most negative normalized coefficient is −0.045 (β_std = 4, ε = 0.27,
    j = 3.5), −0.028 (β_std 6), −0.003 (β_std 12) and −1e-5 (β_std 30). Plain Wilson has positive (Bessel)
    coefficients.
  - So a proof cannot replace the Wilson measure by the admissible one without losing `T ≥ 0`. The small/large-field
    split has to be a partition of unity inside the Wilson measure, as Bałaban does it. The admissible runs above are
    a diagnostic only.

### Upper half of the window: lowest neutral energy seen by ΣP_m² (2026-11-04, reanalysis, numerics)
- **Script.** `scripts/yang_mills_neutral_gevp.py` (data `data/yang_mills_neutral_gevp_2026_11_04.json`) reanalyzes
  the stored Polyakov runs.
- **3×3 GEVP fails.** A GEVP over the three observables ΣP₁², ΣP₂², ΣP₃² gave `n E₀ ≈ 4-5` at t = 2-3, below the free
  value. That is the known downward bias of a GEVP on a noisy correlator matrix: the errors at t ≥ 3 are as large as
  the values. Discarded.
- **Single observables instead.** Effective energies of each observable separately, pooled over the three directions
  by inverse variance, with jackknife errors. Free value: `n · 2ω_min` = 6.14 (n = 6) and 6.20 (n = 8). The exact free
  effective energy at t = 0-4 is within 0.2 of that value.

| n | β_std | n E(0→1) | n E(1→2) |
|---|---|---|---|
| 6 | 3 | 5.76 ± 0.17 | 5.20 ± 0.35 |
| 6 | 4 | 6.34 ± 0.20 | 6.03 ± 0.45 |
| 6 | 8 | 6.12 ± 0.17 | 5.74 ± 0.40 |
| 6 | 16 | 6.26 ± 0.17 | 5.81 ± 0.41 |
| 6 | 32 | 6.03 ± 0.15 | 6.03 ± 0.34 |
| 6 | 64 | 6.08 ± 0.16 | 6.11 ± 0.42 |
| 6 | 128 | 6.55 ± 0.17 | 5.95 ± 0.40 |
| 8 | 3 | 5.58 ± 0.15 | 4.94 ± 0.26 |
| 8 | 4 | 5.81 ± 0.17 | 5.65 ± 0.29 |
| 8 | 8 | 6.09 ± 0.17 | 5.63 ± 0.30 |
| 8 | 32 | 6.08 ± 0.16 | 6.50 ± 0.32 |

- **Result.**
  - At `β_std ≥ 8`, `n E` agrees with the free `n · 2ω_min ≈ 2π` within 1-2σ at both n.
  - At `β_std = 3` it is lower: 4.94 ± 0.26 at n = 8, which is 5σ below. That is the large-physical-volume side, where
    the gap in units of 1/L is not protected.
  - Along the `b*` trajectory `β → ∞`, which is the weak-coupling rows.
- **Prediction made before the run.** Within 25% of free at β_std ≥ 8: holds for the single-observable analysis.
  Below free at β_std 3-4: holds at β_std = 3, borderline at 4.
- **n = 10, β_std = 8, 200 configurations** (`data/yang_mills_slow_polyakov_n10_b8_2026_11_04.json`).
  - `n E` = 6.33 ± 0.15 (t 0→1), 6.68 ± 0.26 (1→2), 6.70 ± 0.50 (2→3) and 5.67 ± 0.80 (3→4). Free values are
    6.25, 6.24, 6.23 and 6.22.
  - `C(3)/C(0)` = 0.127, 0.154, 0.128 for the three directions, against a free 0.154.
  - So the rate stays at the free `2π` through n = 6, 8, 10, with no downward drift in n.
- **Limit.** This bounds only the states that couple to ΣP_m². The upper half of `NeutralWindow` is a statement about
  every neutral state, so a numerical test of this kind can only fail to find a counterexample.

**Lean: `TwistedFastDecay` (2026-11-04; axioms propext, Classical.choice, Quot.sound; covered by
`scripts/CheckYangMillsTwisted.lean`, 163 checks).** This is the upper-half counterpart of `slow_lower_corr`.
- **`norm_pow_sq`, `norm_pow_sq_le`.** For a self-adjoint T, `‖Tᵐf‖² = Re⟨f, T²ᵐf⟩ ≤ ‖f‖ ‖T²ᵐf‖`. This is the
  log-convexity of `k ↦ ‖Tᵏf‖`.
- **`norm_pow_two_pow`.** `‖f‖ ‖Tf‖^N ≤ ‖f‖^N ‖T^N f‖` for `N = 2ʲ`.
- **`contraction_of_decay`, `contraction_of_corr`.** If `‖Tᵏf‖ ≤ C rᵏ` (or `Re⟨f, T²ᵏf⟩ ≤ C r²ᵏ`) for all k, with any
  C, then `‖Tf‖ ≤ r‖f‖`. The prefactor is removed by `N → ∞`, using Bernoulli's inequality. No spectral theorem is used.
- **`fast_upper_corr`.** If every neutral f ⊥ Ω has a correlator that decays like `C_f (ρ‖T‖)²ᵏ`, then the first
  (contraction) clause of `NeutralWindow` holds with ρ.
- **`window_of_correlators`.** `NeutralWindow n β ρ₁ ρ₂` follows from a normalized neutral top eigenvector, uniform-rate
  decay of all neutral correlators (rate ρ₁, prefactors free), and one neutral correlator surviving to some lag 2k
  (rate ρ₂).
- **Meaning.** Both halves of the window are now statements about Euclidean correlators only.
  - Any decay-of-correlations method with observable-dependent constants, such as Helffer–Sjöstrand / Brascamp–Lieb
    from a Hessian lower bound, or a polymer expansion, plugs into the upper half without needing a spectral
    statement.
  - The rate must be uniform over observables; the constant need not be.

**Percolation of large-field plaquettes** (2026-11-04; `scripts/yang_mills_large_field_percolation.py`, data
`data/yang_mills_large_field_percolation_2026_11_04.json`).
- **Setup.** Plaquettes with `a_p ≥ 0.27 ≈ ε*` count as large field; two are connected when they share a link (degree
  24). n = 6, 8, 12, 40 configurations per point. χ is the mean cluster size excluding the largest cluster.

| β_std | density | χ (n = 6, 8, 12) | largest cluster / large plaquettes | spanning probability |
|---|---|---|---|---|
| 5.0 | 0.161 | 0.1, 0.1, 0.1 | 0.96, 0.96, 0.96 | 1, 1, 1 |
| 5.5 | 0.127 | 0.5, 0.4, 0.4 | 0.88, 0.88, 0.89 | 1, 1, 1 |
| 6.0 | 0.100 | 8.1, 3.5, 3.3 | 0.63, 0.67, 0.67 | 1, 1, 1 |
| 6.5 | 0.078 | 11.7, 24.3, 46.3 | 0.24, 0.13, 0.07 | 0.95, 0.95, 0.93 |
| 7.0 | 0.061 | 6.5, 8.6, 11.0 | 0.09, 0.04, 0.01 | 0.50, 0.20, 0.07 |
| 7.5 | 0.048 | 4.2, 4.9, 5.2 | 0.06, 0.03, 0.01 | 0.07, 0, 0 |
| 9.0 | 0.023 | 1.8, 2.0, 2.1 | 0.04, 0.02, 0.004 | 0, 0, 0 |

- **Result.**
  - The large-field set percolates for `β_std ≤ 6`: an n-independent giant cluster holds 67% or more of the large
    plaquettes.
  - At β_std = 6.5 it is critical: χ grows like n² while the giant fraction falls.
  - For `β_std ≥ 7` it is subcritical: spanning vanishes with n and χ saturates.
  - So `β_perc ≈ 6.3-6.5`, at a large-plaquette density `p_c ≈ 0.08`.
- **Prediction made before the run: β_perc between 4 and 7.** It holds.
- **Consequence for a polymer expansion of ε\*-large fields.**
  - Below β_perc, no such expansion can converge: the large-field region is a single infinite cluster.
  - A Peierls-type convergence bound (density × lattice-animal constant < 1, with animal constant ≈ e · 23 ≈ 60 for
    degree 24) needs density ≲ 0.017. That is `β_std ≳ 9.5-10` (`f = 0.013` at 10).
  - On the trajectory `β_std = 0.371 log n + β₀`, this means `β₀ ≳ 10` (std units, about 5 in repo units). That is a
    finite physical box at the start, not a constraint that grows with n.
  - This is the price of the pointwise ε\* criterion. Actual non-convex blocks are far rarer: none at β_std ≥ 3.25 in
    Monte Carlo, because they need a coherent ΔS ≈ 6 lump. A large-field definition by block non-convexity instead of
    by plaquette size would percolate only at much stronger coupling.

**Large field defined by block non-convexity** (2026-11-04; `yang_mills_block_convexity.py` at n = 8 with per-block
output, data `data/yang_mills_block_convexity_n8_strong_2026_11_04.json` plus the 2026-11-03 n = 8 run).
- **Setup.** Hypothesis (a) of the one-step scheme needs exactly this: a side-2 block is large field when its fine
  Hessian is non-convex. Clusters are formed on the 4⁴ block lattice under two adjacencies: face (degree 8) and touching
  (degree 80, which includes corners).

| β_std | non-convex blocks | face: mean cluster, χ | touching: mean cluster, χ |
|---|---|---|---|
| 2.0 | 0.62 | 159, 159 (one cluster) | 159, 159 |
| 2.25 | 0.21 | 4.2, 23 | 54, 55 (one cluster) |
| 2.5 | 0.032 | 1.15, 1.3 | 5.4, 8.3 |
| 2.75 | 0.0073 | 1.07, 1.1 | 1.4, 1.8 |
| 3.0 | 0.0010 | 1.0, 1.0 | 1.0, 1.0 |
| 3.25 | 0 | — | — |

- **Caveat.** A 4⁴ block lattice is too small for a threshold. In particular, the touching graph has diameter 2, which
  inflates clusters.
- **Peierls convergence bounds.** Density below `1/(e(d−1))`:
  - face adjacency, density < 0.046: `β_std ≳ 2.45`;
  - touching adjacency, density < 0.0047: `β_std ≳ 2.8-3.0`.
- **Comparison.** The plaquette criterion `a_p ≥ ε*` needed `β_std ≳ 10`. Defining large field by what the one-step
  scheme actually needs lowers the starting coupling `β₀` from about 10 to about 3 (std units; repo units 5 to 1.5).
  - The reason is the factor-11 gap in action cost: a coherent non-convex lump costs 6, while a single large
    plaquette costs 0.54.
  - At `β_std ≈ 3`, SU(2) is near the crossover region. So the critical-slope trajectory could in principle start in a
    box that is not physically tiny. That is still far from the regime step 5 needs.

**Lean: `TwistedGaussianStep` (2026-11-04; axioms propext, Classical.choice, Quot.sound; covered by
`scripts/CheckYangMillsTwisted.lean`, 170 checks).** One RG step for a Gaussian weight, done exactly: the small-field
(quadratic) case of the Brascamp-Lieb step, where the inequality is an equality.
- **`gaussian_marginal`.** `∫ e^{−Q(x,y)} dx = e^{−yᵀSy} ∫ e^{−xᵀAx} dx`, with `S = D − BᵀA⁻¹B`. The proof is completing
  the square plus translation invariance of Lebesgue measure on `m → ℝ`.
- **`gaussian_integrable`, `gaussian_Z_pos`.** If `xᵀAx ≥ c|x|²` with `c > 0`, the Gaussian weight is integrable (it is
  dominated by a product of 1D Gaussians) and its integral is positive.
- **`isUnit_det_of_coercive`.** A coercive block is invertible.
- **`schur_coercive`.** If `Q(x,y) ≥ c(|x|² + |y|²)`, then `yᵀSy ≥ c|y|²`.
- **`Ueff_eq`, `Ueff_second_diff`.** The coarse effective action `U(y) = −log ∫ e^{−Q(x,y)} dx` equals `yᵀSy − log Z`.
  Its second difference is exactly `U(y+h) + U(y−h) − 2U(y) = 2hᵀSh`.
- **`gaussian_rg_step`.** If `Q(x,y) ≥ c(|x|² + |y|²)` with `c > 0`, the normalization is finite and positive and
  `U(y+h) + U(y−h) − 2U(y) ≥ 2c|h|²`. One Gaussian step preserves the uniform Hessian lower bound, with no loss in `c`.
- **Not covered.**
  - The non-Gaussian convex step, `Hess U ≥ S` for an action with `Hess ≥ K` (needs Prékopa's theorem; not in Mathlib).
  - The compact group, gauge fixing, the large-field region, and the iteration over scales.
  - The step from a Hessian lower bound to decay of correlations (Helffer-Sjöstrand) that `window_of_correlators`
    would consume.

## Lean: TwistedPrekopa (non-Gaussian convex step, one fine variable)

`TwistedPrekopa.lean` proves the Prékopa–Leindler inequality on the line, which Mathlib does not have,
and uses it to prove Prékopa's theorem for one fine variable. Everything is axiom-clean.

- `bm_compact`: Brunn–Minkowski on ℝ for nonempty compact sets, `|A| + |B| ≤ |A + B|`.
- `level_ineq`: for measurable `f, g` with `f(x)^λ g(y)^{1−λ} ≤ h(λx + (1−λ)y)`,
  `λ|{f ≥ t}| + (1−λ)|{g ≥ t}| ≤ |{h ≥ t}|` whenever both level sets are nonempty
  (via inner regularity of Lebesgue measure).
- `pl_linear`: when `sup f = sup g = 1`, the layer-cake formula gives `λ∫f + (1−λ)∫g ≤ ∫h`.
- `prekopa_leindler`: normalization plus weighted AM–GM in `ℝ≥0∞` give
  `(∫f)^λ (∫g)^{1−λ} ≤ ∫h`, for bounded `f, g` and measurable `f, g, h ≥ 0`.
- `prekopa_marginal`: if `V(x, y)` is jointly convex (with `x ∈ ℝ`, `y` in any real vector space),
  then `Z(y) = ∫ e^{−V(x,y)} dx` is log-concave.
- `prekopa_convex`: `U = −log Z` is convex when `Z` is finite and nonzero.
- `prekopa_rg_step`: if `V − c(x² + ‖y‖²)` is jointly convex, then `U − c‖y‖²` is convex.

The last result is the non-Gaussian version of `gaussian_rg_step`: integrating out a fine variable
preserves the uniform strong-convexity constant for any convex action. Not covered:
- integrating out many fine variables at once (iterate via Tonelli; needs measurability and finiteness
  of the intermediate marginals);
- the compact group SU(2), where the action is not convex globally, so this applies only after the
  small-field restriction and a chart, which is exactly where the large-field problem enters;
- turning a Hessian lower bound into correlation decay.

## Lean: TwistedPrekopaMulti (Prékopa on ℝᵐ; RG step with many fine variables)

`TwistedPrekopaMulti.lean` extends `TwistedPrekopa` to any number of fine variables. Everything is
axiom-clean (193 checks).

- `pl_ennreal`: Prékopa–Leindler on ℝ for arbitrary measurable `ℝ≥0∞`-valued `f, g, h`, with no
  boundedness or finiteness assumptions. It truncates at `n + 1`, applies the bounded version, and
  passes to the limit by monotone convergence and continuity of `rpow`.
- `PrekopaSpace X μ`: integrating out `x ∈ X` from any jointly log-concave kernel `F(x, y)`
  that is measurable in `x` leaves a log-concave function of `y`.
- `prekopaSpace_real`: ℝ is a Prékopa space. `PrekopaSpace.prod` shows products are (Tonelli), and
  `PrekopaSpace.of_equiv` transports the property along measure-preserving linear equivalences.
  Together these give `prekopaSpace_pi`: ℝᵐ (`Fin m → ℝ`, Lebesgue) is a Prékopa space for all `m`.
- `prekopa_pi`: Prékopa's theorem on ℝᵐ. If `V(x, y)` is jointly convex, then
  `y ↦ −log ∫ e^{−V(x,y)} dx` is convex.
- `prekopa_rg_step_multi` and `prekopa_rg_step_pi`: if `V(x, y) − c‖y‖²` is jointly convex, then the
  coarse action `U(y) − c‖y‖²` is convex. The hypotheses are only measurability in `x` and that the
  marginal is finite and nonzero.

So the convex (small-field) RG step is now formal for any convex action and any finite number of
fine variables: the coarse strong-convexity constant is preserved exactly. Still missing:
- the gauge-theory input, a chart on SU(2)-small fields in which the action is convex and the large
  fields are controlled;
- iterating over about log n scales with the error terms;
- turning convexity into decay of correlations (Brascamp–Lieb variance / Helffer–Sjöstrand).

## Lean: TwistedBrascampLieb (variance bound for linear observables)

`TwistedBrascampLieb.lean` derives the Brascamp–Lieb bound for linear observables from `prekopa_pi`.
It is axiom-clean (196 checks).

- `quad_convex`: a symmetric positive semidefinite quadratic form is convex.
- `brascamp_lieb_linear`: suppose `V − ½xᵀHx` is convex, with `H` symmetric and positive
  semidefinite. Take `t = Hw` and `Z(s) = ∫ e^{s t·x − V(x)} dx`. Then
  `log Z(s) + log Z(−s) − 2 log Z(0) ≤ s² wᵀHw` (`= s² tᵀH⁻¹t` when `H` is invertible).

  Equivalently, `E[e^{sL}] E[e^{−sL}] ≤ e^{s² tᵀH⁻¹t}` for `L = t·x`. This is a symmetrized
  sub-Gaussian bound; at order `s²` it is `Var(L) ≤ tᵀH⁻¹t`.

  The proof uses `K(x,s) = [V − ½xᵀHx] + ½(x − sw)ᵀH(x − sw)`, which is jointly convex, and
  applies Prékopa in `s`. No derivatives or inverses appear.

How this connects to decay: Var(t·x) ≤ tᵀH⁻¹t gives the covariance its upper bound from the
Hessian's inverse. If `H` is a massive lattice Laplacian, `H⁻¹` decays exponentially, so the
fluctuation of a smeared observable is bounded by an exponentially decaying kernel.

Turning this into decay of the *covariance* between two separated observables needs the full
Brascamp–Lieb (or Helffer–Sjöstrand) argument for nonlinear observables. That is not formalized.
For Yang–Mills it would also need a convex small-field chart, which does not exist globally on
SU(2).

## Lean: TwistedPrekopaDomain (the convex step on a convex small-field domain)

`TwistedPrekopaDomain.lean` is axiom-clean (199 checks).

- `logConcave_indicator`: if `D` is convex and `W` is convex on `D`, then `1_D e^{−W}` is
  log-concave.
- `convex_neg_log_on`: if a log-concave `Z` is finite and nonzero on a convex set `S`, then `−log Z`
  is convex on `S`.
- `prekopa_rg_step_domain`: suppose `D ⊆ X × E` is convex with measurable sections, and
  `V − c‖y‖²` is convex on `D`. Then on any convex set `S` of coarse fields where
  `Z_D(y) = ∫_{D_y} e^{−V(x,y)} dμ(x)` is finite and nonzero, `−log Z_D(y) − c‖y‖²` is convex. This
  holds for any Prékopa space of fine variables, in particular ℝᵐ.

So the convex step needs convexity only on a convex small-field region, not globally. That region
must be convex in the coordinates used: a box `{|A_ℓ| ≤ ε}` in Lie-algebra link coordinates
qualifies, but the plaquette region `{a_p < ε}` of the ε* numerics is not obviously convex in any
chart.

The remaining gap at this level is quantitative. The gauge-fixed quadratic form has smallest
eigenvalue about `(π/n)²` on the whole lattice. Nonlinear corrections are `O(ε)` per link. A
single global chart is therefore convex only for `ε ≲ n⁻²`, which shrinks with the volume.
Convexity has to be used block by block: side-2 blocks conditioned on the coarse field, as in the
block-convexity numerics, with the coarse direction's constant `c` kept small. The Lean step above
is stated in exactly that form (fine `x`, coarse `y`, joint convexity on `D`).

## Box small-field region in a fixed linear chart (numerics)

These runs test the hypothesis of `prekopa_rg_step_domain`.

`scripts/yang_mills_box_convexity.py`:
- **Chart:** U_ℓ = exp(x_ℓ) V_ℓ around the twist-eater.
- **Gauge:** exact axial gauge on a maximal tree in the side-2 block at the origin.
- **Fine variables:** the 17 non-tree internal links (51 coordinates).
- **Box:** every lattice link satisfies |x_ℓ| ≤ ε.
- **Measured:** Λ(ε), the least smallest eigenvalue of the fixed-chart fine Hessian of the Wilson action. The search uses Adam, 2–3 starts and 120 steps, so Λ is an upper bound on the true minimum.

| ε | Λ, n = 4 | Λ, n = 6 |
|---|---|---|
| 0 (vacuum) | 3.26 | 3.26 |
| 0.2 | 1.66 | 1.68 |
| 0.35 | −0.53 | −0.54 |
| 0.5 | −2.98 | — |

The crossing is ε_box ≈ 0.25–0.3, and it does not depend on n. This matches the prediction made before the run (0.2–0.5, same at n = 4 and 6). The runs were not fully converged, so the true threshold may be lower. Data: `data/yang_mills_box_convexity_n{4,6}_2026_11_04.json`.

`scripts/yang_mills_box_mc.py` (n = 8, 40 configurations per β):
- Each side-2 block is put in the same axial gauge.
- The angles of its 17 fine links are recorded.
- Blocks containing the twisted plaquette are skipped.

| β_std | median link | median block max | blocks with max ≤ 0.3 | ≤ 0.5 |
|---|---|---|---|---|
| 4 | 0.62 | 1.21 | 0 | 0 |
| 6 | 0.50 | 0.96 | 0 | 0 |
| 10 | 0.38 | 0.73 | 0 | 0.02 |
| 20 | 0.27 | 0.51 | 0.002 | 0.46 |
| 40 | 0.19 | 0.36 | 0.17 | 0.95 |
| 80 | 0.13 | 0.25 | 0.81 | 1.00 |

The median link angle is 1.2/√β_std at every β, and the block maximum is about 2.25/√β_std. The prediction made before the run was c ≈ 1.5–2.5; the measured c is 1.2.

**Conclusion:** a typical block lies in the convex box only for β_std ≳ 60–80. By comparison:
- the plaquette criterion of the percolation runs needs β_std ≳ 10;
- intrinsic block non-convexity needs β_std ≈ 2.5–3.

Fixed linear coordinates cost about a factor of 30 in β against the intrinsic notion. At the critical slope, β_std = 0.371 log n, this is never reached at physical sizes. So the Lean convex step (`prekopa_rg_step_domain`) cannot be fed by a link box. It would need a chart adapted to the configuration, such as the moving frames of the ε* runs, and Prékopa's theorem is not invariant under such changes of chart.

## Stochastic localization: a covariance criterion with no small fields (numerics)

This is a multiscale (Polchinski / Chen–Eldan) route that needs neither a Gaussian reference nor a small-field region.

**Setup.**
- Embed each link in ℝ⁴ as a unit quaternion and tilt the measure by a link field y:
  `μ_{t} ∝ exp(Σ_ℓ ⟨y_ℓ, U_ℓ⟩) μ`, with `y_t = t U* + B_t`, where `U* ~ μ` and `B` is a Brownian motion.
- Then `E[μ_t] = μ` and `Var_μ f = E Var_{μ_T} f + E∫₀ᵀ |Cov_{μ_t}(f,U)|² dt`.
- Cauchy–Schwarz gives `Var_μ f ≤ exp(∫₀ᵀ α_t dt) · E Var_{μ_T} f`, with `α_t = ‖Cov μ_t‖_op`.

**Consequence.** If α_t is bounded uniformly in n, the Poincaré constant is volume-uniform. With relaxation time ~ ξ²,
TargetAGap needs about `∫₀ᵀ α_t dt ≲ 2 log n` with T ~ β. At t = 0, α = 1/4 exactly, because gauge invariance kills
every cross-link covariance.

**Method** (`scripts/yang_mills_sl_covariance.py`, `scripts/yang_mills_sl_softmode.py`).
- μ_t is sampled by heat bath plus overrelaxation with the link field added, starting from U*.
- U* is gauge-randomized, which makes it an exact posterior sample.
- α is estimated by a direction found on one chain and its variance measured on a second, independent chain. This gives
  a lower bound on α_t.
- Two earlier estimators failed calibration (α ≈ 17 and ≈ 10 at t = 0): a gauge-unequilibrated U*, and interleaved
  halves of one chain with d ≫ N_eff.
- The fixed estimator reproduces α = 0.25–0.31 at t = 0.

**Results** (data `data/yang_mills_sl_covariance{,_beta}_2026_11_04.json`).
- **Order-parameter directions.** These are gauge-orbit tangents at U*, constant or lowest momentum. Their variance
  stays at 0.25–0.37 for every β_std ∈ {2,4,8} and t ∈ [0,8], at n = 4 and 6. There is no synchronization / Higgs-type
  growth.
- **Soft subspace.** At β_std ≥ 4 a soft subspace appears near t ≈ 1–2, where the overlap with U* jumps from 0.27 to
  0.57.
  - Top out-of-sample variance at β_std = 8, t = 1, 800 samples: 3.6 (n = 4) and 3.1 (n = 6), flat in volume.
  - At n = 4, 600 samples, t = 1: 4.9 / 2.6 / 3.9 at β_std = 4 / 8 / 16. The peak height does not grow with β.
  - It is not a global color rotation (that subspace captures < 3%).
  - Its spatial spectrum is white, and side-2 blocks alone carry 0.9–1.3. So it is a set of local correlated clusters
    over a few lattice spacings: a finite correlation length, not long-range order.
- **Large t.** `α_t ≈ 1/t`, which roughly cancels against `C_P(μ_T) ~ 1/T` at the end of the localization.

**Reading.** At these sizes `∫₀ᵀ α_t dt` looks O(5–10), independent of β and n. This holds only where ξ ≲ n ≤ 6: at the critical slope ∫α must grow like 2 log n (see "Self-consistency bound" below). The prediction made before the run (a
synchronization transition with α growing in n at weak coupling) failed at n ≤ 6.

**Caveats.**
- Only n ≤ 6, and these are lower bounds on α from single realizations of y, not sup bounds.
- The criterion needs α_t almost surely. The worst cluster among n⁴ locations, i.e. rare large-field tilts, may grow
  slowly with n. This is where the large-field problem reappears.
- The C_P(μ_T) endgame and the step from a Poincaré inequality to a transfer gap are not checked.
- Estimates at the peak are not converged in sample size (150 → 600 samples moved β_std = 4, t = 1 from 1.7 to 4.9).

**Tail over tilts** (`scripts/yang_mills_sl_tail.py`, data `data/yang_mills_sl_tail_n{4,6,8}_2026_11_04.json`).
- Per side-2 block: top direction from chain A, its variance on an independent chain B, block covariances accumulated
  online (n = 8 fits in ~300 MB). β_std = 8, t = 1.
- Sample size: the largest block per realization reads 0.78 / 0.89 / 1.05 / 1.07 / 1.07 at 150 / 400 / 1000 / 3000 /
  10000 samples (n = 4), so 1000 samples is within a few percent of converged.
- Scan, 1000 samples, R independent (U*, y):

  | n | R | blocks pooled | pooled median | pooled p99 | pooled max | mean of per-realization max |
  |---|---|---|---|---|---|---|
  | 4 | 16 | 256 | 0.80 | 1.26 | 1.36 | 1.08 |
  | 6 | 8 | 648 | 0.78 | 1.11 | 1.29 | 1.15 |
  | 8 | 3 | 768 | 0.77 | 1.11 | 1.35 | 1.27 |

- β dependence (n = 4, t = 1, 1000 samples, 4 realizations each; β_std = 8 from the 16-realization row above):
  median 0.72 / 0.80 / 0.79 / 0.72, p99 0.98 / 1.26 / 1.35 / 1.17, max 1.05 / 1.36 / 1.47 / 1.26 at β_std =
  4 / 8 / 16 / 32 (data `data/yang_mills_sl_tail_beta{4,16,32}_n4_2026_11_04.json`). Prediction written before the
  run (median flat at 0.8 ± 0.15, max ≤ 1.5): held. The local soft structure does not change over an 8× range of β.
- The per-block distribution does not depend on n. The per-realization maximum rises only as an extreme value over
  more blocks (1.08 → 1.15 → 1.27), and no block in any realization exceeds 1.4 (none above 1.5 of ~1700).
  The tail looks Gaussian-light (σ ≈ 0.14 around 0.78), which would make the worst block grow like √(log n), a
  harmless contribution to ∫α.
- Prediction written before the run: the max grows like log(#blocks), 1.3 → 1.6, and none exceeds 3. Direction held,
  the size was overestimated (the n = 4 anchor was 1.08, not 1.3).
- Not settled: the global operator norm also includes inter-block coupling (global ≈ 3 vs block ≈ 1 at n = 4, flat
  4 → 6 in the earlier run); only β_std = 8, t = 1; 3 realizations at n = 8; and "almost every y" needs a tail bound
  proved, not sampled.

**Inter-block coupling** (`scripts/yang_mills_sl_interblock.py`, data `data/yang_mills_sl_interblock_n{4,6,8}_2026_11_04.json`).
- Block-reduced estimator: top k = 4 directions of each side-2 block from chain A, then the coupled covariance of all
  nb·k projections, top direction from A scored on an independent chain B. β_std = 8, t = 1, 1500 samples.
- Calibration at n = 4 against the full out-of-sample estimate: reduced / full = 3.74 / 3.85, 2.24 / 3.27,
  2.45 / 3.48 (69–97% recovered).
- Reduced operator norm: n = 4: 3.74, 2.24, 2.45 (mean 2.8); n = 6: 3.72, 4.72 (mean 4.2); n = 8: 3.18 (one
  realization; 1024 reduced dimensions vs 1500 samples, so the A-direction is noisy and this is a weaker lower bound).
- Prediction written before the run: flat in n within 30% at 2.5–3.5. Roughly held: no growth from 4 to 8, but n = 6
  sits higher (4.2) and the spread between realizations (2.2–4.7) is as large as any trend.
- Reading: the operator norm at the peak is O(3–5), set by a few coupled blocks, with no visible volume growth at
  n ≤ 8. Numerics cannot settle a √(log n) or log n creep at these sizes.

**What a proof would need (status of each piece).**
- Poincaré → mass gap: standard (uniform Poincaré gives exponential decay of correlations; used this way by
  Shen–Zhu–Zhu, arXiv:2204.12737, at strong coupling).
- **Large-t endpoint (proposition; rigorous modulo the cited theorems, except the a.s. issue below).** Write the tilted measure as
  `μ_y ∝ exp(Σ_ℓ ⟨y_ℓ,U_ℓ⟩ + β_std Σ_p ⟨U_ℓ, S_p⟩)` (S_p the twisted staple, a unit quaternion). The conditional law of
  one link is von Mises–Fisher with parameter `K_ℓ = y_ℓ + β_std Σ_{p∋ℓ} S_p`, so `|K_ℓ| ≥ |y_ℓ| − 6β_std`.
  - Lemma V (rigorous, crude constant): for κ ≥ 8 the spectral gap of vMF_κ ∝ e^{κ cos θ} on S³ is ≥ κ/82 (Lean caught that (2/3)(1 + 6e³) ≈ 81.01, so the constant 81 first written here was false).
    *Proof.*
    - Generator on functions of θ: `Lf = f'' + 2 cot θ f' − κ sin θ f'`.
    - Take `W = e^{(κ/2)(1−cos θ)} ≥ 1`. Then `LW/W = (κ/2) g(cos θ)` with `g(c) = (κ/2)c² + 3c − κ/2` (checked
      symbolically). g is convex, and g(−1) = g(1 − 6/κ) = −3.
    - So `LW ≤ −(3κ/2) W` outside the cap `C = {1 − cos θ ≤ 6/κ}`. On C, `LW ≤ 3κ e³ =: b`.
    - C is a geodesically convex cap (radius < π/2 for κ > 6). On it `Ric − Hess(κ cos θ) = (2 + κ cos θ) g ≥ (κ − 4) g`,
      so Bakry–Émery gives a local Poincaré constant ≤ 1/(κ − 4) ≤ 2/κ.
    - Bakry–Barthe–Cattiaux–Guillin (Electron. Commun. Probab. 13 (2008), Thm 1.4) give
      `C_P ≤ (1 + b·C_P(C))/λ ≤ (2/(3κ))(1 + 6e³) < 82/κ`. Algebraic core formalized in `TwistedVMFLyapunov.lean`.
    - The sharp value is κ + ½ + o(1) (`scripts/yang_mills_vmf_gap.py`, sector-wise finite elements, calibrated to
      λ₁(S³) = 3 at κ = 0). The crude constant only enlarges the threshold below.
  - Influence: moving neighbour U_ℓ' moves K_ℓ by ≤ β_std |δU_ℓ'|. For 1-Lipschitz g,
    `|E_K g − E_K' g| ≤ sup_s |Cov_s(g, ⟨K−K',U⟩)| ≤ |K−K'| / gap` along the segment from K to K', which stays in the ball of
    radius 6β_std around y_ℓ. So Dobrushin's W₁ coefficient (geodesic metric) is
    `C_ℓℓ' ≤ 82 β_std / (|y_ℓ| − 6β_std)`. Each link has 18 neighbours (6 plaquettes × 3; twist signs do not change norms),
    so `r ≤ 1476 β_std / (min_ℓ |y_ℓ| − 6β_std)`.
  - Wu's theorem (Ann. Probab. 34 (2006) 1960–1989): under Dobrushin's condition r < 1,
    `gap(μ) ≥ (1 − r) · min_ℓ gap(conditional)`.
  - Conclusion: if `min_ℓ |y_ℓ| ≥ 2958 β_std + 8` then r ≤ ½ and `C_P(μ_y) ≤ 164 / (min_ℓ |y_ℓ| − 6β_std)`. With the
    sharp Lemma V constant the threshold would be about 42 β_std. Hence also
    `‖Cov μ_y‖_op ≤ C_P(μ_y)`, since ⟨θ,U⟩ has gradient norm ≤ |θ|.
  - Since `|y_ℓ| ≥ t − √t |g_ℓ|`, this holds for all 4n⁴ links with probability ≥ 1 − n⁻¹⁰ once
    `t ≥ T₁ := 5916 β_std + C log n`. At the critical slope T₁ = O(log n).
- **Consequence: the localization can stop at T₁.** Then
  `Var_μ f ≤ exp(∫₀^{T₁} α_t dt) · E[C_P(μ_{T₁}) E_{μ_{T₁}} |∇f|²]`, and the endpoint factor is O(1/β).
  - Gap in this step: the n⁻¹⁰-probability event where some |y_ℓ| is small must be handled almost surely. Analysis (not
    a fix):
    - The criterion `Var_μ f ≤ e^{∫α} E Var_{μ_T} f` uses α_t as an almost-sure bound at every t, not only at T₁. With
      Gaussian driving noise, every y has positive probability, so no finite T₁ makes the endpoint bound almost sure.
    - Block-Dobrushin with bad links as blocks: a bad link has conditional gap only ≥ 3e^{−16} (Holley–Stroock), so
      the influence on it is ~ β e^{16}. Isolated bad links survive in the spectral-radius (weighted) Dobrushin
      condition if `min |y_good| ≳ β² e^{16}`. Adjacent bad links do not, and they occur with positive probability.
    - Splitting off the bad event costs `E[C_P(μ_T) E_{μ_T}|∇f|²; bad]`. The only general bound on C_P(μ_T) there is
      Holley–Stroock, e^{O(n⁴(β+T))}, and it cannot beat the bad-event probability.
    - The published non-log-concave uses of this criterion (Eldan–Koehler–Zeitouni for Ising and SK; Bauerschmidt–
      Bodineau–Dagallier, Polchinski flow) get their covariance bound deterministically, uniformly in y. Here that would
      need a sup over all tilts, including adversarial ones. This is an open technical obstacle, not bookkeeping.
    - Bounded-noise alternative, checked and rejected. Observe each link through noise uniform on a cap of radius r.
      The posterior is then μ conditioned on `U_ℓ ∈ cap(y_ℓ, r)` for every link, a martingale scheme with no bad
      events. But its endpoint is YM on a product of small caps, i.e. the small-field box of the section "Box small-field
      region in a fixed linear chart". Convexity there needs every plaquette in the box near the identity, which
      typical configurations satisfy only at β_std ≳ 60–80. The leftover term `Var_y E_{μ_y} f` is a renormalization
      step. So this scheme reduces back to the small-field / large-field problem.
- **Self-consistency bound: the window cannot be uniformly tame (correction).**
  - A draft of this section claimed that `α_t ≤ A·min(1, 1/t)` on [0, T₁], with any fixed A, would suffice. That would
    give a Poincaré constant O((log n)^A).
  - That hypothesis must be false at the critical slope. There the correlation length in lattice units is ξ ~ n, and a
    volume-uniform Poincaré constant C_P gives decay of correlations at rate ~ 1/C_P (finite speed of propagation). So
    C_P ≳ ξ ~ n, and plausibly ~ ξ².
  - In the Gaussian picture, `α_t ≈ 1/(β/ξ² + t)`. It reaches ξ²/β ≫ 1 for t ≲ β/ξ², and `∫₀^T α ≈ log(1 + Tξ²/β) ≈
    2 log ξ`. So ∫α must grow like 2 log n.
  - The real requirement is sharp: `∫₀^{T₁} α_t dt ≤ (2 + o(1)) log ξ` up to an additive constant. Every scale between
    t ~ β/ξ² and t ~ 1 must contribute at most its Gaussian share (dt/t).
  - This is the per-scale accuracy of a renormalization-group analysis in another form. Stochastic localization
    repackages the multiscale problem; it does not remove it.
  - The numerics at n ≤ 8 (α ≈ ¼ at small t, peak 3–5 near t ≈ 1, flat in n and β) are in the regime ξ ≲ n ≤ 8. They
    cannot see the small-t window t ≲ β/ξ² where the long-wavelength gauge-invariant modes would appear. Nor do they
    test the sharp constant, which is what decides the proof. The earlier "∫α = O(5–10), flat" reading is a statement
    about small volumes only.
- Average bound: for any prior, E_y Cov μ_t ⪯ I/t (minimum mean-square error is at most that of the estimator y/t).
  This is the expected covariance only; the criterion needs the operator norm almost surely.
- Endgame check (existing data, `t·α_t`): at t = 8 the product is 0.67–1.05 and falling at β_std ≥ 4 (n = 4:
  1.15 → 0.76; n = 6: 1.00 → 0.67 from t = 4 to 8). With α_t ≤ 1/t at large t (von Mises–Fisher tangent variance
  1/|y|), `exp(∫^T α) · C_P(μ_T)` stays bounded as T → ∞, since C_P(μ_T) ~ 1/T. The endgame is consistent.
- Small t: third moments of links vanish (gauge and center symmetry, bipartite lattice), so Cov μ_t = ¼ I + O(t²). The
  O(t²) term contains connected plaquette–plaquette correlations of μ summed with random-sign weights y. Bounding it
  uniformly needs some decay of those correlations, so the small-t window is weakly circular: not free.
- Middle window: for t = O(1) the tilt acts as a link mass; in the Gaussian approximation the tilted theory has
  precision βΔ + tI, so correlation length ξ ~ √(β/t) ~ √(log n) at the critical slope. A multiscale analysis of the
  tilted theory would need only O(log log n) scales instead of O(log n). This is the most promising reduction found,
  and it is unproved.
- The crux: an almost-sure (or high-probability, with control of the exceptional y) bound ‖Cov μ_t‖ ≤ A on the window
  t ∈ [0, O(β)], uniform in n. Numerically A ≈ 3–5 with α ≈ 1/t already from t ≈ 4 at every β tested (the decay
  starts at t = O(1), not t = O(β)). No argument for it exists here.

**Next.**
- Repeat the tail scan at t = 2 and β_std = 4, 16.
- The C_P(μ_T) endgame and the Poincaré → transfer-gap step.

### Localization path on the GPU, n up to 24 (2026-11-04, numerics, not a proof)

`scripts/yang_mills_sl_gpu.py` (torch, float32), analysis in `scripts/yang_mills_sl_gpu_analyze.py`, data in
`data/yang_mills_sl_gpu_b2.5_2026_11_04.json`. The twisted SU(2) torus N⁴; 24 gauge-invariant long-wavelength
observables F = Σ_x cos/sin(2πx_d/N)·Re P_mn; the localization path μ_t with y_t = tU* + B_t (U* a μ-sample, so
the Nishimori identity applies); 2 realizations of y, two chains per t; V(t) = E Var_{μ_t} F; α_struct is the top
eigenvalue of Cov μ_t in a 216-dimensional structured span (right/left frames × 9 low-k functions), scored on an
independent chain. The criterion needs ∫₀ᵀ α ≥ log(V0/V(T)) ("required").

β_std = 2.5 (⟨½trP⟩ = 0.652 at every N):

| N | R = Var F / E|∇F|² | Gaussian prediction N²/(4π²β) | V(10)/V0 | required ∫₀¹⁰ α | structured ∫₀¹⁰ α |
|---|---|---|---|---|---|
| 8 | 0.042 | 0.65 | 0.743 | 0.30 | 1.48 |
| 12 | 0.043 | 1.46 | 0.725 | 0.32 | 1.43 |
| 16 | 0.043 | 2.59 | 0.737 | 0.31 | 1.42 |
| 24 | 0.043 | 5.84 | 0.727 | 0.32 | 1.46 |

- The prediction made before the run (R grows like N² at β = 2.5) failed: R is flat over a factor 9 in N² and is
  ~1/15 of even the N = 8 Gaussian value. β = 2.5 is confining with ξ ≈ 1 lattice unit, so the long-wavelength F
  carry no slow mode. Nothing along the path depends on N either; the criterion closes with a margin of ~4.5×.
- This says nothing about weak coupling, where the 2 log n growth of the required integral is expected.
- **Flaw in this observable set (found at the first β = 4 row).** Re P ≈ 1 − |F|²/2 is a composite whose variance
  is dominated by short distances, so its Fourier modes cannot see a slow long-wavelength mode at any β: at N = 8,
  R fell from 0.043 (β 2.5) to 0.020 (β 4). The flat R above is therefore not evidence against a slow mode. The
  N²/(4π²β) prediction was for a linear observable, and no gauge-invariant SU(2) observable is linear. The
  β = 4 run was stopped. Replacement: Polyakov loops along the untwisted directions 0, 3 with weights 1, cos/sin(2πx_e/N), split into
  poly2 = (½tr L)² (center neutral, the target sector) and poly1 = ½tr L (center charged, outside the target).
  Written before the run: if a slow neutral mode exists at β 4, R_poly2 grows ≥ 2× from N = 8 to 24.
- Caveats: 2 realizations of y; α_struct is a lower bound on ‖Cov μ_t‖_op on a fixed span, not the operator norm;
  the trapezoid uses ¼ on [0, 0.01].
