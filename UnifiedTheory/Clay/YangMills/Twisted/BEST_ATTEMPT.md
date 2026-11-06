# Best attempt at the Yang-Mills proof (2026-11-01)

**This is not a proof.** It is the strongest argument available from this repo, written as a proof, with the status of every step marked. Steps 4, 5, 6, 7 and 9 are open, and they carry nearly all the mathematical content. All twelve full-target requirements remain open.

Labels:
- **Lean**: compiled, standard axioms only.
- **By hand**: derived here, not formalized and not refereed.
- **Literature**: published, cited from memory, not rechecked here.
- **Open**: no proof exists, here or as far as I know anywhere.

## Target

For SU(2): construct a nontrivial quantum field theory on R⁴ satisfying the Osterwalder-Schrader or Wightman axioms, with spectrum in {0} ∪ [Δ, ∞), Δ > 0. Clay asks for every compact simple gauge group, so even success here leaves the other groups.

## The argument

**Step 1. Lattice theory. Lean.** The Wilson law with twist n₁₂ = 1 is a probability measure on a compact space, and reflection positive in directions 0 and 3 (`reflection_positive`). Its transfer operator is compact, self-adjoint and positive (`TwistedTransfer`). Expectations are ratios of traces (`expectation_trace`).

**Step 2. A gap at each cutoff. Lean, with no useful size.** For each `n` and `β > 0` a first excited neutral level exists (`neutral_level`, `exists_neutralWindow`). A scratch derivation gives only `1 - exp(-72βn³)`, far too weak to survive any limit.

**Step 3. Limit points exist. Lean, possibly trivial.** Compactness gives limits along subsequences, and reflection positivity passes to them (`sliceLoop_limit_exists`, `sliceLoop_os_tendsto`, `physical_limit_exists`). Without tuning the limit can be trivial: at `β → ∞` plaquettes and slice-flowed labels collapse to constants (`TwistedLimit`). Everything below exists to prevent that.

**Step 4. Small volume, weak coupling. Open.** Prove `TargetAGap b`: for `β ≥ b log n + β₀`, the neutral level lies between `exp(-C/n)` and `exp(-c/n)`. That is a gap of order 1/L, uniform in the cutoff, on a physical box of side L. If it holds, connected correlations decay (`connected_of_targetAGap`, Lean, conditional).
- Inputs available: Balaban's ultraviolet stability on the torus (Literature), the twist lifting zero modes, and the near-flat coercivity `near_flat_coercive` (Lean).
- Missing: large-field control through the multi-scale flow, and any bound on the law as opposed to pointwise bounds on the action. `TwistedFixedN` now has `frameWeight_lower`, `integral_tree_chart_of_close` and `energy_no_log` (Lean). These serve only the fixed-`n` limit `β → ∞`, whose limit theory is free. `TwistedValleyChart` (Lean) now proves the closeness in tree gauge on the valley (`valley_close`) and so the chart identity with no open hypothesis (`integral_valley_chart`), for `√σ ≤ 1/(308 n³)`. Still missing there: a slice for the three frame directions and the Laplace evaluation of the kernel. None of this reaches the trajectory `β ~ log n`. A rough hand estimate (README, "Where the chart route can reach") says any pointwise Gaussian chart needs `β ≳ n¹¹ log³ β`. So this route is closed for step 4 as stated, not merely unfinished. `TwistedNormSharp` (Lean) pins the top level `‖T‖` to one free Gaussian per link at fixed `n`. A second route was tried and also fails. It aimed at a Helffer-Sjöstrand / Brascamp-Lieb covariance bound, which needs `Hess U + Ric ≥ c β Δ₀` on horizontal directions at typical configurations. Numerically (README, "Preconditioned convexity") this fails along `β ~ log n`. The bare Hessian has negative long-wavelength directions whose size grows with n, roughly like `n^0.65/√β`. Convexity at long scales holds only for the effective action, so this route also comes back to a renormalization step. Restricted to blocks of side `l`, the deficit is `1 - λ ≈ 0.41 l^0.92 β_std^(-0.51)`, so the bare action is convex only up to `l* ≈ 1.2 √β`, about `1/g`. The averaged long-wavelength stiffness, by contrast, is free-like and flat in n = 4-8 (README, "Averaged long-wavelength stiffness"). So the open content of step 4 is now precise: a gauge-covariant multiscale Bakry-Émery theorem carrying convexity of the coarse marginal from `l*` to `n`. On the large-field side, the classical action along the lowest coarse mode is scale invariant. It is convex up to action about 2.6, with a barrier of about 4.9 to a center copy (README, "Large fields along the lowest mode"). That barrier is an exact critical point, the lattice 't Hooft constant-flux saddle: `S = n⁴(1 − cos(π/n²)) → π²/2`, Morse index 2, with negative modes `−2π/n²` (README, "Constant-flux saddle"). So coarse large fields cost about `n^(-2.6 b')` on `β_std = b' log n`, classically. That is the mechanism by which the `b log n` in TargetAGap would control them. `TwistedSlowObservable` (Lean) now reduces the whole window to two inequalities on the Euclidean measure (README, "two-sided Poincaré"): a neutral Poincaré inequality with constant `n/c` (open, the hard half), and one slow neutral observable with `E[(Δ_t g)²] ≤ 2(1 − e^{−C/n}) Var g` (open, the trial-function half). `slow_lower_corr` (Lean, 2026-11-03) weakens the second to one neutral correlator with `C(2k) ≥ δ C(0)` at a single lag `2k ≈ n/a`, which gives `ρ₂ = δ^{1/2k}`. That is an O(1) statement with no small parameter. For the flowed Polyakov observable `g = Σ P₁²` (README, "A neutral correlator at lag ≈ n/3"), the Gaussian correlator around the twist-eating vacuum is computed exactly: `δ → 0.123` at `n/3`, uniformly in n. Without flow it decays like `1/log n`. The Monte Carlo agrees with it within about 2σ for β_std = 4-128 and n = 6-10. The free theory has no neutral one-gluon states, so (P) at leading order has constant `n/2π`. So both halves of the window sit at `2π/n` at leading order. At β_std = 3 the interaction corrections are visible, grow with n, and raise `δ`. At β_std = 2.4 (n = 8, 12) the correlator dies within 2-3 steps: in large volume the lower half fails, as it must for `b < b*`. What remains of step 4 is uniform control of the interaction corrections on the small-physical-volume side. That is the same multiscale problem as above, seen through one correlator. **Multiscale step, first attempt (2026-11-03, README "One RG step as a Schur complement" and what follows).**
- **The one-step inequality.** `Hess U_eff ≥ E[Schur complement | coarse]`, exact by Brascamp-Lieb wherever the fine
  block is convex. Iterating it needs monotonicity and concavity of the Schur complement, which are proved in Lean
  (`TwistedSchurStep`).
- **Block variables must be covariant.** Measured on the 12 longest coarse modes, with the free field at 1:
  - with vacuum-frame block variables, the averaged bound collapses as n grows (0.79 → 0.64 at β_std 32, 0.65 → 0.31
    at β_std 16, n = 4 → 6);
  - with covariant variables (the configuration's own transport), it holds at about 0.9 of free, flat for n = 4-8 at
    fixed gauge penalty;
  - the dropped frame-curvature term is ±0.03-0.045 and n-independent.
- **Step size.** A step of side l holds exactly when `l ≲ l* ≈ 1.2 √β_std`: n = 8, l = 4 gives 0.52 at β_std 16 and
  0.97 at β_std 64. Smeared transport made it worse.
- **Large fields.** A side-2 fine block is non-convex with probability about `e^{−6.4 β_std}`. So at the critical slope
  `b*` large-field blocks are unavoidable (about `n^{1.5}` of them), while for `b ≳ 0.3` (repo units) none occur with
  high probability.
- **Small-field threshold and large-field density (2026-11-04).**
  - A side-2 block can turn non-convex with every plaquette at `a_p ≤ 0.30` (ε* ≈ 0.25-0.30).
  - One plaquette above ε costs action 2ε. So plaquettes above ε* have density `e^{−0.54 β_std}`, which is `n^{−0.2}` at
    `b*`. No fixed cutoff removes them, and large fields need a polymer expansion with a local, volume-independent
    density criterion.
  - Removing them (admissible measure, `a_p < 0.27`) does not change `C(n/3)/C(0)` at n = 6, 8: the slow weight is
    small-field.
  - The hard admissible kernel is not reflection positive, so the split must be a partition of unity inside the Wilson
    measure.
- **Both halves as correlator statements (Lean, 2026-11-04).** `window_of_correlators` (`TwistedFastDecay`) derives
  `NeutralWindow` from two inputs: uniform-rate decay of all neutral correlators (observable-dependent constants
  allowed), and one correlator surviving to lag 2k. Upper-half numerics: `n E ≈ 2π` (free `n·2ω_min`) for ΣP_m² at
  β_std ≥ 8.
- **Open.**
  - A rigorous Brascamp-Lieb step on the group.
  - The Ward identity for the frame term.
  - Large-field blocks at `b*`.
  - Gauge fixing.
  - The iteration over `log₂ n` scales.
- **Literature.** The closest template is Piazza-Shen (arXiv:2610.35286): a one-step RG proof of a log-Sobolev
  inequality for 2D lattice Yang-Mills at every β, which they say does not extend to 4D directly.

**Step 5. The crossover, coupling of order 1. Open, and the real gap.** Pass from small box, where weak coupling applies, to large box, where a decay criterion could apply. Best attempt, using `y = (1 - z)/(1 + z)`, `z = Z_tw/Z`:
- *5a. By hand, algebra in Lean.* With time along direction 1, `Z_tw = Tr(Ω T^t)` for the periodic `T` and center operator `Ω`, so `y = Z_1/Z_0` is a ratio of sector traces of a positive operator. Hence `y(2L₁, 2L₂) ≤ K₃ y(L₁, L₂)⁴` (`TwistedFluxRecursion.four_step`). Checked on exact 2D SU(2) sums, 0 violations.
- *5b. Numerics.* `y < K₃^(-1/3)` appears to start near the deconfinement scale: β_std 2.2-2.3 at L = 4, about 2.4 at L = 6. `log K₃` falls with L at fixed β_std from L = 4 to 6. Massless U(1) has `y` flat in L, as it must.
- *5c. Where it breaks.*
  1. No bound on `K₃` in L. The numbers above are isotropic bases, not the constants of a chain.
  2. `L₀` and `L₃` are not doubled. `-log z(2t) = -2 log z(t) + log K_tw - log K_per` is an identity, and using it needs `K_tw/K_per = 1` to the precision of `y`. A Jensen bound in the eigenbasis of `T` gives linearity in `t` with no `K`, but its rate is a single-slice 't Hooft loop, of order `L₃`. That is not small in `L₁L₂`, so it is useless.
  3. Nothing proves `y` falls below threshold at some L for every β. At L = 4 and β_std = 2.5 the bound is `K₃ y⁴` ≈ 52 while `y < 1`, so it is vacuous exactly where control is needed. This is the crossover restated.

- *5d. What the constant is, and why the route needs the gap (2026-11-06, `TwistedFluxThermal`, Lean, standard axioms; lattice identification by hand).*
  1. **K is thermal.** Normalize the sector spectrum by its top eigenvalue and let `Φ(t) = log Σ e^{-t(E_i - E_0)}` be the box's
     vacuum-subtracted thermal free energy at temperature `1/t`. Then exactly `Φ(t) ≤ log K ≤ 2Φ(t)` (`thermal_two_sided`).
     A uniform bound on `K₃` is equivalent to a Stefan-Boltzmann-type bound on boxes at temperature of order their inverse size.
     That bound holds in a massless phase too, so it carries no confinement. The measured `log K₃` fits this reading: large
     where the box is hot (β_std 2.5, L = 4, 6 < N_t,c = 8: 5.2, 4.0), small where it is cold (β_std 2.3, L = 6 > N_t,c = 4: 0.95).
  2. **The (1,2) chain only sees a slab.** At fixed `L₀, L₃` the chain doubles only the flux plane. The slab theory is
     two-dimensional at long distance (2D gauge theory with adjoint scalars), which has a fundamental area law at every β, and
     2D compact U(1) does too. So the chain can succeed at fixed thickness without saying anything about four dimensions. All 4D
     content of step 5 is in doubling `L₀, L₃`. (By hand, from the standard 2D results; not formalized.)
  3. **Transverse doubling costs the box thermal free energy.** Take `L₀` as the time of the magnetic-sector transfer operators
     (untwisted `A`, twisted `B`, `z = B/A`). `A(2t) ≤ A(t)²` and the definition of `K_B` give `z' ≥ z²/K_B`, hence
     `y' ≤ (K_B − z²)/(K_B + z²) ≤ 4y + κ` with `K_B = 1 + κ` (`transverse_ratio`, `transverse_y`, `transverse_y_linear`).
     By item 1, `κ` is small only when `Φ` is small, i.e. the box at temperature `1/L` is cold. That means a gap at scale `L` of
     order `log(L³)/L`.
  4. **Consequence.** With these inequalities an isotropic doubling chain `y(2L) ≤ K₃(4y(L) + κ(L))⁴` contracts only if
     `κ(L) ≪ 1` at every scale past the start, which is a finite-volume mass gap at every scale. Together with step 7 (no theorem from
     area law to gap) the flux-recursion route is circular: it consumes the gap instead of producing it. It also cannot start below the
     deconfinement length, where `κ = O(1)`, which agrees with the center-sector numerics of GAP_BAND_STATEMENT §8 (box ≳ 2.5–3.5 N_t,c).
     The route is closed in this form. A crossover argument needs an inequality for transverse doubling whose error term is not a
     thermal free energy, and none is known.

**Step 6. Long distance. Open.** `BoxCriterionOn` implies mixing and covariance decay (`TwistedBridge.mixing`, Lean, conditional), and holds at strong coupling (Lean). Nothing establishes it at the coupling reached after step 5. Hand argument: block Dobrushin has no margin below the correlation length.

**Step 7. A gap in infinite volume. Open.** Two routes, neither complete:
- From step 6, decay plus reflection positivity gives a gap at that cutoff. The bound must then scale as `1/a` to survive, which requires steps 4 and 5 uniformly.
- From step 5, `y → 0` gives an area law through Tomboulis-Yaffe (Literature). I know of no theorem from area law to mass gap.

**Step 8. Reconstruction. Literature.** Osterwalder-Schrader reconstruction gives a Hilbert space and Hamiltonian from reflection-positive Schwinger functions with the needed growth bounds. The bounds are not established here.

**Step 9. Euclidean invariance and nontriviality. Open.** The lattice has only hypercubic symmetry, so O(4) must be restored in the limit. The limit must also be non-Gaussian, and gauge-invariant local fields must be identified. Nothing here addresses this beyond the labels in `TwistedLimit`.

## Conditional statement

If steps 4, 5, 6, 7 and 9 hold, with the bounds step 8 needs, then SU(2) Yang-Mills exists with a mass gap. This is not formalized. It has little content as a theorem, because the hypotheses are nearly the whole problem.

## Where the first attempt to fill it would stop

- Step 4 is the first step that fails. It has a known shape, but needs large-field control nobody has written for this setting.
- Step 5 is the step with no method. The filter any argument must pass: it must use something massless compact U(1) lacks, because Coulomb U(1) at β = 1.1 shares the lattice, reflection positivity and compactness. The scale-correlation recursion failed this filter. The flux recursion passes it only by being silent at `y` near 1, so it adds no control there.
