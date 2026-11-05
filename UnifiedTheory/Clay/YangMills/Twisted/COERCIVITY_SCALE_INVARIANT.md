# Scale-invariant classical coercivity on the twisted lattice (by hand, 2026-11-02)

**Lean (2026-11-02):** `TwistedPlaquetteValue.lean` proves the per-plaquette step of (i) with explicit constants:
- `plaquette_value_lower`: `((‖c‖ − 5s²)₊)²/2 ≤ 1 − Re(e^A e^B e^C e^D)` for imaginary `A..D` with `s ≤ 1/2`;
- `sum_value_lower`: the summed form, `(1−δ)/2 · Σ‖c_p‖² − 25/(2δ) · Σ s_p⁴ ≤ S`.

Both use only the standard axioms, with no sorry. They are not yet wired to the lattice types.

**Status of everything else: by hand, not formalized, not refereed.** Part (i) is proved below modulo one standard input, a discrete
Sobolev inequality on the torus (S1). Part (ii), a lattice Uhlenbeck gauge, is open; the only evidence is numerical, on
cooling paths. Together they would replace the `n⁻¹⁰` hypothesis of `near_flat_coercive` with an `n`-independent one.
This is a classical statement. It is an input to step 4, not step 4.

## Setting

- SU(2) on the 4D lattice torus `Λ = (Z/n)⁴`, with twist `n₁₂ = 1`.
- `V` is a flat twisted vacuum, and `U_e = exp(a_e) V_e` with `a_e ∈ su(2) ≅ R³`.
- The action is `S(U) = Σ_p (1 − z_p P0(U_p))`, and the weight is `exp(−β_std S)`.
- `d_V` is the covariant lattice differential at `V`, `Δ₀ = d_V^* d_V + d_V d_V^*`, and `E(a) = ⟨a, Δ₀ a⟩`.
- The Landau slice is `d_V^* a = 0`; on it, `E = ‖d_V a‖²`.
- `‖a‖₄⁴ = Σ_e |a_e|⁴`.

## (S1) Twisted lattice Sobolev, uniform in n

**Claim.** `‖a‖₄ ≤ C_S E^{1/2}`, with `C_S` independent of `n`.

**Proof sketch.**
1. Because `V` is flat, `Δ₀` acts componentwise: `E = Σ_μ ‖∇_V a_μ‖²`, where each `a_μ` is a twisted adjoint section over
   sites. (Covariant differences commute when the curvature is zero.)
2. Lattice Kato inequality: `||u| − |v|| ≤ |u − Ad(V) v|`. So `f_μ = |a_μ|` satisfies `‖∇f_μ‖₂ ≤ ‖∇_V a_μ‖₂`.
3. Split `f_μ = f̄_μ + g_μ`, with `f̄_μ` the mean. Then `‖f̄_μ‖₄ = ‖f̄_μ‖₂ / n ≤ ‖a_μ‖₂ / n`.
4. Twisted Poincaré: every adjoint component gets a momentum shift of at least `π/n`, so
   `‖a_μ‖₂² ≤ ‖∇_V a_μ‖² / (4 sin²(π/2n)) ≤ (n²/4) ‖∇_V a_μ‖²`. Hence `‖f̄_μ‖₄ ≤ ½ ‖∇_V a_μ‖`.
5. For the mean-zero part, use the discrete Sobolev inequality on `(Z/n)⁴`: `‖g‖₄ ≤ C ‖∇g‖₂`, with `C` independent of `n`.
   - This follows from discrete Loomis-Whitney, `‖h‖_{4/3} ≤ C ‖∇h‖₁`, applied to `h = |g|³`.
   - It also uses the discrete chain rule `|∇|g|³| ≤ 3 max(|g|, |g(·+e)|)² |∇g|`, plus Hölder.
   - The torus version comes from the `Z⁴` version by a partition of unity at scale `n`. The resulting lower-order term is
     absorbed by Poincaré as in step 4.
6. Steps 1-5 give `‖a‖₄ ≤ Σ_μ ‖a_μ‖₄ ≤ (C + ½) Σ_μ ‖∇_V a_μ‖ ≤ 2(C + ½) E^{1/2}`.

The Hausdorff-Young route gives only `C_S ≲ (log n)^{1/4}`, which is not enough: on `β ~ log n` the log loss would use up
the margin. The numerical value of `C_S(n)` is checked in `scripts/yang_mills_twisted_sobolev.py`.

## (i) Coercivity on the Landau slice

**Claim.** There are constants `c₁, c₂, E₀ > 0` independent of `n` such that, if `d_V^* a = 0` and `E(a) ≤ E₀`, then

`S(exp(a) V) ≥ c₁ E − c₂ E²`.

So `S ≥ (c₁/2) E` for `E ≤ min(E₀, c₁/(2c₂))`, uniformly in `n`.

**Proof.**
1. **Pointwise smallness for free.** On a lattice, `max_e |a_e| ≤ ‖a‖₄ ≤ C_S E^{1/2}`. So all `|a_e| ≤ r₀` once
   `E ≤ (r₀/C_S)²`. This is where the lattice helps: the critical norm controls the sup norm.
2. **Plaquette angle.** For a plaquette `p` with transported increments `η₁..η₄` (so `|η_i| = |a_{e_i}|`), write
   `e^{η₁} e^{η₂} e^{η₃} e^{η₄} = e^{Θ_p}`. Then `z_p P0 = cos|Θ_p|`, because `z_p V_p = 1`. Second-order BCH with all
   `|η_i| ≤ r₀` gives `|Θ_p − c_p| ≤ K m_p`, where `c_p = Σ η_i = (d_V a)_p` and `m_p = Σ_{e∈p} |a_e|²`.
3. **Lower bound.** Use `1 − cos θ ≥ (2/π²) θ²` for `|θ| ≤ π`, and `(x − y)₊² ≥ (1−δ) x² − δ⁻¹ y²`. Then
   `S ≥ (2/π²) [ (1−δ) Σ_p |c_p|² − δ⁻¹ K² Σ_p m_p² ]`.
4. **Quartic term.** `Σ_p m_p² ≤ 4 Σ_p Σ_{e∈p} |a_e|⁴ = 24 ‖a‖₄⁴`, since each link lies in 6 plaquettes in 4D. By (S1)
   this is `≤ 24 C_S⁴ E²`.
5. **Conclusion.** With `Σ_p |c_p|² = ‖d_V a‖² = E` on the slice:
   `c₁ = (2/π²)(1−δ)`, `c₂ = (48/π²) δ⁻¹ K² C_S⁴`, `E₀ = (r₀/C_S)²`. ∎

With `1 − cos θ ≥ θ²/2 − θ⁴/24` the leading constant becomes `½(1 − δ)`, which matches the numerics.

**Numerical check.** In `scripts/yang_mills_sphere_barrier.py`, the minimum of `S` on `E = R²` is n-independent:
0.42, 2.50, 4.75 at R = 1, 3, 6. The ratio `S/E` falls from 0.42 to 0.13 over that range, as `c₁ − c₂E` predicts.

## (ii) Lattice Uhlenbeck gauge (open)

**Claim.** There are `ε₀, C` independent of `n` such that `S(U) ≤ ε₀` implies: some gauge transformation and center
element bring `U` to `exp(a) V` with `d_V^* a = 0` and `E(a) ≤ C S(U)`.

**Status: open.** Evidence: on cooling paths at n = 4, 6, 8, the global-best Landau gauge (4 center sectors) has
`E/S ≤ 2.41`, flat in n (`scripts/yang_mills_uhlenbeck_test.py`).

The continuum analogue is Uhlenbeck's theorem on small-curvature connections. The lattice difficulty is that small
action bounds plaquettes only in `ℓ²`, not pointwise at scale `n`. The existing Lean route goes through tree gauges and
sup norms, which is what costs `n⁻¹⁰`. A proof would need a continuity method: deform `U` to `V` along the gradient flow
of `S` (which decreases `S`) and keep the Landau gauge by the implicit function theorem, using (i) and the invertibility
of the Faddeev-Popov operator `d_V^* d_U`.

### Reduction of (ii) to an action gap (by hand)

**(ii') Action gap.** Every critical point of `S` with `S < ε₀` is a vacuum, that is, gauge and center equivalent to
`V`. Here `ε₀` is independent of `n`.

**(i) + (S1) + (ii') imply (ii)** by a continuity method:

1. **Flow to a vacuum.** Let `U` have `S(U) < ε₀`. The gradient flow `U_t` of `S` decreases `S`. `S` is real-analytic on a
   compact manifold, so by Łojasiewicz the flow converges to a critical point `U_∞` with `S(U_∞) < ε₀`. By (ii'),
   `U_∞` is a vacuum. Choose the gauge and center element with `U_∞ = V`.
2. **Bootstrap set.** Run the path backwards from `V` to `U`. Let `T` be the set of times `t` at which `U_t` has a slice
   representative `a_t` (`d_V^* a_t = 0`), continuous in `t`, with `E(a_t) ≤ E₁`. Here `E₁ = min(E₀, c₁/(2c₂))` from (i).
3. **Closed.** By (i), `E(a_t) ≤ (2/c₁) S(U_t) < (2/c₁) ε₀`. Choose `ε₀` with `(2/c₁) ε₀ ≤ E₁/2`. Then `E` stays at most
   half its allowed bound, and a limit of slice representatives is again one.
4. **Open.** The slice condition is `d_V^* log(g U g⁻¹ V⁻¹) = 0`, solved for the gauge transformation `g` by the implicit
   function theorem. That needs the Faddeev-Popov operator `d_V^* d_{U_t}` to be invertible. At `V` it is the covariant
   scalar Laplacian, whose lowest eigenvalue is at least `4 sin²(π/2n)`, because the twist leaves no zero mode.
   Perturbing to `U_t` costs at most `C max|a| ≤ C C_S E^{1/2}` relative to the lowest eigenvalue.
5. **Openness without loss.** The sup-norm perturbation in step 4, measured against the lowest eigenvalue (about
   `1/n²`), is not scale-invariant. The relative bound is, and it follows from (S1):
   `|⟨φ, [a, ∇ψ]⟩| ≤ ‖a‖₄ ‖φ‖₄ ‖∇ψ‖₂ ≤ C_S ‖a‖₄ ‖∇φ‖₂ ‖∇ψ‖₂` (Hölder, then the scalar Sobolev bound for `φ`).
   So `d_V^* d_{U_t} ≥ (1 − C C_S² E^{1/2}) d_V^* d_V`, which is invertible for `E ≤ E₁` once `E₁` is small. Then (ii)
   follows with `C = 2/c₁`.

**Evidence for (ii').** Every cooling path in `scripts/yang_mills_uhlenbeck_test.py` (n = 4, 6, 8, β_std = 8) went to
`S < 0.05`, a vacuum. No small-action critical point was met. The cheapest non-vacuum stationary configuration seen is
the barrier at `S ≈ 4.75` (`scripts/yang_mills_sphere_barrier.py`).

So the classical input reduces to two statements on the twisted lattice:
- (S1), a standard discrete Sobolev inequality;
- the action gap (ii'), that no non-vacuum critical point has `S < ε₀`.
Both are scale-invariant, and neither is formalized. (ii') is the genuinely new claim.

**Direct search for (ii') (2026-11-02).** `scripts/yang_mills_action_gap.py` minimizes `|∇S|²` from 36 starts at n = 4
and 6: cooled heatbath configurations, small random lumps of links, and random long-wavelength waves. Every search
ended at an exact critical point (`|∇S|² ≤ 4e-18`):
- either a vacuum, `S ≈ 0` (all cooled and wave starts, and 3 lumps);
- or `S = 12, 24, 36` exactly, the lattice artifacts in which one, two or three links are replaced by `-V_e`. Each of
  its 6 plaquettes then has `zP = -1`, a maximum of the plaquette term.

No critical point with `0 < S < 12` was found. But one exists: the constant-flux 't Hooft saddle, with `S = n⁴(1 − cos(π/n²)) → π²/2` and Morse index 2 (README,
"Constant-flux saddle"). The searches did not reach it. So `ε₀ < π²/2` is forced. Because this saddle has `∇_A F = 0`,
any proof of (ii') must compare the action with π²/2 quantitatively. The collective mountain pass at about 4.75 (sphere barrier) is the
expected lowest non-vacuum critical value, but this search was not aimed at saddles. So (ii') is supported with
`ε₀` below about 4.7.

The flipped-link artifacts are local and cost `exp(-12 β_std)` each, with about `n⁴` positions. On `β_std = b' log n`
that is `n^(4 - 12 b')`, negligible once `b' > 5/12`.

**(S1) numerically (2026-11-02).** `scripts/yang_mills_twisted_sobolev.py` finds the best `C_S = max ‖a‖₄/E^{1/2}` by
preconditioned ascent on `E = 1`, 4 starts:
- n = 4: 0.367; n = 6: 0.360. Flat, no log growth.
- The maximizers are spread out: about 147 of 256 sites at n = 4, 797 of 1296 at n = 6.
- For comparison, a single-link lump gives `1/√8 = 0.354`, and a uniform-modulus lowest mode tends to `1/π = 0.318`.
- n = 8 was stopped unfinished after more than 2 hours.
