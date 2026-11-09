# Finite-spin state geometry: Berry matching and the missing gauge identification

Date: 2026-09-11

Finite spins can reproduce the preceding prepotential kinetic form
exactly on an open coherent-state chart. A simple spatially local
product-state construction does so, but fails a separate requirement:
three nominal gauge directions per nonzero momentum still change the
physical state.

A global normal-mode encoding fixes that problem. The same family of
finite-spin states then reproduces the Berry form, identifies gauge
parameters as the same state, and has the required quadratic energy
under a specified spin Hamiltonian. Its exact ground-state response
has the prescribed metric pole. The encoding and its momentum-dependent
energies are supplied and spatially nonlocal; they do not derive a
gravitational phase from the local spin dynamics.

An analytical obstruction makes this distinction useful. A uniformly
bounded-depth, finite-range state preparation from a product reference,
with local parameter dependence and exact linearized gauge-ray
identification, has Berry response starting at order |k|^6. It cannot
give the nonzero order-|k|^3 prepotential form under these hypotheses.
This is not an exclusion of general entangled phases, approximate
emergent gauge identification, or preparations whose range or depth
grows in the infrared. Einstein gravity and the TOE remain unproved.

## 1. A physical gauge direction must leave the ray unchanged

For a normalized differentiable family |Psi(z)>, define

    Gamma_ab = <partial_a Psi|(I-|Psi><Psi|)|partial_b Psi>,
    g_ab = Re Gamma_ab,
    A_a = i<Psi|partial_a Psi>,
    F_ab = partial_a A_b - partial_b A_a = -2 Im Gamma_ab. (1)

The sign convention for F follows the displayed definition of A.
These are standard quantum-state geometric structures; see
[Hetenyi and Latorre](https://arxiv.org/pdf/2309.03621).
For a real tangent v,

    g(v,v) = ||(I-|Psi><Psi|) partial_v Psi||².             (2)

Thus v is a state-ray redundancy at first order exactly when
g(v,v)=0. It then lies in the kernel of F. The converse need not
hold: a direction can have zero Berry pairing with every tangent
in a restricted family and still move the state.

Operationally,

    1 - |<Psi(z)|Psi(z+epsilon v)>|²
       = epsilon² g(v,v) + O(epsilon³).                   (3)

This distinguishes a gauge identification from mere degeneracy of
a chosen variational kinetic term.

## 2. Exact finite-spin Berry coordinates

A spin j can be realized in the symmetric sector of 2j spin halves.
For |p|<j and q real, choose the coherent state

    |p,q> = exp(-i q J_z) exp[-i arccos(p/j) J_y] |j,j>.

Its component with m=j-n is

    sqrt[binomial(2j,n)]
    [(1+p/j)/2]^((2j-n)/2)
    [(1-p/j)/2]^(n/2) exp[-i(j-n)q].                      (4)

The coherent-state geometry and its finite-spin realization are
standard; see
[Chryssomalakos, Guzman-Gonzalez and Serrano-Ensastiga](https://arxiv.org/pdf/1710.11326).
Differentiating (4) gives, without a large-j limit,

    A = p dq,         F = dp wedge dq,
    g = j dp²/[2(j²-p²)] + (j²-p²) dq²/(2j).              (5)

The metric is strictly positive on this chart. Product states add
the individual Berry forms and metrics. For directions n,n' on the
spin sphere, their squared fidelity is
[(1+n.n')/2]^(2j); the audit checks this against explicit vectors.

## 3. A local spin family gets the Berry form right

The [prepotential lattice action](PREPOTENTIAL_LATTICE_BRIDGE.md)
has real finite-range matrices O and Q, with

    I = integral dt [P^T O dot Phi
                      - (J/2)P^T QP - (g/2)Phi^T QPhi].   (6)

Use the same staggering to reconstruct Frobenius-normalized local
metric and momentum coordinates:

    p = R_lat P,       q = S_lat Phi,
    R_lat^T S_lat = O.                                   (7)

These reconstruction maps are finite-range real matrices. They
come from the double-curl and symmetric-curl operators of the
preceding note, with the same component phases and half-cell shift.
The audit constructs their local coefficients independently.

Place a spin j on every reconstructed component and set

    |Psi_loc(P,Phi)> = product_s |(R_lat P)_s,(S_lat Phi)_s>.

Restrict to an open neighborhood where every |p_s|<j. From (5),

    A_loc = P^T O dPhi.                                  (8)

This is an exact finite-spin realization of the desired Berry
one-form on that chart. No canonical-commutator approximation or
continuum limit is needed for (8).

It is not yet the physical prepotential state space.

## 4. The quantum metric exposes three false gauge directions

Let D denote the four-column-per-site prepotential gauge matrix
in the preceding lattice note. It satisfies OD=O^T D=0.
At P=Phi=0, the metric of the local spin family is

    g_loc = diag[R_lat^T R_lat/(2j), j S_lat^T S_lat/2].   (9)

It is not null on every direction (D eta,D zeta).
At each nonzero momentum, R has rank three and S has rank four.
The Berry form has rank four, whereas this metric has rank seven.
Exactly three additional directions are distinguishable in the
state metric:

- The scalar shift of P changes p by the original scalar momentum
  gauge shift. That is a nonzero change of spin polarization.
- Two transverse components of the spatial shift of Phi change q.
  They are original metric gauge shifts, but still rotate the
  local spin states.

The remaining prepotential gauge directions really leave (7)
unchanged. On V periodic sites the exact ranks are

    rank F_loc = 4(V-1),
    rank g_loc = 7(V-1),
    rank [diag(D,D)^T g_loc diag(D,D)] = 3(V-1).           (10)

The audit also checks finite displacements: parameter shifts with
zero Berry pairing produce spin-state fidelities strictly below one.
Thus this failure is not a choice of phase convention.

A degenerate time-dependent variational action cannot be interpreted
as a physical gauge quotient solely because its Berry form is
degenerate. The family must either identify those rays or justify
a new physical equivalence through a constructed constrained sector.

## 5. A local preparation bound

Here are the precise hypotheses for the obstruction stated above.
Consider translation-covariant spin-state families with a fixed
finite unit cell and:

1. A product reference acted on by a circuit with uniformly bounded
   depth and gate range.
2. Gate parameters depending smoothly only on a uniformly bounded
   neighborhood of the local P,Phi parameters.
3. Uniformly bounded parameter derivatives as volume grows.
4. Exact linearized gauge-ray identification at the reference state,
   for each of the two prepotential gauge maps D.

Undo the reference circuit after differentiating it. Each resulting
tangent insertion has bounded spatial support on the product
reference. Expand it in non-vacuum product-basis excitations.
There are only finitely many translation classes of such bounded
patterns. Their Fourier amplitudes give a finite matrix A(k)
of Laurent polynomials, with

    Gamma(k) = A(k)^dagger A(k).                          (11)

The component parallel to the reference state has been removed.
For lattices larger than the fixed insertion supports, translated
non-vacuum product patterns can be chosen as orthogonal excitation
bases. This supplies the factorization (11); it is not assumed for
an arbitrary correlated state.

Gauge-ray identification implies A_P(k)D(k)=A_Phi(k)D(k)=0.
Undo the analytic staggering phases. Each row becomes a symmetric
tensor covector a_ij(k) satisfying

    a(k) v(k) = 0,       tr a(k) = 0.                    (12)

Since v(k)=k+O(|k|³), the successive homogeneous Taylor terms are
controlled by the following finite polynomial lemma:

| Homogeneous degree | Unknown coefficients | Exact rank of (12) | Kernel dimension |
| --- | ---: | ---: | ---: |
| 0 | 6 | 6 | 0 |
| 1 | 18 | 18 | 0 |
| 2 | 36 | 36 | 0 |
| 3 | 60 | 55 | 5 |

The table comes from including every monomial of the stated degree
in a symmetric three-by-three matrix, then equating all coefficients
of a(k)k and tr a(k) to zero. Exact rational elimination is an
exhaustive proof for degrees zero through two; no floating-point
rank threshold is involved.

Starting at degree zero and proceeding successively, lower
coefficients vanish, so the higher-order lattice corrections in
v(k) do not change this conclusion. Hence

    A_P(k), A_Phi(k) = O(|k|³),
    Gamma(k) = O(|k|^6),       F(k) = O(|k|^6).           (13)

The last statement follows by antisymmetrizing the real-space
geometric tensor; in Fourier space it involves the corresponding
k and -k tensors, both of the displayed order.

The target O has a nonzero cubic leading term. Therefore a state
family satisfying all four hypotheses cannot reproduce that target
with a nonzero fixed coefficient.

This does not establish that every short-correlated state is
excluded. Finite correlation length alone does not supply (11).
Nor is it a theorem against approximate emergent gauge symmetry:
the size of its state-metric errors on the physically normalized
infrared domain would need a separate estimate. Growing preparation
depth, nonlocal parameter dependence, singular scaling, and a
different constrained or correlated phase are outside the result.

## 6. A global encoding supplies the missing gauge identification

At finite lattice size, take the nonzero singular-value decomposition

    O = U Sigma V^T,       r = rank O = 2(V_sites-1).

Here U,V have orthonormal columns and Sigma is positive. Define

    p0 = Sigma^(1/2) U^T P,
    q0 = Sigma^(1/2) V^T Phi.                            (14)

Then p0^T dq0 = P^T O dPhi. Both parameter gauge maps lie in
the kernels of (14), so they now leave the state coordinates
unchanged, not just the Berry form.

Pulling back the target energy gives a positive canonical form

    H2 = (1/2)p0^T Kp p0 + (1/2)q0^T Kq q0.              (15)

An explicit canonical normal-mode transformation makes this
sum_s omega_s (p_s²+q_s²)/2. For completeness, diagonalize

    Kp^(1/2) Kq Kp^(1/2) = W diag(omega_s²) W^T,

and use

    p0 = Kp^(-1/2) W diag(sqrt(omega_s)) p,
    q0 = Kp^(1/2) W diag(1/sqrt(omega_s)) q.              (16)

The two matrices obey the canonical pairing condition.
The frequencies are precisely the previously specified lattice
values sqrt(Jg)|v_s|. The audit checks the complete Berry and energy
pullbacks as full real-space matrices, including their gauge kernels.

Now assign one genuine spin j to each of these r normal modes,
using the scaled coherent-state chart

    p_spin,s = sqrt(j) p_s,
    q_spin,s = q_s/sqrt(j).                              (17)

On |p_s|<sqrt(j), its Berry form is exactly sum_s p_s dq_s.
The composed finite-spin family therefore has the target Berry
form and exact gauge-ray identification throughout this chart.
At the origin, its quantum metric has the same kernel as the
target presymplectic form.

This encoding is global. Its singular vectors and normal-mode
coordinates are not bounded-range functions of spatial spin
parameters. In the orthonormal TT description, the mode amplitudes
scale as |k|^(3/2), with the necessary polarization rotations.
The metric consequently scales as |k|³, rather than the analytic
factorized |k|^6 behavior in (13). The fractional momentum dependence
exhibits how this construction avoids that local-preparation result.

## 7. One finite-spin Hamiltonian matches its quadratic energy

On the mode-labelled spins, specify

    H_spin = sum_s omega_s (j I - J_x,s).                 (18)

Its ground state is the product with J_x,s=j. In the same coherent
coordinates (17), its exact expectation is

    E = sum_s omega_s
        [j - sqrt(j²-j p_s²) cos(q_s/sqrt(j))].

Its Hessian at the origin is exactly
sum_s omega_s (dp_s²+dq_s²); higher amplitude terms start at
fourth order and are suppressed by 1/j on bounded small charts.
Thus the same state family realizes the target Berry form,
gauge identification, and quadratic energy. Finite-amplitude
nonlinearities in (18) are spin nonlinearities, not Einstein vertices.

There is also an exact finite-spin spectral check, with no
large-j approximation. Set, for one nonzero mode,

    Q_s = J_y,s/sqrt(j),
    h_s = sqrt(J/omega_s) Q_s.

Q_s connects the polarized ground state only to its first excited
level, with squared matrix element 1/2. Consequently

    <h_s h_s>(omega_E) = J/(omega_E²+omega_s²).            (19)

The positive pole is exact for this prescribed mode Hamiltonian.
Its dispersion has been inserted through omega_s, and the metric
observable has a normalization diverging as omega_s^(-1/2).
This is not a pole derived from a spatially local microscopic
Hamiltonian or a bounded local matter bilinear.

For j=2 each mode fits in the existing four-spin quintet. That
dimension match does not localize the global encoder. The compact
code also has enough abstract logical dimension for these modes
and its six homogeneous coordinates, but an abstract Hilbert-space
isometry does not provide a uniformly local implementation.
The homogeneous Einstein dynamics are still missing.

## 8. What the microscopic target now requires

Finite-dimensional spins and the linear gravitational state
geometry are compatible in the global construction. Spatially
local product coherent states instead reproduce only part of
that geometry. The remaining issue is a physical mechanism for
the nontrivial gauge-state identification and the required
kinetic form in a local, selected spin sector.

The next candidate must therefore be checked through its complete
quantum geometric tensor and energy, with the physical observable
map specified. A projected or correlated phase could differ from
the bounded-depth families of Section 5, but its preparation,
energetic selection, and infrared control must be constructed.
Calling Berry-null parameters gauge transformations is insufficient.

The global construction (14)--(19) is an existence benchmark.
It does not justify adding the supplied spectrum to the original
microscopic model and calling it emergent. Local refinement,
uniform physical locality, nonlinear refoliation constraints,
universal matter coupling, homogeneous gravity, the fixed-species
matter curvature limit, Standard Model recovery, and the TOE
remain open.

## 9. Verification

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/spin_state_gauge_geometry_audit.py

[The script](scripts/spin_state_gauge_geometry_audit.py) produces
[the report](data/spin_state_gauge_geometry_audit.json).
It checks four exact rational coefficient systems and 53 numerical
cases: 18 direct single-spin geometries, four complete local-state
pullbacks and gauge-fidelity tests, four global encodings with the
same Berry and energy forms, and 27 exact finite-spin spectral
responses. The reconstruction maps have finite real stencils.

The local-preparation conclusion uses the stated analytical
factorization hypotheses and the exact polynomial lemma. It is
not inferred from the finite examples. No Lean source is changed
or theorem added.
