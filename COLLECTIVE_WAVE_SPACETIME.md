# A controlled collective wave cone in the regulated model

Date: 2026-09-10

The regulated model has a branch with a derived linear collective wave
cone. The derivation uses two additional limits: large spin about a
chosen ordered orientation, followed by a large geometry excitation
gap. Its long-wavelength equation is

```
partial_t^2 phi = 6 kappa [Dbar_x partial_x^2
                          + kappa(partial_y^2+partial_z^2)] phi.
```

The positive tensor Dbar is calculated from a periodic cell problem.
This is a flat Lorentzian **acoustic** cone of one neutral collective
field. It is not a derivation of fundamental spacetime, the physical
spin-1/2 phase, a common cone for all matter, or Einstein gravity.
The new limits and the chosen ordered sector are essential hypotheses.

## 1. A specified extension of the same matter coupling

Keep the separated-switch family G_z: each graph is connected, degree
six, and has N vertices and 3N edges. Its reference cells have side
ell>=12. Write the shifted geometry Hamiltonian as

```
G = sum_s [-b X_s + d n_s + (Omega-d)/2],
b=4rho>0, d=62J>=0, Omega=sqrt(d^2+4b^2).
```

G is positive, has product ground state g, and has gap Omega. In g,
each switch has active probability p=(1-d/Omega)/2. Replace each
matter qubit by a spin S and use

```
H_(S,Lambda) = Lambda G
 - (kappa/S) sum_(uv in G_z) (Sx_u Sx_v + Sy_u Sy_v).   (1)
```

The graph-dependent sum is diagonal in the geometry basis; G still
changes the graph coherently. At S=1/2 and Lambda=1, the matter term
is exactly the previous hard-core hopping, since
`Sx_u Sx_v+Sy_u Sy_v=(b_u^dagger b_v+b_v^dagger b_u)/2`.
At larger S, (1) is a new controlled extension, not a consequence of
the original qubit model.

Choose the aligned +x orientation and fluctuations about it. Neither
preparation nor spontaneous selection of this orientation is proved.
At finite volume the eventual quadratic model has a free global phase
mode, so it does not have a normalizable oscillator ground state in
that mode. Finite-energy wave packets and relative-phase modes are the
appropriate objects below.

## 2. The large-spin limit, including its error and domain

Quantize spin along x. The
[Holstein-Primakoff representation](https://journals.aps.org/pr/abstract/10.1103/PhysRev.58.1098)
on occupations 0<=n<=2S gives

```
Sx=S-n,
Sy=[sqrt(2S-n) a + a^dagger sqrt(2S-n)]/2,
q=(a+a^dagger)/sqrt(2),  pi=(a-a^dagger)/(i sqrt(2)).
```

This is an on-site rotation of the usual z-quantized spin basis. The
raising/lowering order in the square root matters. Set y_S=Sy/sqrt(S).
For input occupations n<=m and 2S>=m+1,

```
||(y_S-q) P_m|| <= m sqrt(m+1)/(sqrt(2) S),
||y_S P_m||, ||q P_m|| <= sqrt(2(m+1)).
```

These follow from `0<=1-sqrt(1-x)<=x` on [0,1], applied to the two
shift coefficients. For a bond, subtract the constant -kappa S:

```
H_bond+kappa S
 = kappa(n_u+n_v) - kappa n_u n_v/S - kappa y_S,u y_S,v.
```

On the two-site input cutoff, its difference from
`kappa(n_u+n_v-q_u q_v)` has norm at most
`kappa(3m^2+2m)/S`. Summing over the 3N edges yields

```
||(H_(S,Lambda)+3kappa SN-H_quad) P_m,all||
 <= 9 kappa N (m+1)^2/S,
H_quad = Lambda G + 3kappa sum_v pi_v^2
          + (kappa/2) q^T L_G q - 3kappa N.            (2)
```

The bound is uniform over all geometry configurations, at fixed N,m.
Degree six is crucial: both the classical energy -3kappa SN and the
coefficient of sum n_v are independent of the switch configuration.
No hidden O(S) force on the geometry has been discarded.

The limit is more than a formal expansion. For every bond, the sum
of squares of spin differences gives
`Sx_u Sx_v+Sy_u Sy_v <= S(S+1)`. Consequently

```
A_(S,Lambda):=H_(S,Lambda)+3kappa SN+3kappa N >= 0.
```

Embed the physical spin space into bosonic Fock space by its occupation
basis; extend A_(S,Lambda) on the orthogonal complement by (2S+1) times
the identity. At fixed finite N,Lambda, these self-adjoint positive
operators converge on the dense finite-occupation core to

```
A_Lambda = Lambda G + 3kappa pi^T pi + (kappa/2)q^T L_G q. (3)
```

On that core, (3) increases total occupation by at most two, with matrix
coefficients bounded by a constant times occupation plus one. Iterating
gives a factorial bound on powers, so every finite-occupation vector
is analytic for (3). The analytic-vector criterion gives essential
self-adjointness; see [Nelson (1959)](https://www.jstor.org/stable/1970331).
For such a core vector psi,

```
(A_(S,Lambda)+i)^(-1)(A_Lambda+i)psi - psi
 = (A_(S,Lambda)+i)^(-1)(A_Lambda-A_(S,Lambda))psi -> 0.
```

The uniform resolvent bound and density of (A_Lambda+i) applied to the
core prove strong resolvent convergence. Spectral cutoff approximation
then gives strong convergence of the unitary groups, uniformly on
compact time intervals. Equation (2) is a core error estimate, not a
volume-uniform dynamical error or a justification of S=1/2 spin waves.

At finite Lambda the operator equations in this limiting model read
`dot q=6kappa pi`, `dot pi=-kappa L_G(t)q`. They do not close as a
scalar-coefficient wave equation: geometry and field remain coupled.

## 3. Eliminate fast geometry by a proved limit

The earlier path-energy comparison gives
`L_0/4 <= L_z <= 4L_0` for every graph. Thus the positive forms in (3)
have a common domain, controlled by the momenta and relative positions.
As Lambda increases they are monotone. Their finite-energy limit
domain lies precisely in ker(G) tensor H_field. The limiting form there is

```
H_ph = 3kappa pi^T pi + (kappa/2)q^T Lbar q,
Lbar = <g|L_G|g> = L_0+p sum_s (L_switched,s-L_0).      (4)
```

In the last sum each difference is the local single-switch correction,
not a repeated subtraction of the entire reference graph. The limit
retains the coherent geometry vector g. It is not a measurement or
collapse of the switches to a classical graph.

The monotone-form theorem, including nondensely defined limits, gives
generalized strong resolvent convergence

```
(A_Lambda+1)^(-1) -> |g><g| tensor (H_ph+1)^(-1).
```

Theorems 4.1 and 4.2 of
[Simon (1978)](https://www.tu-chemnitz.de/mathematik/analysis/kalmes/DAAD_Tunesien_2014_Simon.pdf)
supply the external functional-analysis result. Bounded continuous
functional calculus converges on the limiting subspace. In particular,
for psi=g tensor f, the evolved vector converges to
`g tensor exp(-it H_ph)f`. Uniformity on bounded time intervals follows
by an energy cutoff and density. For finite form-energy input E,
energy conservation also gives the explicit leakage bound

```
||(1-|g><g|) exp(-it A_Lambda)(g tensor f)||^2
 <= E/(Lambda Omega).                                 (5)
```

The energy E=<f,H_ph f> is independent of Lambda. This bound alone
would not control phase errors; the form-convergence argument supplies
the limiting evolution. Equation (4) is therefore a justified average
only in this specified fast-geometry limit. At finite Lambda it is not
the exact quantum field Hamiltonian.

The order of limits is: first S->infinity at fixed N,Lambda, then
Lambda->infinity at fixed N, then the spatial continuum. Finite-volume
results allow a diagonal sequence for finitely many chosen bounded
observables and time windows; there is no proved uniform error rate
for an arbitrary simultaneous limit or the original S=1/2,Lambda=1.
Convergence of unbounded field moments is not inferred solely from
strong unitary convergence; bounded fluctuation observables are safer
for that comparison.

## 4. Compute the spatial stiffness rather than fitting a speed

Lbar is a periodic weighted graph Laplacian. Removed reference bonds
have weight 1-p, new length-two bonds have weight p, and all other
bonds retain their original weights. Let hbar(k) be the ell^3-dimensional
Bloch fiber of kappa Lbar, using microscopic momentum k. Its lowest
band is simple near zero, with constant zero-momentum eigenvector u.
The same energy comparison and contour proof used in the preceding
one-probe calculation give

```
epsilon_bar(k)=k^T Dbar k+R(k),
|R(k)|<=C_b |k|_1^4,      |k|_1<=r_b/2,
(kappa/4)1 <= Dbar <= 4kappa 1,
delta_b=kappa sin^2(pi/ell),
r_b=(1/2)log(1+delta_b/(24kappa)), C_b=delta_b/r_b^4.     (6)
```

Reality removes odd Taylor coefficients. The constants are conservative.
Since only x bonds change, Dbar=diag(Dbar_x,kappa,kappa). With
fbar=hbar'_x(0)u and the inverse taken on u's orthogonal complement,

```
Dbar_x = kappa(1+6p/ell^3)-<fbar,hbar(0)^+ fbar>,
||fbar||^2=20 kappa^2 p^2/ell^3.                       (7)
```

The p^2 in (7) is distinct from p in the earlier full quantum source
norm. At ell=12, rho=0.1, J=0.005, kappa=0.25, the audit gives

```
Dbar_x = 0.250224884717...,  Dbar_y=Dbar_z=0.25.
```

For comparison, the original one-cell quantum probe has
D_x=0.250171277730.... Its coefficient increases toward (7) when both
geometry couplings are multiplied by Lambda at fixed ratio. The
monotonicity follows because the reduced zero-momentum operator
increases with Lambda, its positive inverse decreases, and the source
and ground vector are unchanged. Its limit is the mean-cell reduced
inverse. The numerical check of this statement is for finite probe
fibers; it is not a simulation of the infinite bosonic field.

## 5. A wave continuum with linear clock scaling

For (4), canonical equations close exactly:

```
dot q=6kappa pi,      dot pi=-kappa Lbar q,
ddot q=-6kappa^2 Lbar q.
```

Thus the lowest collective frequency obeys
`omega(k)^2=6kappa epsilon_bar(k)`. At spacing a and macroscopic
momentum p, use the *linear* time calibration t=a t_micro. Define

```
omega_a(p)=sqrt(6kappa epsilon_bar(ap))/a,
omega_cont(p)=sqrt(6kappa p^T Dbar p).
```

For |p|_1<=P and aP<=r_b/2, the difference-of-squares identity and
the lower bound omega_cont>=kappa |p|_1/sqrt(2) give

```
|omega_a(p)-omega_cont(p)| <= 6sqrt(2) C_b a^2 |p|_1^3. (8)
```

At p=0 both frequencies are exactly zero; no division is used. Identify
continuum Fourier modes with the actual lowest-band cell eigenvectors.
Set q_a(0)=J_a f and partial_t q_a(0)=J_a v in the macroscopic clock.
The initial microscopic velocity is consequently a J_a v. The rescaled
microscopic and continuum solutions have factors cos(t omega) and sin(t omega)/omega.
The latter equals t at zero. Since it is the integral of cos(s omega),
(8) proves the cutoff wave-propagator estimate

```
||q_a(t)-J_a phi(t)||
 <= 6sqrt(2) C_b a^2 P^3 [|t| ||f||+(t^2/2)||v||].     (9)
```

This is a controlled second-order wave limit, not an inference from a
maximum-speed envelope. There is also an exact collective zero mode
`q_0(t)=q_0(0)+6kappa t pi_0(0)` in microscopic units.

Eliminating pi from the canonical action, and using the canonical
continuum normalization q_v=a phi(av), pi_v=a^2 Pi(av), gives

```
S_eff=(1/2) integral [chi (partial_t phi)^2
                       - grad(phi)^T Dbar grad(phi)] dt d^3x,
chi=1/(6kappa)>0.                                     (10)
```

The cell corrector in (7) supplies the spatial tensor in (10).
The resulting equation is the one at the start of this note. With
C=6kappa Dbar its characteristic geometry can be represented, up to
a positive constant conformal factor, by

```
ds^2 = -dt^2 + dx^2/C_x + dy^2/C_y + dz^2/C_z.         (11)
```

All C_i are positive, so this metric has Lorentzian signature. Rescaling
each spatial coordinate by sqrt(C_i) turns the equation into the
ordinary flat wave equation. For the audited parameters,
`c_x=sqrt(C_x)=0.612647800188...` and
`c_y=c_z=sqrt(6)kappa=0.612372435696...` in the supplied units.
The cone is acoustic and anisotropic in the original reference coordinates.
No dimensional speed in physical units has been predicted.

## 6. Compatibility with the partial-order clock

At every finite S,N,Lambda, (1) is a sum of bounded local operators.
The [local order-clock construction](LOCAL_CAUSAL_CLOCK.md) therefore
encodes its gate evolution, with work qudits replacing qubits. Gate
unitarity and support bounds still hold. Refine those gates at each
fixed parameter choice before taking the limits above. The collective
wave limit uses linear calibration of those clock readings. It does
not require a second fundamental clock. The previous quadratic scaling
applied to a different, single-particle band and limit.

An important matching problem remains: a gate-dependency order has not
been shown to converge to the acoustic causal order (11). Arbitrarily
small nonzero gates still count as dependencies even when their signal
amplitudes are negligible. The physical partial order, duration
calibration, and effective signal cone must agree in a completed theory;
defining one from another after the calculation is not a derivation of
that agreement.

## 7. Consequence for the proposed theory

The prior positive susceptibility/stiffness criterion now has a concrete
supplier in a specified extension: chi=1/(6kappa), positive Dbar, and
the wave-propagator bound (9). This is a useful controlled benchmark.
It remains a limit about a chosen orientation on a supplied spatial
carrier. It does not prove the relevant phase at physical spin 1/2.

The fast limit makes geometry excitations infinitely costly; the metric
in (11) is constant. There is no massless spin-two mode, curved-metric
dynamics, Einstein equation, universal matter cone, or empirical TOE
prediction here. Finite-gap geometry feedback and the physical ordered
phase are the next dynamical questions, rather than declaring the
acoustic metric to be fundamental gravity.

The executable audit checks spin-half matching, the low-occupation
operator bounds, a finite oscillator fast-gap benchmark, quantum-probe
coefficient convergence, and cell-band wave dispersion. Eleven supporting
Lean results cover algebra and error inequalities. The functional
analysis and continuum arguments above are analytic proofs, not a
claim that the entire field theory has been formalized in Lean.
