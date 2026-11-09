# Compact loops and a flat reference determinant orientation

Date: 2026-09-10

The bounded weak-chart construction in
[SECOND_COHOMOLOGY_COMPLETION.md](SECOND_COHOMOLOGY_COMPLETION.md) now has
two further ingredients for compact-field assembly:

1. The exact Kato holonomy of every integer on-site gauge loop agrees with
   the phase required by its corrected Ward equation. This holonomy need
   not be one on a curved background.
2. On the entire flat Wilson-line torus, the overlap projector has a
   canonical determinant orientation. Its determinant connection has zero
   curvature and trivial winding holonomy, separately for every integer
   charge. No physical Dirac-gap assumption or charge cancellation is needed
   for this restricted result.

This is an analytic construction with exact spin-matrix checks, numerical
operator/transport checks, and eleven Lean algebraic results. The momentum
decomposition, differential equation, and full bundle argument are not
assembled as a Lean theorem. It does **not** finish the interacting compact
measure or the physical TOE. A separate control below shows why the previous
zero-potential cancellation cannot simply be copied to every flat reference.

## 1. Conventions and what is being transported

Use the existing four-dimensional rectangular periodic lattice, with either
periodic fermions or antiperiodic time. Link potentials are at the head of
an edge: a gauge change adds `omega(head)-omega(tail)`. For integer charge
`q`, let `H_q` be the repository's mass-one Hermitian Wilson kernel,
`P_q=(1+sign(H_q))/2` its positive projector, and
`Pbar=(1+gamma5)/2`. The anomaly convention is

\[
a_q(x)=q\,\operatorname{tr}_{spin}(P_q-\bar P)(x,x).
\]

The measure connection is `i Tr(V† dV)`. Kato transport satisfies
`Qdot=[Pdot,P]Q`, `Q(0)=1`. Its closed occupied-frame holonomy is
`det(V0† Q(T) V0)`. A path closing up to a gauge transformation `G` instead
uses `det(V0† G† Q(T) V0)`. This convention is essential for winding loops:
the uniform potential does not literally return to itself.

## 2. Compact gauge loops: the Ward equation fixes a nontrivial phase

Let `n(x)` be any integer-valued function, `X=iq n`, and
`G(t)=exp(tX)` for `0 <= t <= 2pi`. Then `G(2pi)=1` and
`P(t)=G(t) P G(t)†`. Put

\[
X_d=PXP+(1-P)X(1-P).
\]

The identity

\[
[[X,P],P]-X=-X_d
\]

gives the exact solution `Q(t)=G(t) exp(-t X_d)`. In an initial occupied
frame, it reads

\[
Q(t)V=G(t)V\exp[-t(V^\dagger X V)].
\]

Differentiating proves the Kato ODE; its compressed derivative is zero,
so the displayed frame is horizontal. At the endpoint,

\[
\begin{aligned}
\det(V^\dagger Q(2\pi)V)
 &=\exp[-2\pi i q\operatorname{Tr}(nP)]\\
 &=\exp[-2\pi i\sum_x n(x)a_q(x)].
\end{aligned}
\]

The reference contribution is `q Tr(n Pbar)=2q sum_x n(x)`, an integer.
For a multiplet, multiply the determinants with their multiplicities.
The corrected weak-chart connection obeys `J(Bn)=-sum_x n(x)a(x)`;
the density is constant along the gauge orbit. Thus its integrated phase
is exactly the Kato phase above. The Wilson gap stays unchanged along this
orbit even when its real potential lift leaves the bounded chart.

This establishes the loop compatibility condition in gauge directions.
Requiring the occupied Kato holonomy itself to equal one on all backgrounds
would impose an incorrect extra condition.

## 3. A quaternionic orientation on all flat Wilson lines

Represent a flat reference by `A_mu=theta_mu/L_mu`, with each
`theta_mu` an angle modulo `2pi`. Fourier transformation splits the kernel
into independent four-spin blocks. For momentum
`p_mu=2pi(n_mu+b_mu)/L_mu`, where `b_3` is zero or one half,

\[
k_\mu=p_\mu-q\theta_\mu/L_\mu,\qquad
H(k)=\sum_{\mu=0}^3\sin k_\mu\,\Gamma_\mu+
       (3-\sum_\mu\cos k_\mu)\Gamma_4,
\]

where `Gamma_mu=i gamma5 gamma_mu`, `Gamma_4=gamma5`. These five matrices
are Hermitian Clifford generators. With `u_mu=1-cos(k_mu)>=0`,

\[
H(k)^2=r(k)^2 I,\qquad
r(k)^2=1+2\sum_{\mu<\nu}u_\mu u_\nu\geq1.
\]

Consequently the positive projector `(I+H/r)/2` is smooth for **all** flat
holonomies, all integer charges, and all these lattice sizes. Each block
has rank two. There is no restriction on `|theta_mu/L_mu|`. The physical
overlap Dirac operator can still have zero modes; it is not inverted.

For the repository's spin conventions define the antiunitary

\[
\mathcal J=J_s K,\qquad
J_s=\gamma_5\gamma_1\gamma_3=
\begin{pmatrix}0&1&0&0\\-1&0&0&0\\0&0&0&1\\0&0&-1&0\end{pmatrix}.
\]

Here `K` conjugates coefficients **at fixed momentum label**. The exact
identities are `J_s J_s†=I`, `J_s conjugate(J_s)=-I`, and
`J_s conjugate(Gamma_a) J_s†=Gamma_a` for all five generators.
Thus `J²=-I` and `J` commutes with every flat projector and its flat
parameter derivatives.

Choose a local normalized occupied vector `v`. Its partner `Jv` is
orthogonal to it, and the two span that momentum's occupied space. Any
other paired frame has transition matrix

\[
(w,\mathcal Jw)=(v,\mathcal Jv)
\begin{pmatrix}a&-\bar b\\b&\bar a\end{pmatrix},
\qquad |a|^2+|b|^2=1.
\]

Its determinant is one. Therefore `v wedge Jv` is independent of the
local vector choice and glues smoothly even where that vector chart fails.
Taking the product over momenta gives a canonical unit determinant section.
Exchanging two momentum blocks exchanges two pairs of columns and has
positive sign. This argument proves determinant triviality without
asserting the existence of a global smooth frame of all occupied vectors.

The section is horizontal: `v†dv + (Jv)†d(Jv)=0`. Equivalently Kato
transport preserves the paired form and every endpoint transition has
unit determinant. The determinant curvature vanishes as well. Indeed,
`Tr(P[dP,dP])` is imaginary by Hermiticity and real by antiunitary
similarity, so is zero. The exact spin audit also checks all 125 traces
`Tr(Gamma_a Gamma_b Gamma_c)=0`.

Under `theta -> theta+2pi m`, with integer four-vector `m`, the identifying
gauge transformation is

\[
G_q(x)=\exp(2\pi i q\sum_\mu m_\mu x_\mu/L_\mu).
\]

In the fixed Fourier convention it is the **real permutation** of momentum
blocks by `q m`. It commutes with `J` and preserves the paired determinant
orientation. Thus every flat loop, including winding loops, has
endpoint-identified determinant holonomy exactly one. Its full rank-two
transport can be nonidentity; vanishing determinant curvature says nothing
about vanishing non-Abelian Berry curvature.

The physical Weyl measure involves the relative line
`det(P) tensor det(Pbar)*`. For these winding identifications the reference
factor also equals one:
`det(G_q|Pbar)=exp(2pi i q sum_mu m_mu (V/L_mu)(L_mu-1))=1`.
For a constant gauge transformation the two equal ranks cancel its action
in the relative line. The occupied determinant line alone should not be
declared invariant under arbitrary constant gauge transformations.

This antiunitary is a property of the flat momentum family. In position
space its fixed-momentum conjugation involves spatial inversion/Fourier
structure. It is not a new local symmetry of arbitrary charged backgrounds,
and it neither adds opposite-charge fermions nor makes the chiral spectrum
vectorlike. No cubic charge cancellation is used in this flat result.

## 4. The remaining interacting extension is substantive

The gap argument extends immediately to `A=theta/L+a` with bounded weak
fluctuation `a`: the same perturbation estimate gives
`gap(H)>=1-24||a||infinity` for the supplied `|q|<=6`, uniformly in `theta`.
This supplies a spectral starting point for contraction of `a` at each
flat reference. It does not complete the measure current on those charts.

In particular, the earlier proof used
`a_q''(0)=q^3 a_1''(0)` and `sum multiplicity*q^3=0`. At a general flat
reference the identity is instead

\[
\delta^2 a_q(\theta/L)[\eta,\zeta]
 =q^3\,\delta^2 a_1(q\theta/L)[\eta,\zeta].
\]

The arguments on the right differ between charges. The finite-volume
Hessian need not cancel. With the explicitly seeded two directions in the
audit on `2^4`, its summed norm is about `5.16e-14` at zero holonomy and
`4.6897` at `theta=(.37,-.29,.43,.61)`. Its total over sites remains zero.
These are derivative coefficients for the stated directions, not anomaly
values at a finite fluctuation.

This control disproves exact cancellation of that entire Hessian at an
arbitrary toron. It does **not** prove a nonzero topological obstruction or
show that the final descended top coefficient fails to cancel. A next
construction must control the holonomy-dependent finite-volume terms,
construct the current with the required symmetries, and match its transition
phases on overlaps. Flat reference orientation by itself is insufficient.
Nonzero flux sectors, non-Abelian fields, physical continuum limits, and
gravity remain further obligations.

## 5. Reproducible evidence and formal scope

Run, sequentially with other Lean jobs in this repository:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/compact_measure_holonomy_audit.py
lake env lean UnifiedTheory/Audit/KFCausalCompactHolonomy.lean
lake build
```

The JSON report in `data/compact_measure_holonomy_audit.json` records source
hashes, exact symbolic identities, 44 flat loops (the five supplied charges
in four directions on two tori, plus closed curved and mixed-winding paths),
dense position/Fourier agreement, endpoint gauge checks for both time
boundary conditions, gauge-loop refinement, and the extension control.
The species are the supplied `q=6Y` multiplet; its non-Abelian background
is held at identity.

For the compact gauge loop at the selected site, the predicted phase is
`6.16626e-6` radians. The exact closed-form Kato/Ward comparison differs
by about `1.8e-15`; independent projector transports with 128, 256, and
512 steps have errors `6.76e-8`, `1.68e-8`, and `4.20e-9`. The nonzero
phase is resolved, and the convergence has the expected factor of four.
The flat determinant tests are at floating roundoff; their all-angle
justification is the paired-orientation proof, not sampling.

The eleven Lean results prove the rotating gauge generator, integer phase
removal, free-gap polynomial and inequality, rank-two transition determinant,
paired permutation sign and full block determinant, and the trace/curvature
implications of antiunitary similarity. The explicit gamma realization and
analytic Kato/bundle construction remain separately checked arguments.

## Relation to established work

This is a repository implementation and verification step, not a claim to
have discovered anomaly-free Abelian lattice gauge theory. Lüscher's
[Abelian chiral gauge theories on the lattice with exact gauge invariance](https://arxiv.org/abs/hep-lat/9811032)
already establishes its existence under stated hypotheses. Sections 7–10
explain the flat Wilson-line coordinates, determinant bundle, and need to
match loop phases as well as local curvature. Section 10.3 treats compact
gauge loops. Our flat proof uses the explicit overlap momentum spin matrices.
That literature result cannot substitute for verifying the locality,
symmetry, and domain hypotheses of this repository's particular current.
