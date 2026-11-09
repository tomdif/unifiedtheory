# A controlled curved spectral window and the microscopic term it omits

Date: 2026-09-10

This stage tests a geometry-dependent regulator on a genuinely curved
finite-matrix family. Two angular-momentum representations give the
known fuzzy approximation to \(S^2(r_1)\times S^2(r_2)\). Its exact
scalar spectrum yields a geometric heat-kernel window, including the
Einstein curvature coefficient and controlled first and second radius
variations. An explicit tail bound specifies how the matrix size must
grow relative to the physical cutoff.

The complete finite Gaussian determinant fails the corresponding
Einstein test. Its second variation along a fixed-volume shape change
is strictly positive, proved mode by mode. The Euclidean Einstein term
with positive Newton coefficient has a negative second variation along
that same path. The ultraviolet contribution omitted by the window
accounts for the difference. A volume counterterm cannot fix it.

Thus a covariant-looking intermediate spectral action cannot be promoted
to a microscopic derivation by discarding its remaining terms. This
result sharpens the regulator matching obligation from
[the lattice tensor test](ISOTROPIC_TENSOR_REGULATOR.md).

The matrix geometry, growing representations, and spectral window are
new supplied benchmark choices. They are not a selected phase of the
repository's four-spin Hamiltonian. Uniform microscopic locality,
Lorentzian reconstruction, general metric variations, gravitational
constraints, Einstein dynamics, and a TOE remain unproved. No new Lean
theorem is claimed.

## 1. A curved finite matrix construction

Take spin \(j_i=L_i/2\) representations \(V_{j_i}\), with the standard
Hermitian angular momentum matrices \(J_{ia}\), and the algebra

\[
 \mathcal A=\operatorname{End}(V_{j_1}\otimes V_{j_2}).
\]

A real scalar is a Hermitian matrix \(\Phi\in\mathcal A\). With the
Hilbert--Schmidt inner product, define

\[
 \Delta\Phi=\sum_{a=1}^3\frac{[J_{1a},[J_{1a},\Phi]]}{r_1^2}
 +\sum_{a=1}^3\frac{[J_{2a},[J_{2a},\Phi]]}{r_2^2}.        \tag{1}
\]

The quadratic form is nonnegative:

\[
 \langle\Phi,\Delta\Phi\rangle
 =\sum_{i,a}r_i^{-2}\|[J_{ia},\Phi]\|_{\rm HS}^2.
\]

The scalar constant matrix is the only zero mode. For the massless
ordinary determinant we omit it, equivalently integrate the trace-free
Hermitian scalar. A positive scalar mass instead makes the whole matrix
strictly positive. The measure is the fixed Hilbert--Schmidt Gaussian
measure; a volume normalization also remains constant on the shape path
used below.

Representation theory gives
\(\operatorname{End}(V_j)=\bigoplus_{\ell=0}^{2j}V_\ell\). Hence the
eigenvalues and real scalar multiplicities are exactly

\[
 \lambda_{\ell k}=\frac{\ell(\ell+1)}{r_1^2}
                  +\frac{k(k+1)}{r_2^2},\qquad
 d_{\ell k}=(2\ell+1)(2k+1),
\]

with \(0\leq\ell\leq L_1\), \(0\leq k\leq L_2\). They coincide
with the product-sphere scalar spectrum through those angular cutoffs.
The audit independently diagonalizes five dense adjoint-Casimir products
through scalar dimension 256 and checks their multiplicities and positive
quadratic forms.

Commutators obey the exact matrix product rule
\([J,\Phi\Psi]=[J,\Phi]\Psi+\Phi[J,\Psi]\). The finite pointwise-algebra
obstruction in [the Ward calculation](MICROSCOPIC_METRIC_WARD.md) does
not apply to this noncommutative product. This alone supplies neither
arbitrary spatial diffeomorphisms nor the normal clock algebra.

Fuzzy-sphere spectra and their intermediate heat-kernel geometry are
established constructions; see
[Sasakura, *Heat kernel coefficients for compact fuzzy spaces*](https://arxiv.org/abs/hep-th/0411029).
The present contribution is the explicit product-family variation and
cutoff-matching audit. The spatial dimension, topology, radii, and choice
of Casimir operator have been supplied, not derived by state selection.

## 2. Heat traces and a bound on their radius variations

Put

\[
 H_L(t)=\sum_{\ell=0}^L(2\ell+1)e^{-t\ell(\ell+1)},\qquad
 K_{L_1,L_2}(s)=H_{L_1}(s/r_1^2)H_{L_2}(s/r_2^2).
\]

The proper-time parameter s has units of length squared. At fixed
finite L, taking s to zero gives the finite scalar dimension, not the
continuum heat-kernel singularity. The geometric window requires
\(sL_i^2/r_i^2\gg1\) while \(s/r_i^2\ll1\).

Here is a uniform cutoff error that also controls variations. Set

\[
 B(t)=1+\frac1t+\frac{3\sqrt\pi}{2\sqrt t},\qquad
 c_0=1,\quad c_1=8/e,\quad c_2=256/e^2+16/e.
\]

Then \(H_\infty(t)\leq B(t)\). For \(\ell\geq1\), integrate over
\(x\in[\ell-1,\ell]\):
\((2\ell+1)e^{-t\ell(\ell+1)}\leq(2x+3)e^{-tx^2}\).
Summing the intervals and integrating the Gaussian proves this bound.

Let \(D=r\partial_r=-2t\partial_t\) at fixed s, and
\(\lambda_*= (L+1)(L+2)\). For n=0,1,2,

\[
 |D^n(H_\infty-H_L)(t)|
 \leq c_n e^{-t\lambda_*/4}B(t/2).                       \tag{2}
\]

Indeed the derivatives of each exponential are respectively
\(e^{-x}\), \(2xe^{-x}\), and \((4x^2-4x)e^{-x}\), with
\(x=t\ell(\ell+1)\). Use
\(x^p e^{-x/4}\leq(4p/e)^p\), extract
\(e^{-t\lambda_*/4}\), and bound the remaining heat sum at t/2.
The same constants without the extracted exponential bound derivatives
of the full or truncated heat sums.

For the product, write its error as
\((H_\infty-H_{L_1})H_\infty+H_{L_1}(H_\infty-H_{L_2})\).
The product rule and (2) bound every first and second log-radius
variation. In particular along \(r_1=re^u,r_2=re^{-u}\), the bounds
for orders 0,1,2 in u have a common factor

\[
 B(t_1/2)B(t_2/2)
 [e^{-t_1\lambda_{*,1}/4}+e^{-t_2\lambda_{*,2}/4}],
\]

multiplied by \(1\), \(2c_1\), and \(2c_2+2c_1^2\), respectively.
No cancellation of numerical tails is needed to establish these bounds.

## 3. The curvature coefficient in the geometric window

Euler--Maclaurin summation gives

\[
 H_\infty(t)=\frac1t+\frac13+\frac{t}{15}
                +\frac{4t^2}{315}+O(t^3).                \tag{3}
\]

This expansion and its first two log-radius derivatives hold uniformly
on compact positive radius intervals. One way to verify the remainder
is to apply Euler--Maclaurin through derivative order eight to
\(f_t(x)=(2x+1)e^{-tx(x+1)}\). Its integral is 1/t; the endpoint terms
give the displayed coefficients. The remainder is bounded by a fixed
Bernoulli constant times \(\int_0^\infty|\partial_x^8f_t|dx\).
After \(y=\sqrt t(x+1/2)\), this is bounded by a constant times t^3
on a bounded positive t interval. Applying the same argument to
\((-2t\partial_t)^nf_t\), n<=2, adds only Gaussian-weighted polynomials
in y and bounded powers of t. This proves the stated derivative control.

For the product geometry,

\[
 V=16\pi^2r_1^2r_2^2,\qquad R=2/r_1^2+2/r_2^2,
\]
\[
 K_\infty(s)=\frac{V}{(4\pi s)^2}
       [1+sR/6+s^2a_4+O(s^3)],
\]
\[
 a_4=\frac1{15}(r_1^{-4}+r_2^{-4})
                    +\frac1{9r_1^2r_2^2}.               \tag{4}
\]

The last expression equals
\((5R^2-2R_{ab}R^{ab}+2R_{abcd}R^{abcd})/360\) on this homogeneous
product, as checked symbolically. These are the standard minimally
coupled scalar heat coefficients; their general geometric setting is
described by [Vassilevich](https://arxiv.org/html/hep-th/0306138v3).
Only this explicit product family is realized and varied by the finite
matrix construction here.

Define the **regulated spectral contribution** of \(N_s\) real massless
scalars between proper-time cutoffs by

\[
 \Gamma_{\Lambda,\mu}^{(L)}
 =-\frac{N_s}{2}\int_{\Lambda^{-2}}^{\mu^{-2}}\frac{ds}{s}K_L(s),
 \qquad 0<\mu<\Lambda.                                  \tag{5}
\]

This is a smoothly weighted spectral window, not a sharp subset of
eigenmodes and not the complete finite Gaussian determinant. The constant
mode contributes a radius-independent term to (5), so its treatment
does not affect the shape derivatives.

First remove the angular cutoff at fixed \(\mu,\Lambda\). Equation (2)
allows the limit to pass through (5) and its first two radius variations.
Then choose \(\mu r_i\gg1\), so the whole window is within (4). The
local terms are

\[
 \Gamma_0=-\frac{N_s(\Lambda^4-\mu^4)}{64\pi^2}\,V,
\]
\[
 \Gamma_1=-\frac{N_s(\Lambda^2-\mu^2)}{192\pi^2}
                              \int\sqrt g\,R,            \tag{6}
\]
\[
 \Gamma_2=-\frac{N_s}{32\pi^2}\log(\Lambda^2/\mu^2)
                              \int\sqrt g\,a_4.
\]

In the Euclidean convention \(S_{EH}=-(16\pi G)^{-1}\int\sqrt gR\),
(6) corresponds to \(G^{-1}=N_s(\Lambda^2-\mu^2)/(12\pi)>0\).
This coefficient matching is not a Lorentzian gravitational
reconstruction or a proof of a propagating graviton. The broader
induced-gravity mechanism is reviewed by
[Visser](https://arxiv.org/abs/gr-qc/0204062).

A simultaneous limit can also be controlled. On a compact radius family
with \(r_i\leq r_{\max}\), set \(\eta=\Lambda r_{\max}>e\), fix
\(\mu=\Lambda/2\), and take

\[
 L_1=L_2\geq\left\lceil\eta\sqrt{24\log\eta}\right\rceil.
\]

At the lower endpoint of the proper-time integral, the exponential in
(2) is at most \(\eta^{-6}\), while the product of B factors is
O(eta^4). Thus the finite-matrix error in the action and its first two
radius derivatives is O(eta^-2). Multiplying by half the logarithmic
window width and the constants after (2) gives an explicit bound.
The continuum remainder after (6) and the curvature-square term is
also O(Lambda^-2) on this family. Matrix size is kept fixed while
differentiating within the radius family.

## 4. A physical shape deformation, with volume fixed

Set \(r_1=re^u\), \(r_2=re^{-u}\). Then V is constant and

\[
 \int\sqrt gR=64\pi^2r^2\cosh(2u).
\]

The Einstein and curvature-square contributions to the shape Hessian are

\[
 \Gamma_1''(u)=-\frac{4N_sr^2}{3}(\Lambda^2-\mu^2)\cosh(2u),
\]
\[
 \Gamma_2''(u)=-\frac{16N_s}{15}\log(\Lambda^2/\mu^2)\cosh(4u).
\]

For \(N_s=r=1,u=0,\mu=\Lambda/2\), the audit finds:

| Lambda | Spectral-window shape Hessian | Einstein contribution |
| --- | --- | --- |
| 4 | -17.589964 | -16 |
| 8 | -65.504818 | -64 |
| 16 | -257.485144 | -256 |
| 32 | -1025.480316 | -1024 |

The curvature-square correction is approximately -1.478714. After
subtracting it, the remaining absolute error decreases by a factor
approaching four on doubling Lambda, as the remainder predicts.
The audit also checks u=0.2, independent finite differences of the
action value, and direct eigenvalue formulas for the window Hessian.

This path changes the scalar spectrum and curvature invariants. It
cannot be generated by the isospectral field-basis rotation of the
previous Ward completion. However it is only a homogeneous Euclidean
shape test. A negative shape Hessian here is not a claim about a ghost
or a Lorentzian instability, and agreement on this family is not a
test of every metric component or of arbitrary wave directions.

## 5. The complete finite determinant has the opposite sign

Keep the matrix size fixed and use its full ordinary scalar integral:

\[
 \Gamma_{\rm full}(u)=\frac{N_s}{2}\sum_{\ell,k}'
 d_{\ell k}\log(A+B+m^2),
\]
\[
 A=\ell(\ell+1)r^{-2}e^{-2u},\qquad
 B=k(k+1)r^{-2}e^{2u}.
\]

The prime removes only the zero mode when m=0. Any fixed dimensional
reference inside the logarithm changes an additive constant and not
the following result. Direct differentiation gives

\[
 \boxed{\Gamma_{\rm full}''(u)=N_s\sum_{\ell,k}'d_{\ell k}
 \frac{8AB+2m^2(A+B)}{(A+B+m^2)^2}>0.}                    \tag{7}
\]

Strict positivity holds when both angular cutoffs are at least one,
since modes with A,B>0 occur. It holds for every real u and every
nonnegative mass. For equal cutoffs, exchange of the spheres also
makes u=0 stationary. Equation (7) is an exact analytical sign result,
verified separately against rational differentiation and finite
differences of the full determinant.

There is also an all-size scaling obstruction. Set equal angular cutoffs
L>=2, m=0, and restrict |u|<=u0. For modes with both angular momenta
between ceiling(L/2) and L, the ratio A/B lies between 1/kappa and
kappa, where \(\kappa=8e^{4u_0}\). Their per-mode factor obeys
\(8AB/(A+B)^2\geq8\kappa/(1+\kappa)^2\). There are at least L^2/4
such pairs, each with degeneracy at least L^2. Conversely, every mode's
factor is at most two. Therefore

\[
 \frac{2N_s\kappa}{(1+\kappa)^2}L^4
 \leq\Gamma_{\rm full}''(u)\leq2N_s(L+1)^4.               \tag{8}
\]

Thus the unwanted shape curvature has fourth-power angular-cutoff
growth. With fixed radii and a separated spectral window it dominates
the Einstein contribution of order Lambda^2. No common normalization
can keep a nonzero finite window Einstein coefficient while suppressing
this full shape response in that limit. The audit checks both bounds
at every window parameter choice; the proof applies to all such L.

An Einstein term with positive Newton coefficient has the opposite
sign along this fixed-volume path. Adding a cosmological constant or
any function of volume cannot change either shape derivative. Thus the
bare Gaussian induction proposal on this fixed-size matrix family fails
this necessary matching test. Additional metric-dependent interactions,
measure factors beyond a volume normalization, or matched counterterms
would change the model and need their own derivation. This is not a
no-go theorem for all matrix models or all renormalized gravity theories.

## 6. The missing contribution can be accounted for explicitly

For a nonzero eigenvalue lambda, let \(p=\partial_u\lambda\),
\(q=\partial_u^2\lambda\). The second derivative of the proper-time
integral from a positive lower limit s0 to infinity is

\[
 F''(s_0)=\frac{N_s}{2}\sum' d\,e^{-s_0\lambda}
 \left[\frac q\lambda-p^2\left(\frac1{\lambda^2}
                                    +\frac{s_0}{\lambda}\right)\right].
\]

The spectral window is \(F''(\Lambda^{-2})-F''(\mu^{-2})\).
The rest splits into

\[
 \Gamma_{UV}''=\Gamma_{\rm full}''-F''(\Lambda^{-2}),\qquad
 \Gamma_{IR}''=F''(\mu^{-2}).
\]

Their sum with the window exactly recovers (7). The audit checks this
decomposition and independently compares F with the heat-trace integral.
In the tested large-matrix cases, the ultraviolet term overwhelms the
negative Einstein-like window. The overall bare shape response cannot
be inferred from that window alone.

This does not contradict the covariance of a proper-time regulator on
a supplied continuum geometry. Fixed angular cutoffs correspond to
different physical momentum limits when the two radii change. The
intermediate window avoids those edges; the complete finite integral
includes them. Specifying that the window is the physical action, or
subtracting the other contribution, requires additional microscopic
matching input. Positivity of the original scalar matrices does not
by itself make that modified spectral functional a positive Lorentzian
microscopic theory.

## 7. Consequence for the TOE program

The constructive result is a curved finite-spin-matrix spectral benchmark
with a controlled geometric window and derivative limit. It demonstrates
how geometric curvature coefficients can appear after the regulator
scales are separated, beyond an isospectral coordinate redundancy.
It also gives an exact countercheck: the whole microscopic determinant
has a different response that cannot be repaired by a volume term.

The next physical construction must explain the complete ultraviolet
matching, not just identify an Einstein term inside a selected window.
It must select the carrier and geometry, provide bounded local microscopic
dynamics, remove unphysical tensor components, and recover the joint
normal/spatial constraint action on geometry and matter. The present
matrix algebra uses growing angular-momentum representations and an
externally assigned Euclidean four-dimensional geometry. No local
embedding into the fixed four-spin lattice with uniform interaction
bounds is established, and no Lorentzian time direction has emerged.

The earlier [conditional Einstein variation](CONTINUUM_EINSTEIN_BRIDGE.md)
and [clock-constraint derivation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
remain conditional benchmarks. This stage does not discharge their
microscopic assumptions or complete the TOE.

## 8. Reproduction

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/geometric_spectral_induction_audit.py
```

The script checks exact heat-coefficient and sign identities, five dense
spin spectra, nine tail/derivative cases, twelve curvature expansions,
eight spectral windows with complete determinant decompositions, and ten
independent variation cases. It writes
`data/geometric_spectral_induction_audit.json` with eight source hashes.
Numerical quadrature estimates are not interval certificates; equations
(2) and (7) have analytical proofs. Earlier sources and reports are
preserved. No Lean source is changed.
