# Uniform locality after reference-phase descent

Date: 2026-09-10

**Result.** The canonical reference-phase adjustment in
[REFERENCE_PHASE_DESCENT.md](REFERENCE_PHASE_DESCENT.md) preserves uniform
exponential locality on the growing `L^4` weak-potential domain specified
below. Its scalar phase, and each fixed order of link differentiation, are
bounded by a polynomial in `L` times an exponentially decreasing function
of `L`. This closes the locality obligation left in that earlier note.

The essential identity is exact cancellation for a **pure-gradient change
of reference at fixed endpoint field**. It permits replacing a uniform
reference shift by a distant seam before estimating the corrected phase.
The proof keeps the derivatives of the canonical mean and the finite
cohomology remainder. The spectral and cubical-kernel argument below is
analytic; twelve supporting calculus, geometry, and algebra results are
Lean-checked. This is not a fully Lean-formalized locality theorem.

This result does **not** complete a theory of everything. Section 8 proves
a concrete remaining freedom: two different positive gauge-action
couplings satisfy the same measure conditions and give different weights.

## 1. Domain and precise estimate

Use the supplied five integer hypercharges, their multiplicities, the
specified spin structure, and the overlap Wilson kernel already used in
the repository. Work on cubic four-tori, with all four lengths equal to
`L`, volume `V=L^4`, and a spatially constant flat reference `b`. Let

\[
 W=b+A,\qquad \|A\|_\infty\le\epsilon<1/48.
\]

Constants below may depend on the fixed `epsilon`, differentiation order,
charges, and geometry conventions, but not on `L`, `b`, or the field in
this domain. Derivatives are those of the smooth construction on an open
neighborhood of this closed domain. Gauge orbits of these representatives
are included by the covariance identities. Arbitrary compact logarithm
lifts, nonzero flux, thin-torus limits, and non-Abelian fields are outside
this theorem.

Temporarily regard a constant reference shift `r` as an independent four
vector, with `|r_mu|<=epsilon`. The interpolation

\[
 W_{s,t}=b+s r+t(A-s r),\qquad 0\le s,t\le1
\]

has fluctuations of norm at most `2 epsilon` about a flat field. Its
Wilson gap is at least

\[
 h_*=1-48\epsilon>0. \tag{1}
\]

In particular `epsilon=.018` gives `h_*=.136`; no physical Dirac gap or
inverse is needed. Define the real comparison

\[
\begin{split}
 I(b,A,r)&=\int_0^1ds\int_0^1dt\,(1-t)
          \mathcal F_{W_{s,t}}(A-sr,r),\\
 K(b,A,r)&=I(b,A,r)+C(b+r,A-r)-C(b,A),\\
 C(b,A)&=-\sum_e A_e\bar h_e(b,A),\qquad
 \bar h(b,A)=\int_0^1 h(b,tA)\,dt .
\end{split}\tag{2}
\]

Here `h` is the actual double-descent Ward primitive, including its final
finite summation, and `F` is the summed projector curvature. The convention
is `beta=i Tr(V†dV)`, so a transition is `exp(-i K)`.

The quantitative claim is: for all fixed nonnegative integers `m,k`,
all choices of `m` links and `k` reference components, there are
`C_mk,p_mk,beta_mk>0` (with `p_mk` an integer) such that

\[
 \left|\partial_{A_{e_1}}\cdots\partial_{A_{e_m}}
          \partial_{r_{\mu_1}}\cdots\partial_{r_{\mu_k}}K(b,A,r)\right|
 \le C_{mk}(1+L)^{p_{mk}}e^{-\beta_{mk}L}. \tag{3}
\]

Set `r(A)=mean A` and `f(b,A)=-K(b,A,r(A))`. The sign agrees with the
earlier convention, which integrates from the canonical description to
the original one. Equation (3) will imply the same kind of bound for all
fixed derivatives of `f`, hence locality of `beta_desc=beta-df`.

## 2. Pure-gradient reference changes cancel exactly

For this step extend the formulas to a flat real link field `b`, rather
than only a constant one. Every such zero-flux flat field is a constant
plus a periodic gradient. The density derivatives and the same
field-independent cubical maps define the extension. The gap statements
are applied to its gauge-equivalent bounded representative.

Write `g=B_grad omega`. Under the simultaneous reference/fluctuation change

\[
 (b,A)\longmapsto(b+g,A-g), \tag{4}
\]

the endpoint `W` is unchanged. At any nested radial parameter `u`, the
fields `b+u A` and `b+g+u(A-g)` differ by the periodic gradient `(1-u)g`.
Every density jet is invariant under this change: conjugation by a site
phase leaves its local spin trace unchanged, and the gauge phase is
independent of any additional test-link variations. The field strengths
are identical because `C_curl g=0`.

All maps in the descent are field independent. Consequently the local
pieces of `h`, their divergences, the retained density residual, and its
averaged finite primitive are unchanged. Applying this observation also
at the outer radial parameter proves

\[
 \bar h(b+g,A-g)=\bar h(b,A). \tag{5}
\]

The Ward identity then gives

\[
 C(b+g,A-g)-C(b,A)
 =\langle g,\bar h\rangle
 =\left\langle\omega,\int_0^1\rho(b+tA)dt\right\rangle . \tag{6}
\]

For the triangle flux, covariance and the curvature/Ward identity
`F(B_grad omega,eta)=<omega,delta_eta rho>` yield

\[
 I(b,A,g)=-\int_0^1(1-t)
              {d\over dt}\langle\omega,\rho(b+tA)\rangle\,dt
 =-\left\langle\omega,\int_0^1\rho(b+tA)dt\right\rangle. \tag{7}
\]

The last equality is integration by parts, using `rho(b)=0` at a flat
reference. The `s` dependence drops out by gauge covariance. Equations
(6) and (7) cancel as **real numbers**, giving

\[
 \boxed{K(b,A,B_{\rm grad}\omega)=0.} \tag{8}
\]

There is no omitted flat-reference connection here. The paired flat
orientation has zero determinant connection along constant-flat
variations. Extend it along gradients with the physical gauge action.
The relative fermion/antifermion connection is zero there since the flat
density is zero. Equivalently, for the occupied determinant alone its
extra constant-density term cancels in the supplied sum `sum m q=0`.
Mixed gradient/flat curvature vanishes by the same Ward identity; the
constant-flat curvature is zero by the earlier quaternionic pairing.
Thus the extended flat determinant line is flat and horizontal in the
convention of (2).

The fibre cocycle from the earlier phase proof therefore extends to
these flat reference fields. Its path independence applies on the convex
lifted domain of bounded constant representatives plus arbitrary periodic
gradients. Combining it with (8) gives, for any allowed flat `r,g`,

\[
 K(b,A,r+g)=K(b,A,r),\qquad g=B_{\rm grad}\omega. \tag{9}
\]

## 3. Move the shift to a seam far from a differentiated link

Fix one of the differentiated links `e`. Choose periodic sawtooth
coordinates `y_mu(x)` centered at its head. Their backward differences
are `1-L c_mu(x)`, where `c_mu` indicates the opposite cut. With

\[
 \omega_r(x)=\sum_\mu r_\mu y_\mu(x),\qquad
 S_\mu(x)=L r_\mu c_\mu(x),
\]

one has `r=S+B_grad omega_r`, `C_curl S=0`, and

\[
 K(b,A,r)=K(b,A,S). \tag{10}
\]

The seam geometry depends on `e` and `L`, not on the field or reference
parameters, so it can be held fixed while differentiating. Its endpoints
are at maximum-coordinate distance at least `L/2-3` from `e`. Its amplitude
is at most `L epsilon`; derivatives with respect to `r` cost factors of `L`.
These factors will remain polynomial, not be hidden in uniform constants.

Large seam potentials do not invalidate (1): at every `s,t`,

\[
 b+sS+t(A-sS)
 =b+sr+t(A-sr)-s(1-t)B_{\rm grad}\omega_r. \tag{11}
\]

They are gauge equivalent to the bounded uniform-reference path. The same
holds for every nested radial field used in `h`. Also
`C_curl(A-sS)=C_curl A`, so all explicit field-strength factors in the
descent stay uniformly bounded.

## 4. A locality bound with an additional marked seam

Here is the quantitative transfer needed beyond the earlier unmarked
locality argument. It is useful to allow polynomial volume factors in
this intermediate estimate; the seam separation will absorb them.

With `alpha=log(1+h_*/8)`, the weighted-resolvent proof gives

\[
 \|R_t(x,y)\|\le
 2e^{-\alpha d_1(x,y)}/\sqrt{h_*^2+t^2}. \tag{12}
\]

Projector locality itself also follows from the even resolvent pair:
`R_++R_-=-2 R_+ H R_-`. The weighted norm of the nearest-neighbor `H` is
uniformly bounded, so this representation is integrable in `t`. The
identity term in `P` is supported on the diagonal. Derivatives insert
finite-support link vertices into these chains; a repeated-link vertex
is included whenever multiple derivatives hit the same link.

When two background fields differ only on a seam, the resolvent identity
inserts their operator difference on that seam. Differences or derivatives
of the link vertices themselves also have seam support. Thus a difference
of density-jet kernels has the bound

\[
 C_m(1+L)^p
 \sum_{z\in\mathrm{seam}}e^{-\alpha\,operatorname{diam}_\infty(X\cup\{z\})}.
 \tag{13}
\]

`X` contains the density site, every explicit kernel anchor, and all test
links, using their endpoints up to a fixed one-step loss. A closed
resolvent chain visits all these insertions; its length controls this
diameter. Any fixed additional `A` or `r` derivatives preserve a seam
insertion and change only constants and powers. Uniform differentiability
and (1) justify the integral formulas at every step.

For clarity, the following finite geometric rules carry (13) through the
**actual** cohomology construction:

1. An entry of a centered homotopy has coefficient `0,+1,-1`. If its input
   anchor has radius `u` about the retained center and its output has
   radius `v`, then `v<=u`. For a marked site at distance `R` from the
   center and distance `D` from the output, `D<=v+R`. In particular
   `D<=2 max(u,R)` and `u+D<=3 max(u,R)`. An output anchor is therefore
   within at most twice the old marked diameter of the retained anchors.
   Replacing anchors weakens the exponent by a fixed factor. Summing
   coefficients costs at most `16V` per homotopy if the sharper lattice
   sum bound is not used.
2. Boundary maps shift an anchor by one step and have a bounded number
   of terms. Diagonal anchor identification does not enlarge the marked
   set. Removing an anchor by summation cannot enlarge its diameter and
   costs at most `16V`. These statements apply to the first descent map
   `S`, to `H_x,H_y`, and to the top-diagonal subtraction in the second
   descent. In each homotopy its center is another anchor of its input.
3. Contracting a kernel with an undifferentiated field strength costs a
   uniform factor and a finite site sum. If a derivative hits that field
   strength, the differentiated link lies on its plaquette: it is within
   one step of the contracted anchor. It can therefore replace that
   anchor in (13). Higher derivatives of the linear field strength vanish.
   The shifted cap product in `h_2` only adds a one-step anchor shift.

There are at most two centered homotopies along a term of `h_1` and five
along a term of `h_2`: the initial map `S`, then the longest branch through
`T,U,V,L`. Thus their diameter losses are bounded by `2^5`, independently
of volume or differentiation order. Boundary and cap shifts cost fixed
additive distances; their constants may depend on the derivative order.
Iterate the displayed coefficient and diameter rules, and sum the finitely
many product-rule terms at the chosen differentiation order.
This proves (13), with some positive exponent and polynomial prefactor,
for the local part of the primitive, with its output link retained in `X`.
It covers derivatives hitting explicit field strengths as well as those
hitting density kernels. No assumption that a finite summation is local
has been made.

The remaining piece `h_fin` is handled separately. The prior second
descent and toron-extension estimates bound all its fixed field and flat
reference derivatives by `C poly(L) exp(-beta L)`. Apply those estimates
to the bounded uniform representatives on the right of (11). Identity
(5), which applies to each piece of the descent, transfers them to the
seam representatives. A derivative in a uniform shift is a sum of link
derivatives and a flat-reference derivative; converting the latter from
`theta` to `b=theta/L` costs another factor of `L`. These are polynomial
losses. **We do not claim seam support for `h_fin`.**

## 5. Bound the complete phase, including both endpoint corrections

First suppose `m>=1`, and choose the seam opposite `e_1` as in section 3.

In the differentiated triangle flux, an `A` derivative either hits the
explicit tangent `A-sS`, or inserts its link into the curvature kernel.
In both cases each term visits `e_1` and a seam link from the second
tangent `S`. Reference derivatives act on seam fields or tangents and
retain such a mark. The differentiated projector-curvature trace has the
same closed-chain bound as (13). Summing all unmarked links and bounding
the tangent amplitudes gives `C poly(L) exp(-beta L)`.

For the scalar terms let `h_i=bar h(b,A)` and
`h_j=bar h(b+S,A-S)`. Use the exact decomposition

\[
 C_j-C_i=\sum_x S_x(h_j)_x
          -\sum_x A_x\big((h_j)_x-(h_i)_x\big). \tag{14}
\]

In its first sum, the output link is on the seam. Every `A` derivative
acts on `h_j`, so its local derivative kernel joins that output to `e_1`.
Reference derivatives contribute sums of additional bounded-representative
field derivatives and powers of `L`; the same marked bound still applies.
The finite piece of `h_j` is already volume-small.

In the second sum, the difference of local kernels has a seam mark:
their nested backgrounds differ by `(1-u)S` (with `u` the product of
radial parameters), and their explicit field strengths coincide. If the
derivative at `e_1` hits the external `A_x`, it pins `x=e_1`. Otherwise
it marks a kernel or a field-strength factor inside `h_j-h_i`. Section 4
covers both cases and joins `e_1` to the seam. The summation over `x`
costs only a polynomial volume factor. The difference of finite pieces
is bounded by the sum of their volume-small bounds. This establishes
(3) for `m>=1`, including all mixed reference derivatives.

To obtain the cases with `m=0`, observe that

\[
 K(b,0,r)=0 \quad\hbox{for every allowed flat }r. \tag{15}
\]

Indeed all triangle fields and tangents are flat, their determinant
curvature vanishes, and the primitive is zero because the field strength
and flat density vanish. Consequently all pure `r` derivatives of (15)
vanish. Integrate their `A` derivative along `tA` from zero to the desired
field. The already proved `m=1` estimate bounds every term, and contraction
with `A` costs at most `4V epsilon`. This proves (3) also for `m=0`.

## 6. The global mean and the local descended current

For an edge `e` in direction `mu`, differentiation after `r=mean A` acts as

\[
 D_e=\partial_{A_e}+V^{-1}\partial_{r_\mu}. \tag{16}
\]

The mean is linear, so these constant-coefficient operators commute and
its higher derivatives vanish. An order-`m` derivative expands into
`2^m` mixed derivatives controlled by (3), with coefficients `V^{-j}<=1`.
In particular, for directions `mu,nu`,

\[
 \partial_e\partial_f f=-\left[
 K_{A_eA_f}+V^{-1}K_{A_e r_\nu}
 +V^{-1}K_{r_\mu A_f}+V^{-2}K_{r_\mu r_\nu}\right]_{r=\operatorname{mean}A}.
 \tag{17}
\]

The final term uses the `m=0` result from (15). Discarding it, or inferring
exponential locality from the factor `1/V` alone, would be incorrect.

At fixed differentiation order a polynomial can be absorbed into half
the exponential decay rate. Thus `|partial_e partial_f f|<=D exp(-beta L)`
with adjusted positive constants. The torus has `d_1(e,f)<=2L`, so

\[
 |\partial_f\partial_e f|\le D e^{-(\beta/2)d_1(e,f)}. \tag{18}
\]

The previous fixed-reference current already has a uniform local response:
the radial part follows from its projector chains, and the scalar part
from the local derivatives of `h` contracted with bounded `A`. Adding
(18) proves, with `j_e^{desc}=beta(0,e)-partial_e f`,

\[
 \boxed{|\partial_f j_e^{desc}|\le C e^{-\nu d_1(e,f)},\qquad \nu>0,}
 \tag{19}
\]

uniformly in the stated domain and volume. The same argument works at
each fixed higher derivative order, using the maximum separation from
the output link. The previous exact phase proof already established Ward
preservation, unchanged projector curvature, and consistency under equal
real-potential descriptions. Equation (19) supplies its missing locality
estimate. It does not change the scope of its compact-sector obligations.

## 7. Verification and provenance

The new executable independently evaluates the actual weighted primitive
with a spatially varying flat base, and the triangle flux with a general
flat shift. It tests a pure-gradient change of reference and compares a
uniform shift with its seam representative at the same physical field.
It also reproduces the previous nonzero uniform comparison. These tests
can detect a wrong sign or an omitted scalar correction; their finite
residuals are not the proof of the all-volume estimate.

The geometric audit applies the actual homotopy to every input basis in
degrees zero through three at two centers on `3^4` and `4^4`. For every
nonzero output it checks the marked-radius and marked-diameter inequalities
against **every marked site**, in exact bounded integer arithmetic. A
separate exact symbolic check differentiates a polynomial comparison
through the mean and verifies all four Hessian terms in (17).

The run gives a pure-gradient comparison of `-4.6581e-16`, from a nonzero
flux of `5.7637e-7` canceled by the endpoint scalar corrections. Uniform
and seam comparisons agree to `6.2517e-16` and reproduce the previous
uniform phase to `2.0444e-16`. All 10,110 input basis vectors and 4,474,240
marked-output inequalities pass. For the action witness the plaquette
cost is `0.00753786318`, giving weights `0.9924904753` and `0.9850373435`.

The Lean module proves integration by parts in (7), the resulting Ward
cancellation with its physical identities supplied explicitly, seam
replacement from the fibre cocycle, the marked geometric inequalities,
their exponential consequence, (14), a finite chain-rule sum bound,
integration of a small derivative, preservation of an exponential response,
and the two action-freedom facts below. The overlap functional calculus,
the identification of the implemented homotopies, and their complete
composition into (3) remain the analytic proof above.

The full repository build passes with 8,927 jobs. All twelve new Lean
results report only `propext`, `Classical.choice`, and `Quot.sound`; the new
module has no unfinished proofs or warnings.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/uniform_reference_locality_audit.py
lake env lean UnifiedTheory/Audit/KFCausalUniformReferenceLocality.lean
lake build
```

Lean/Lake commands must run sequentially with other jobs in this repository.
The report `data/uniform_reference_locality_audit.json` records the diagnostic
values and source hashes. Prior hashed proof notes are left unchanged;
this note supersedes their stated open obligation for this phase's locality.

Finite-volume locality estimates based on winding resolvent chains are
part of the existing Abelian chiral-measure literature; see section 11 of
[Lüscher's construction](https://arxiv.org/html/hep-lat/9811032v2).
The work here checks their application to this repository's particular
reference phase and finite descent. No new general anomaly-classification
or quantum-gravity theorem is claimed.

## 8. What this proves about the proposed TOE

The locality result supplies a property of a chiral measure on a supplied
lattice. It does not select the action of that theory. This distinction
has an explicit witness. Keep this fermion measure and define

\[
 S_\lambda(A)=\lambda\sum_p[1-\cos((C_{\rm curl}A)_p)],
 \qquad w_\lambda(A)=e^{-S_\lambda(A)},\quad \lambda>0. \tag{20}
\]

Every member is a local gauge action: `C_curl B_grad=0` proves periodic
real-gauge invariance, and the cosine also respects compact plaquette
angles. The usual plaquette sum has the ordinary lattice gauge-action
symmetries. Its coupling has no effect on the constructed fermion
measure's Ward, projector-curvature, reference-consistency, or locality
properties. We do not infer additional fermion-measure symmetries here.

Choose a weak field with at least one nonzero plaquette angle. Its
`s=sum_p(1-cos F_p)` is strictly positive in this domain. Then

\[
 0<e^{-2s}<e^{-s}. \tag{21}
\]

Thus the choices `lambda=1` and `lambda=2` give different relative
configuration weights while satisfying the same measure conditions.
Because the cost varies with the field, the difference is not merely a
constant normalization. The executable supplies such a field, and Lean
proves gauge invariance under a curl-free increment and the strict
inequality (21).

This is an underdetermination result for the current hypotheses, not a
no-go theorem for all future unification proposals. Additional principles
and physical evidence must select dynamics. The full compact/nonzero-flux
and non-Abelian measure, its intended symmetries, a controlled continuum
limit, dynamical spacetime with Einstein gravity, and quantitative physical
predictions are still absent. Consequently a TOE cannot be concluded from
the uniform-locality theorem proved here.
