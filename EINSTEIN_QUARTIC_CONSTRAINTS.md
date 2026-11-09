# The Einstein quartic requires a constraint and its clock response

Date: 2026-09-11

The selected [tensor parent](TENSOR_VERTEX_SELECTION.md) contains the
supplied cubic but has no construction of the gravitational quartic.
This note addresses that next requirement directly. It gives a local
classical constrained realization of the complete previously derived
quartic, with the correct reduced canonical brackets and forces. The
scalar multiplier agrees with the leading maximal-slicing lapse response.
It also proves why two simpler microscopic interpretations fail.

This is a conditional realization of an Einstein target. Its constraints
and TT input space are supplied, rather than derived from spins. It is
not a selected quantum phase, a new derivation of Einstein's equations,
or a completed TOE. The distinction is essential: adding the auxiliary
constraints below does not remove four of the original six tensor pairs.

## 1. The target and the signs of its sources

Use the compact smooth TT seeds and asymptotically decaying inverses of
[the reduced Hamiltonian](REDUCED_TENSOR_HAMILTONIAN.md). Write

    T=|s|^2, V=|partial h|^2/4, L=-Delta, N=L^(-1),
    A=7T-V, B=T+V,
    K=-Delta I-(1/3)grad div,
    f_i=-(1/2)[s:partial_i h+partial_j[s,h]_ij].

K is positive on the specified decaying vector fields. Let L_0 be the
tracefree symmetric gradient. Integration by parts gives
L_0^* L_0=2K. The rescaled fourth-order energy is

    H_4:=kappa E_4
       = integral [|L_0 W|^2-|[h,s]|_F^2/12-R_4]
         -(1/8)<A,N B>,             K W=f.                 (1)

Here R_4 may be replaced under the integral by the local first-derivative
bulk expression in the preceding note. Brackets below are normalized by
{h,s}_0=Pi_TT and use H=kappa E: the kappa factors in the original
one-form and energy cancel in the classical equations.

The scalar term has the exact decomposition

    -(1/8)<7T-V,N(T+V)>
      =-(1/10)<3T+V,N(3T+V)>
        +(1/40)<T-3V,N(T-3V)>.                            (2)

Its source matrix in the (T,V) coordinates has eigenvalues -1 and 1/4.
It is not negative semidefinite. For example, T=0 gives the positive
term <V,N V>/8 for any nonzero gradient seed.

A stable independent auxiliary coordinate with positive quadratic
operator D and linear source coupling has induced energy

    inf_y [(1/2)<y,Dy>+<y,C rho>]
          =-(1/2)<rho,C^* D^(-1) C rho>.                  (3)

It cannot reproduce (2) by itself. The result applies to this quadratic
elimination mechanism, including any finite number of such channels.
It does not exclude pre-existing source terms, new constraints,
non-Gaussian auxiliaries, or a different joint phase. This specializes
the prior [mediator obstruction](CONSTRAINED_MEDIATOR_TEST.md) to the
actual fourth-order Einstein source matrix.

## 2. The positive channel is not an independent Abelian charge

One might supply the positive term in (2) using a field E with Gauss law

    G=div E-S,                  S=T-3V.                    (4)

Independent electric momenta commute with one another and with h,s.
Consequently {G[N],G[M]}_0={S[N],S[M]}_0. This need not vanish on
G=0. It is not legitimate to replace the tensor sources by commuting
classical charge labels before testing their canonical algebra.

For F_ab[N]=integral N(a T+b V), direct variation on the TT phase space
gives the exact bracket

    {F_ab[N],F_ab[M]}_0
      =ab integral [N s:Pi_TT partial_i(M partial_i h)
                    -M s:Pi_TT partial_i(N partial_i h)]. (5)

Pi_TT acts on the full tensor immediately to its right. In an
unreduced canonical tensor space Pi_TT is replaced by the identity,
and the result reduces to

    ab integral s:partial_i h (N partial_i M-M partial_i N). (6)

For TT fields (6) still follows when either lapse is constant. For
general lapses, multiplication does not preserve transversality and
the projector in (5) cannot be discarded.

A real exact counterexample to first-class closure fits on a flat
three-torus. Normalize its volume to one; let e_ij be a constant unit
TT polarization transverse to z, and take

    h=2 cos(z) e,           s=sqrt(3) sin(z) e,
    N=1,                   M=sin(2z).

Then T=3 sin^2(z), V=sin^2(z), so S vanishes pointwise. With electric E=0
the entire Gauss law (4) is satisfied. Nevertheless (5) gives

    {G[1],G[sin(2z)]}_0=-3sqrt(3) != 0.                  (7)

This is a violation on the constraint surface, not merely a nonzero
off-shell expression. It rules out the independent Abelian Gauss law
(4) with these tensor sources. A larger coupled constraint algebra
would have to be constructed and tested separately.

The TT distinction also has a simple exact Fourier diagnostic. Take

    h=diag(1,-1,0) cos(z),  s=diag(0,1,-1) cos(x),
    N=cos(y),              M=cos(x+y+z).

For a=b=1, (5) is zero whereas (6) is -1/8. The fields are TT, and
all Fourier modes in the calculation are nonzero. Thus the local
stress-density algebra of six unconstrained fields cannot simply be
assigned to the two physical tensor polarizations. This is a familiar
consequence of constraint reduction, not a failure of general relativity.

## 3. A scalar constraint generates the correct energy and force

Introduce a conformal response coordinate u and multiplier n. The
following differential expression is spatially local:

    H_scalar,ext=integral [-A u+n(8 L u-B)].               (8)

Stationarity with respect to n and u gives, respectively,

    8 L u=B,                 8 L n=A,
    u=N B/8,                 n=N A/8.                    (9)

With the stated boundary conditions these solutions are unique. Their
substitution in (8) gives exactly the scalar part of (1).
The Hessian in (u,n) has blocks [[0,8L],[8L,0]] and both signs. Equation
(8) is a constraint saddle, not a stable auxiliary vacuum energy to
minimize. Equation (3) therefore does not apply to it.

Crucially, varying -A u while freezing the solved u gives the wrong
tensor force. The multiplier term retains the response of u to h,s.
For the reduced scalar functional H_N=-(1/8)<A,N B>, its derivatives
before TT projection are

    delta H_N/delta s=-(1/4)s[7 N B+N A],
    delta H_N/delta h=(1/16)partial_i[(N A-N B)partial_i h]. (10)

Varying (8) at fixed u,n and then using (9) gives the same expressions.
The actual tensor equations apply Pi_TT to these derivatives. The
additional N A terms are absent from the frozen-u prescription.

The multiplier has a precise conditional clock interpretation. In
maximal slicing the supplied vacuum lapse satisfies
Delta_q alpha=S_metric psi^(-12) alpha. Transforming this equation
with q=psi^4 gamma and using the scalar constraint gives

    Delta_gamma(alpha psi)
       =(1/8)[R_gamma+7 S_metric psi^(-8)](alpha psi),

where S_metric is the exact momentum square of the preceding metric
reconstruction. Its quadratic part is T. This is the established
conformal lapse equation; see
[Pfeiffer and York](https://arxiv.org/html/gr-qc/0207095v2), Section VI.
Together with psi=1+u+O(degree three), its quadratic expansion gives

    (alpha psi)_2=-N(7T-V)/8=-n,
    alpha_2=-(u+n)=-N T.                                 (11)

Thus precisely the second scalar response required by the canonical
quartic force supplies the leading maximal-lapse correction in the
Einstein reconstruction. This identifies the needed clock response;
it does not derive a microscopic clock or arbitrary-lapse symmetry.

## 4. Localizing the vector term without changing the tensor pairs

Include the three-component coordinate W, the multiplier v, and the
local part H_local,4=integral[-|[h,s]|_F^2/12-R_4]. Set

    H_ext,4=H_local,4+integral [|L_0 W|^2-A u
                              +n(8 L u-B)+v.(K W-f)].    (12)

Stationarity gives (9), K W=f, and

    v=-4W.                                               (13)

Indeed delta_W integral |L_0 W|^2=4KW. With K invertible,
4KW+Kv=0 implies (13). Substituting the solutions into (12) gives
all of (1). The vector energy is also 2<f,K^(-1)f>. Its response
variation is 4<K^(-1)f,delta f>, exactly the contribution -v.delta f
in (12). Local curvature and commutator forces are unchanged.

There is a general symplectic check, which is needed beyond static
energy substitution. Give y=(u,W) conjugate momenta pi_y and impose

    pi_y=0,      chi=mathcal L y-F(h,s)=0,
    mathcal L=diag(8L,K),     F=(B,f).                    (14)

After solving (14), the extended one-form pulls back to

    integral s:delta h+pi_y.delta y = integral s:delta h.  (15)

This remains true even though F depends on both h and s. It preserves
the TT symplectic structure and hence both physical polarizations
already assumed in the input.

For completeness, in a finite-mode realization let D={chi,chi}_0.
In the order (pi_y,chi) the second-class matrix and its inverse are

    C=[[0,-mathcal L^T],[mathcal L,D]],
    C^(-1)=[[mathcal L^(-1)D mathcal L^(-T), mathcal L^(-1)],
            [-mathcal L^(-T),                         0]]. (16)

For observables depending only on h,s their brackets with pi_y vanish;
the zero lower-right block of C^(-1) then gives

    {F_1(h,s),F_2(h,s)}_Dirac={F_1,F_2}_0.               (17)

Noncommutativity of the sources does not spoil (17). It resides in D,
which need not vanish. The same argument applies on the decaying
function spaces where the elliptic inverses and pairings exist.
The general Dirac reduction framework is standard; a self-contained
exposition is [Deriglazov](https://arxiv.org/html/2210.09131v2).

Equations (12)-(17) repair the static-substitution problem for this
quartic localization: both the energy and its reduced Hamiltonian
vector field agree with the target. No finite-time solution of the
nonlinear field equations is asserted. The perturbative truncation
inherits the preceding fixed-profile small-data scope.

## 5. Why this is not yet the microscopic Einstein phase

The four auxiliary coordinates and their four momenta are all removed
by eight second-class constraints. This removes no original tensor
pair. The input was already TT. Starting with the microscopic parent's
six unconstrained pairs would still leave six pairs after (14).
These auxiliary constraints are not the four first-class gravitational
constraints and do not establish the hypersurface-deformation algebra.

Moreover, one cannot quantize (14) by requiring both pi_y and chi to
annihilate a state in the unreduced canonical representation. Their
commutator contains the nonzero scalar operator -i hbar mathcal L^T.
Such a common kernel is zero on the common invariant operator domain.
Dirac reduction before quantization is possible in this prescribed
classical system; realizing it as the low-energy limit of a local
finite-spin Hamiltonian is a separate problem. A sum of squared
second-class constraints is not automatically an exact physical code.

This does not exclude quantum confinement to a band of transverse
oscillators. There is an instructive exactly soluble control. Take one
physical pair (q,p), two auxiliary pairs (a,p_a),(b,p_b), and

    H_pen=(Lambda/2)[p_a^2+p_b^2+(a-gq)^2+(b-gp)^2].       (18)

The four constraints have {a-gq,b-gp}=d=g^2. Their normal frequencies,
divided by Lambda, are

    omega_+=(sqrt(d^2+4)+d)/2,
    omega_-=(sqrt(d^2+4)-d)/2.                            (19)

The remaining two-dimensional zero space is symplectic, preserving one
physical pair. Quantization of this exact quadratic model has a normal
ground-band energy

    E_normal=Lambda hbar sqrt(1+d^2/4).                   (20)

It differs from the commuting-source value Lambda hbar. In this linear
example d is constant, so the difference is only a constant energy
shift. One should neither call it an extra physical potential nor
infer that no quantum physical band can exist.
Here hbar is the control model's canonical quantization parameter;
an application to the rescaled gravitational fields must restore kappa.

For nonlinear sources the tangent constraint matrix generally depends
on the physical background through D={F,F}_0. In a two-source tangent
block with mathcal L=ell I and D=d [[0,1],[-1,0]], the corresponding
quadratic normal energy is Lambda hbar sqrt(ell^2+d^2/4). Its expansion
contains Lambda hbar d^2/(8ell). Quadratic sources have brackets of
degree two, so this expression has a quartic background dependence.
It identifies a quantum correction that a confinement construction
must examine at the same order as (1). This tangent calculation is not
a proved Born--Oppenheimer expansion for the nonlinear Einstein
sources, and no uniform nonlinear band or counterterm is asserted.

The recent permutation-sector selection theorem does not resolve this
issue. It can protect a specified bounded-strength block Hamiltonian;
it does not turn second-class conditions into commuting quantum
constraints, derive the TT quotient, or supply the required lapse.
Likewise the TT-projected bracket in (5) is already spatially nonlocal,
even though (12) is written as a local differential expression.

The modified construction target is therefore a joint spin-metric and
clock constraint phase whose reduction has (9), (11), and (13), with
the original six pairs reduced to two. Its quantum physical space and
locality estimates must be proved, not inferred from matching (12).
The nonzero-G limit, finite-strain control and universal matter coupling
also remain open. Einstein gravity and the TOE remain unproved.

## 6. Verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/einstein_quartic_constraints_audit.py

The report is
[data/einstein_quartic_constraints_audit.json](data/einstein_quartic_constraints_audit.json).
It contains exact identities and 20 numerical cases. It checks the
source signature, saddle and lapse identities,
the on-constraint Gauss counterexample and the distinct TT bracket.
Numerical checks retain the full projected field derivatives, compare
independent elliptic solves, check scalar and vector response forces,
and compare complete Dirac Hamiltonian flows with reduced flows for
noncommuting sources. The quadratic quantum control checks both normal
frequencies and the surviving symplectic pair, rather than inferring
physical dynamics from a static energy alone.

The Fourier field tests remove constant source modes explicitly. They
test operator and variation identities, not asymptotically flat
boundary data or full periodic Einstein solutions. The analytical
statements above instead use the stated decaying inverses. Earlier
completed source files are unchanged. No new Lean theorem is claimed.
