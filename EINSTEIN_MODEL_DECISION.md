# Can the present spin program reach Einstein gravity?

**Scope:** metric-sector assessment originally recorded in October 2026.
The duplicated progress feed has been removed. This note retains the metric
argument and its numerical evidence; [STATUS.md](STATUS.md) and the
[current research plan](TOE_COMPLETION_PLAN.md) govern the current program.
No physical Einstein/Standard-Model identification follows from this note.

## 1. What can be retained, and what actually needs changing

The four-spin cell already contains the scalar and five tensor
transitions needed to label six symmetric collective coordinates.
The spin-block calculation supplies a restricted canonical limit, and
the logarithmic calculation supplies one positive metric component and
its dilation action on a controlled input domain. Those are useful
kinematic ingredients. Their carrier, spin-to-space identification,
large-block sector, and state selection still contain supplied inputs.

The uncoupled seed at mu>0 instead has an exact gap and five internal
polarizations. Tuning its one-particle gap to zero gives quadratic
dispersion. Adding a trace coordinate gives six candidate fields; it
does not generate the four gravitational constraints. The exact energy
bracket of the later model produces a spin-dependent matter current,
but not the complete total spatial generator. These are different
diagnostic Hamiltonians, not one already unified construction.

An interacting critical phase could have different collective physics.
We have not ruled that out, and have not proved that it occurs anywhere
in the current parameter families. My recommendation to change the
Hamiltonian is a research judgment based on the demonstrated gaps, not
a theorem excluding all strong-coupling phases of these spins.

A coordinate change alone cannot achieve that phase transition. Around
a stationary background, let an invertible field redefinition have
Jacobian J. A quadratic inverse propagator transforms as

```
K_new(omega,k)=J^T K_old(omega,k) J,
det K_new=(det J)^2 det K_old.
```

Its zeros and rank are unchanged. With the corresponding canonical
momentum transformation, the linear Hamiltonian flow changes by a
similarity transformation. Its frequencies are identical. Congruence
also preserves the inertia of a real quadratic form. Thus logarithmic
coordinates can enforce metric positivity, but cannot create massless
gravitons, remove physical scalar modes, or cure a negative physical
kinetic direction. This statement concerns regular coordinate changes
of the same model, not changing its interactions or taking a singular
collective/critical limit.

## 2. The existing coefficient fits a densitized metric convention

In the classical commuting limit, write d=det(q_ij)>0. A minimally
coupled canonical scalar has the normal-energy generator

```
H_m[N]=integral N [p^2/(2sqrt(d))
          +sqrt(d) q^ij partial_i phi partial_j phi/2
          +sqrt(d) U(phi)].
```

Using the densitized lapse n=N/sqrt(d), this is

```
H_m[n]=integral n [p^2/2+C^ij partial_i phi partial_j phi/2+d U(phi)],
C=d q^(-1).                                               (1)
```

The tensor in the existing energy bracket therefore has a plausible
interpretation as C, rather than directly as q^(-1). In three spatial
dimensions this identification has an explicit inverse:

```
det C=d^2,        d=sqrt(det C),        q=sqrt(det C) C^(-1). (2)
```

For positive commuting symmetric matrices, every C determines a unique
positive q. The audit checks the underlying polynomial adjugate
identities exactly. This resolves a coordinate and density ambiguity;
it does not prove that the finite spin observables, whose components
can fail to commute, already constitute a canonical metric.

There is a concrete missing matter term. If U=m_phys^2 phi^2/2, GR
requires `d m_phys^2 phi^2/2` inside the densitized generator. The
current constant coefficient `m_phi^2 phi^2/2` does not have that volume
factor. Keeping it would give `m_phys^2=m_phi^2/d` in this interpretation.
The massless gradient sector avoids this particular mismatch, but
generic matter potentials must be revised for minimal common-metric
coupling. The first energy-current bracket does not determine these
ultralocal potential coefficients.

Density weights also fix the spatial test. Put B^a_b=partial_b xi^a.
Then

```
delta q=xi.grad q+B^T q+q B,
delta C=xi.grad C+2 tr(B) C-B C-C B^T.                    (3)
```

At a point with xi=0 and B=sigma I, delta C=4sigma C,
while delta q^(-1)=-2sigma q^(-1). The finite-matrix scaling
obstruction still applies for either nonzero scaling coefficient.
The matter generator for an externally specified xi still lacks this
geometric action.

## 3. All six logarithmic metric coordinates are available classically

Let h be an arbitrary real symmetric 3x3 matrix and set

```
q=exp(h),          C=exp((tr h) I-h).                     (4)
```

This is a global chart on positive spatial metrics. It includes the
trace and five traceless components. If instead the earlier strain
notation is used, C=kappa exp(-H), equation (2) gives

```
q=sqrt(kappa) exp(H-(tr H) I/2).
```

Thus the density convention changes the trace coordinate, not the
number of available coordinates. These statements require commuting
classical coordinate components; they are not determinant identities
for arbitrary noncommuting spin-matrix entries.

Define the derivative of the matrix exponential on a symmetric A by

```
L_h(A)=integral_0^1 exp((1-s)h) A exp(s h) ds.
```

In a basis diagonalizing h, its matrix-entry coefficients are
`(exp(h_i)-exp(h_j))/(h_i-h_j)`, with the continuous value exp(h_i)
at equal eigenvalues. All are strictly positive. Consequently L_h is
self-adjoint and invertible for the Frobenius pairing. If pi is the
metric momentum and P the logarithmic momentum, set

```
P=L_h(pi),          pi=L_h^(-1)(P).
pi:delta q=P:delta h.                                    (5)
```

This is an exact classical canonical coordinate transformation. For a
spatial vector field xi, define

```
F_xi(h)=xi.grad h+L_h^(-1)(B^T exp(h)+exp(h) B),
D_g[xi]=integral P:F_xi(h).                              (6)
```

Then `{h,D_g}=F_xi(h)` and `{q,D_g}=Lie_xi q`. The total generator
also includes `D_m[xi]=integral p xi.grad phi`. On the supplied
canonical field phase space and with boundary terms controlled, this
is the ordinary spatial diffeomorphism generator in new coordinates,
and inherits its spatial constraint algebra.

The local matrix part can be checked independently. Diagonalize h,
write B=S+A with S symmetric and A antisymmetric in that basis, and
put Delta_ij=h_i-h_j. Its entries are

```
(F_B)_ij=Delta_ij coth(Delta_ij/2) S_ij+Delta_ij A_ij,     (7)
```

where the first factor is 2 at Delta_ij=0. In particular, B=sigma I
gives F_B=2sigma I and the inverse-metric dilation previously repaired.
This extends the *classical target* to shear and rotation as well.
It does not extend the finite-spin error theorem to these generators;
that requires a common six-component operator domain and new estimates.

Positive metric variables and generators preserving positivity also
appear in [Klauder's affine gravity program](https://arxiv.org/abs/1003.2617).
That is relevant precedent for the representation choice, not evidence
that our spins have its physical Hilbert space or solve quantum gravity.

## 4. The dynamical target is a constrained phase

With the notation above, Einstein's densitized normal constraint would
take the following form, with a=16pi G>0:

```
H_GR[n]=integral n {
 a[tr(pi q pi q)-(tr(pi q))^2/2]
 -d/a [R^(3)-2Lambda]
 +p^2/2+C^ij partial_i phi partial_j phi/2+d U(phi)}.      (8)
```

Here pi is obtained from P by (5). This formula is a precise matching
target. Writing it down, discretizing it, or encoding its evolution
in a history-clock Hilbert space would insert GR into the model. The
unproved emergence statement is that a specified microscopic spin
dynamics produces its constraint structure and leading coefficients
without supplying equation (8) as the starting law.

The physical reduction must be derived along with the dynamics. For
nonzero wave number, six canonical metric coordinates give twelve
phase-space dimensions. Four independent first-class constraints remove
eight dimensions after imposing the constraints and quotienting their
gauge directions, leaving two physical oscillators. The negative trace
direction of the unconstrained DeWitt quadratic form is not a physical
ghost merely because it is negative before this reduction. Conversely,
substituting that form into a stable unconstrained oscillator medium
does not perform the reduction.

Our [finite-penalty tests](BOND_TENSOR_CONSTRAINTS.md) already show why
two simple attempts fail: derivative penalties leave unwanted infrared
modes, while the tested positive curvature-square dynamics gives cubic
dispersion. A successful microscopic construction needs a mechanism
that supplies the gauge reduction and linear physical dynamics together.
Exact constraints, an emergent gauge sector, or a controlled critical
phase are possibilities to test; none has been selected here.

This difficulty has close precedent. [Gu and Wen](https://arxiv.org/abs/0907.1203)
give a controlled semiclassical helicity-two construction with cubic
dispersion; their proposed linear-dispersion model lacks reliable
control of its strongly interacting low-energy dynamics. Two tensor
polarizations alone therefore do not establish the Einstein phase.

## 5. Why Einstein gravity remains the preferred long-distance target

The [existing conditional calculation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
shows what the missing symmetry would accomplish. Given canonical
metric variables, the correct spatial action, and the normal-deformation
bracket

```
{H[N],H[M]}=D[q^ij(N partial_j M-M partial_j N)],
```

the stated local two-derivative metric ansatz fixes the trace coefficient
to -1/2 and the matched scalar propagation speed. Its canonical action
is Einstein's action. G and Lambda remain free. This is a conditional
result within that ansatz, not uniqueness among arbitrary additional
fields, higher-derivative theories, or different constraint algebras.

There is a complementary check once a physical massless relativistic
spin-two sector exists: its consistent coupling to matter must include
its own stress source. [Deser's derivation](https://arxiv.org/html/0910.2975)
performs that nonlinear completion under the stated massless spin-two,
locality, and derivative assumptions. It does not generate the initial
massless gauge sector from a gapped spin Hamiltonian.

The appropriate quantum target is Einstein gravity at leading long
distances, with controlled corrections. [The effective-field-theory
formulation](https://arxiv.org/abs/gr-qc/9405057) separates low-energy
gravitational effects from unknown short-distance physics. Finding
suppressed higher-curvature or quantum corrections would not by itself
require abandoning GR as the leading continuum theory.

The next decisive calculation is therefore a microscopic construction
with a controlled physical sector: derive the spatial generator and
linear constraints, establish precisely two positive linear tensor
modes, and test the first nonlinear normal-bracket terms with common
matter sources. Algebraic errors must vanish on states preserved by
the relevant dynamics, while microscopic interaction range remains
controlled. Fixed-input canonical estimates alone do not establish
that condition.

Failure of that construction would reject the proposed spin dynamics,
not force a replacement for Einstein gravity. Retaining a preferred
clock slicing or extra physical scalar modes would instead define a
different candidate theory whose predictions still need derivation.
The original order-to-geometry and recovered matter-theory gaps also
remain independent of this metric-sector assessment.

## 6. Verification and scope

The [audit](scripts/einstein_model_decision_audit.py) and
[report](data/einstein_model_decision_audit.json) check exact polynomial
density identities, the six-component canonical pairing, local matrix
spatial transformations including repeated eigenvalues, and unchanged
linearized spectra and kinetic inertia under coordinate changes.
There are 83 numerical metric cases, including degenerate logarithmic
eigenvalues. General field-domain and microscopic-phase arguments are
not proved by these finite checks. No Lean file is added or changed.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/einstein_model_decision_audit.py
```
