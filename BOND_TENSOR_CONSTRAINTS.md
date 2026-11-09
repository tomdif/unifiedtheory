# A bond tensor and the constraint required for two gravitational polarizations

Date: 2026-09-10

The collective-spin suggestion can be made into a precise **candidate
effective theory**, with a sharp test of what its microscopic dynamics
must supply. Bond variables can encode a full spatial symmetric tensor.
If canonical tensor variables and four specified first-class constraints
are supplied, requiring spatial gauge invariance off the constraint
surface and preserving the constraints fixes the stated minimal quadratic
Hamiltonian to the linearized-gravity form, with two linear wave modes.
These are conditional results. The canonical variables and constraints
have not been derived from the repository's spin or causal-order law.

Two tempting substitutes fail in this test. Positive quadratic dynamics
with finite constraint penalties retain six gapless modes. Using the
linearized-gravity quadratic form with those penalties instead makes
the noncompact fluctuation Hamiltonian unstable at sufficiently small
wave number. The remaining task is a stable microscopic realization of
the constrained physical sector, not finding an internal spin-2 label.

This note adds an explicit diagnostic extension. It does not change the
Hamiltonian in [the entangled acoustic calculation](ENTANGLED_ACOUSTIC_BOUNDS.md),
and does not claim a TOE or microscopic emergence of Einstein gravity.

## 1. Encoding a spatial tensor in local bond coefficients

For bonds with displacement r, the smooth scalar-field energy contains
`w_r (r.grad phi)^2/2`. Its stiffness tensor is

```
D = sum_r w_r r r^T.                              (1)
```

Here r is a physical spatial direction, so D transforms as a spatial
tensor. This differs from assigning an internal spin index the meaning
of a spatial index. Bond correlations, for example expectations of XY
exchange operators on several directions, could provide coefficients
w_r; this identification is a model-building ansatz at this stage.

Three axis directions span only diagonal tensors. Adding copies of the
original straight switches rotated among those axes does not supply the
full six-component stiffness at the affine-strain level. The six
directions `e_x,e_y,e_z,e_x+e_y,e_y+e_z,e_z+e_x` do span Sym(3).
For a desired infinitesimal tensor h, set

```
delta w_xy=h_xy, delta w_yz=h_yz, delta w_zx=h_zx,
delta w_x=h_xx-h_xy-h_zx,
delta w_y=h_yy-h_xy-h_yz,
delta w_z=h_zz-h_yz-h_zx.                          (2)
```

Substitution in (1) gives delta D=h exactly. A positive isotropic
reference can instead use nine directions: three axes and both
diagonals `e_i+e_j,e_i-e_j` in each coordinate plane. Assign positive
weights w_a to axes and w_d to diagonals. Then

```
D_0=(w_a+4w_d) I,
delta w_i=h_ii,
delta w_(ij,+)=h_ij/2, delta w_(ij,-)=-h_ij/2.     (3)
```

All weights stay positive if `|h_ii|<w_a` and `|h_ij|<2w_d`.
This is a local stiffness encoding with finite-length bonds. It does
not establish that six collective bond observables obey independent
canonical commutators, or that they have the dynamics below.

## 2. The proposed tensor constraints and their physical dimension

As a diagnostic, introduce real symmetric canonical fields h_ij,p_ij
in three spatial dimensions, with the Frobenius canonical pairing.
For one nonzero Fourier wavevector k write q=|k| and define

```
C_j=(p k)_j,                        j=1,2,3,
C_0=k^T h k-q^2 tr h = B:h,
B=k k^T-q^2 I.                                    (4)
```

Fourier factors i can be retained in complex amplitudes or absorbed
into the sine/cosine partners. The audit uses real coefficient blocks;
the reality condition pairs k with -k. The zero mode is excluded: the
constraint ranks and physical mode count there are different.

These four constraints commute. In particular B k=0, so the Poisson
bracket of C_0 with each C_j vanishes. At k!=0 they are independent.
Their Hamiltonian flows generate the gauge directions

```
h -> h + k xi^T + xi k^T,
p -> p + a B,                                     (5)
```

with inessential generator sign/normalization absorbed in xi,a.
The constraints cut twelve phase-space dimensions to eight; quotienting
their four gauge directions leaves four dimensions, or two canonical
oscillators. This subtraction is justified by the explicit rank and
isotropic-gauge calculations, not simply by counting tensor indices.

For k along z, C_j set p_xz,p_yz,p_zz to zero; C_0 sets h_xx+h_yy=0.
The vector gauge removes h_xz,h_yz,h_zz, and the scalar gauge removes
p_xx+p_yy. Representatives are transverse and traceless (TT). Rotations
about k act by twice the angle on their two components. These are the
two helicity-two polarizations in this supplied continuum tensor theory.

## 3. Gauge conditions fix the minimal quadratic coefficients

Assume a translation-invariant, rotationally invariant, parity-even,
time-reversal-even quadratic Hamiltonian with no p-h cross term, no
mass term, zero spatial derivatives on p, and two on h. After normalizing
the p:p and q^2 h:h coefficients, write

```
H = (J/2)[p:p + alpha (tr p)^2] + (g/2)V(h),
V(h)=q^2 h:h + a q^2(tr h)^2 + b |h k|^2
                                      + d (tr h)(k^T h k),
J>0, g>0.                                        (6)
```

The restrictions in this ansatz are hypotheses, not consequences of
the microscopic model or a classification of all possible gravity.

Requiring invariance under the spatial gauge shift (5), for every h,k,xi,
fixes `a=-1, b=-2, d=2`. Requiring that time evolution preserve C_0 on
C_j=0 fixes `alpha=-1/2`. To see the latter, Hamilton's equation is
`dot h=J[p+alpha (tr p)I]`, hence

```
dot C_0 = J[k^T p k-(1+2alpha)q^2 tr p].          (7)
```

On p k=0 the transverse trace tr p is arbitrary before gauge fixing;
therefore 1+2alpha must vanish. The resulting forms are

```
K(p)=p:p-(tr p)^2/2,
V(h)=q^2 h:h-q^2(tr h)^2-2|h k|^2
                                      +2(tr h)(k^T h k). (8)
```

They obey `dot C_j=0` and `dot C_0=J k.C`. Thus the constraint surface is
preserved. K is invariant under the scalar gauge on this surface; its
variation is proportional to k^T p k. Off that surface it is not a
positive kinetic energy on all six canonical fields.

The off-surface spatial invariance requirement is stronger than merely
preserving the constraint surface. For example, adding a multiple of
`(tr h) C_0` changes the quadratic coefficients but vanishes on the
physical surface and preserves it. The coefficient uniqueness above
uses the stated stronger requirement; it does not exclude such
constraint-proportional extensions of the same physical dynamics.

On the physical TT representatives,

```
H_TT=(J/2)|p_TT|^2+(g q^2/2)|h_TT|^2,
omega_TT=sqrt(Jg) q.                              (9)
```

The two modes have positive energy and linear dispersion. Equation
(8), with the constraints, is the familiar linearized-gravity canonical
structure, here recovered by solving the specified coefficient test.
This is an explicit conditional effective construction, not a new
derivation of that known theory from microscopic spins. Its speed
sqrt(Jg) is still a free parameter; matching the scalar-wave speed is
an additional condition, not a prediction.

## 4. Finite penalties do not realize this quotient

Start with a bounded-below, noncompact six-field oscillator model,

```
H_soft=|p|^2/2+c^2 q^2 |h|^2/2
                     +(U/2)|p k|^2+(W/2)(B:h)^2,
c>0, U,W>=0 finite.                              (10)
```

Choose k=(0,0,q) and a Frobenius-orthonormal tensor basis. Its six
frequency squares are exactly

```
c^2 q^2                       (two TT modes),
c^2 q^2 (1+U q^2/2)           (two mixed longitudinal modes),
c^2 q^2 (1+U q^2)             (one longitudinal mode),
c^2 q^2+2W q^4                (one transverse trace mode). (11)
```

All six satisfy omega/q -> c as q->0 at fixed U,W. A very large penalty
can change a finite momentum window, but it does not leave only two
gapless modes uniformly as volume grows. This is an exact counterexample
to implementing (4) by these finite quadratic penalties. It is not a
no-go theorem for compact spins, discrete constraint spectra, other
interactions, or other phases.

Applying the same penalties to the already-fixed form (8) is worse on
the unbounded canonical space. Take p=t I and h=0:

```
H_FP+penalty=(t^2/2)[-3J/2+U q^2].               (12)
```

For any fixed finite U, sufficiently small nonzero q makes this negative
and unbounded as |t| grows. Independently, for k along z choose
`h=diag(t,t,0), p=0`. Then

```
H_FP+penalty=t^2[-g q^2+2W q^4].                 (13)
```

This is negative for sufficiently small q at fixed W. The exact
constraint quotient removes these directions; a finite derivative
penalty does not. A finite-spin cutoff bounds the original operator,
so this calculation diagnoses instability of its proposed noncompact
quadratic expansion, not literal unbounded energy of a finite qubit
Hamiltonian.

## 5. A positive curvature-square alternative has the wrong dispersion

There is a useful comparison with a manifestly nonnegative local
quadratic form. Let R(k)v=k cross v and define

```
H_square=(J/2)||R(k)[p-(tr p)I/2]||_F^2
                         +(g/2)||R(k) h R(k)^T||_F^2. (14)
```

The scalar gauge shifts the square bracket by a k k^T, killed by R(k).
The vector gauge is killed by the two R factors in the potential.
Thus the quadratic form commutes with all four constraints, even before
restricting to their common zero surface. On the same TT quotient it is

```
H_square,TT=(J q^2/2)|p_TT|^2+(g q^4/2)|h_TT|^2,
omega_square=sqrt(Jg) q^3.                       (15)
```

Positive local squares do provide a tensor benchmark, but this one
does not share a linear relativistic cone with the scalar sector.
No claim of classifying all positive tensor Hamiltonians is made.

The comparison with (8) explains why preserving a constrained physical
energy can differ from demanding a sum of gauge-invariant positive
squares on the whole unconstrained space. The microscopic theory must
supply the appropriate physical subspace or an independently justified
low-energy mechanism for it.

## 6. Coupling to the scalar waves: a necessary extension, not universality

The original exact transverse factor had no switch backreaction.
A spatial tensor perturbation of scalar stiffness gives instead

```
delta H_phi=-(epsilon/2) integral h_ij
                         partial_i phi partial_j phi. (16)
```

For a traceless shear `h=diag(0,1,-1)` and a scalar gradient in the y
direction this is nonzero, even though that scalar profile was invisible
to every original x-directed switch. Equations (1)–(3) give a local
bond-coefficient realization of this vertex at the stiffness level.
This demonstrates a way to remove the old decoupling by changing the
model. It is a static/off-shell vertex test, not a claimed real on-shell
one-particle decay or a proof of a coupled tensor phase.

The spatial vertex alone is insufficient for gravitational coupling.
In coordinates using a **supplied common wave speed** and a canonically
normalized free scalar, the symmetric stress tensor is

```
T^(mu nu)=partial^mu phi partial^nu phi
                       -eta^(mu nu)(partial phi)^2/2,
partial_mu T^(mu nu)=(Box phi) partial^nu phi.     (17)
```

The full linear vertex `(epsilon/2)integral h_mu nu T^(mu nu)` varies
under `delta h_mu nu=partial_mu xi_nu+partial_nu xi_mu` by
`-epsilon integral xi_nu partial_mu T^(mu nu)`, up to a boundary term.
It is gauge compatible on the free scalar equation. The h_00 and h_0i
multiplier components supply the energy and momentum sources of the
constraints. They are absent from a model containing only (16).

There is another useful limit to the result: separate free scalar
species have separately conserved stresses. Therefore
`epsilon_1 T_1+epsilon_2 T_2` is conserved even when epsilon_1!=epsilon_2.
The first-order free-field identity (17) **does not prove universal
coupling**. Nor does it ensure conservation after the interaction changes
the scalar equation. A consistent interacting gauge symmetry and its
self-coupling must be established at the next orders.

## 7. What this contributes to the repository

The new bond map supplies full spatial tensor kinematics. The coefficient
test identifies exactly which assumed constraints recover two linear
helicity-two modes in the minimal quadratic ansatz. Explicit spectra and
negative-energy directions rule out two simple penalty implementations.
The scalar vertex shows how the old zero-backreaction obstruction could
be removed, while the Ward test keeps that separate from universality.

The remaining microscopic task is now concrete: derive canonical
collective bond variables and a stable physical sector realizing (4),
with the constrained kinetic structure (8), from an actual local quantum
Hamiltonian. Its continuum speed, constraint sources, nonlinear closure,
and universal coupling must then be controlled. None follows merely from
the four-spin spin-2 representation found in the previous audit.

This analysis is consistent with established tensor-gauge research.
[Gu and Wen](https://arxiv.org/abs/0907.1203) distinguish constrained
linear-dispersion tensor dynamics from a positive curvature-square
construction and explain why compactification/discretization matters
for proposed microscopic realizations. Their linear-dispersion qubit
phase is not established by the reliable calculation for their other
model. [Deser's consistency argument](https://arxiv.org/abs/gr-qc/0411023)
addresses nonlinear completion once the appropriate linear spin-2 gauge
theory and coupling are supplied. Here the independently checked
coefficient equations, finite-momentum matrices, and bond encoding serve
as diagnostics; they do not fill those microscopic or nonlinear gaps.

## 8. Audit scope

The Python audit uses exact symbolic bond maps, coefficient identities,
constraint brackets, axis spectra, and stress-conservation polynomials.
It separately checks generic momentum directions numerically: four
independent commuting constraints, the TT projector, symplectic quotient,
constraint-preserving evolution, and both tensor dispersions. It tests
the finite-penalty spectra and infrared instabilities without interpreting
a large finite penalty as an exact projection.

The fifteen supporting Lean results verify scalar coefficient, constraint,
quadratic-energy, and dispersion algebra. They do not formalize the
microscopic limit, a constrained quantum Hilbert space, or nonlinear
Einstein dynamics. Previous research artifacts remain unchanged.

The [audit script](scripts/bond_tensor_audit.py) writes its detailed
[report](data/bond_tensor_audit.json), including sixty generic momentum
checks and the exact symbolic coefficient and penalty spectra. The
[Lean module](UnifiedTheory/Audit/KFCausalBondTensor.lean) reports only
the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Reproduce from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/bond_tensor_audit.py
lake env lean UnifiedTheory/Audit/KFCausalBondTensor.lean
```
