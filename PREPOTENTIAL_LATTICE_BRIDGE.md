# A local lattice action with consistent linear gravitational waves

Date: 2026-09-11

There is a consistent action-level repair of the preceding mediator
failure. Two tensor prepotentials parameterize the linear constraints;
their kinetic term is derived by pulling back the metric canonical
one-form. An explicit staggered lattice action then has positive
physical energy, exactly two tensor modes per nonzero momentum, and
the positive massless metric response. Its full lattice spectrum has
no extra zeros at the momentum-space corners.

This adapts the established prepotential formulation of linearized
gravity, rather than discovering a new gravitational theory.
[Henneaux and Teitelboim](https://arxiv.org/pdf/gr-qc/0408101)
introduced two local symmetric tensor potentials and their common
action. The contribution here is an explicit lattice realization and
an audit of the bracket problem identified in this repository.

The action is supplied as a new benchmark. It has not been derived
from the finite spins, causal-order dynamics, or convex matter measure.
Locality of an action does not itself supply a tensor-product
microscopic Hilbert space. Nonlinear Einstein gravity and the TOE
remain unproved.

## 1. Solve the linear constraints before assigning brackets

Use the Frobenius pairing of real symmetric spatial tensors.
At a nonzero real Fourier vector v, let X(v) be the cross-product
matrix, X(v) u = v cross u. Define the Fourier symbols

    R(Z) = -X Z X^T,
    S(Z) = (i/2)(X Z - Z X).                              (1)

R is a double-curl operator and S is symmetric curl. Their factors
of i give the reality condition at opposite Fourier vectors.
Introduce two symmetric prepotentials P and Phi through

    pi = R(P),       h = S(Phi).                          (2)

Then v_j pi_ij = 0 and
v_i v_j h_ij - |v|² tr h = 0. These are the supplied linear momentum
and scalar constraints of
[the tensor benchmark](BOND_TENSOR_CONSTRAINTS.md).

Each prepotential has the four-parameter redundancy

    delta Z = i(v xi^T + xi v^T) + sigma I.                (3)

For P, its gradient part leaves pi unchanged and its scalar part
produces the original scalar gauge shift of pi. For Phi, its scalar
part leaves h unchanged and its gradient part is an original spatial
gauge shift of h. Thus (3) expresses the old gauge quotient through
unconstrained potentials; it is not the nonlinear refoliation algebra.

At v != 0, (3) has rank four. One can gauge each Z to a transverse
tracefree tensor, denoted TT. On that two-dimensional tensor subspace,

    R = |v|² I,       S² = |v|² I.                        (4)

S is Hermitian, with eigenvalues +|v| and -|v|. Hence (2) covers
both physical canonical tensor pairs after the original constraints
and gauge quotient. Inverse maps exist at nonzero momentum and are
singular at v = 0.

## 2. The energy and kinetic form come from the same substitution

Write K(pi) = pi:pi - (tr pi)²/2 for the DeWitt quadratic form,
and let V_FP be the spatial Fierz--Pauli operator already defined in
the tensor benchmark. Define the prepotential operators

    Q = R* K R,
    O = R* S.                                             (5)

Here K in operator products means I - |I><I|/2.
An exact calculation gives

    Q = S* V_FP S = |v|⁴ Pi_TT,
    O* = O,       O² = |v|⁶ Pi_TT.                        (6)

The projector is used to prove these identities, not inserted into
the local action: Q and O themselves are polynomial operators of
degree four and three, respectively. They annihilate (3). Q is
positive semidefinite and has rank two at every nonzero real v.

Substitute (2) into the original canonical one-form and Hamiltonian:

    <pi, dot h> = <P, O dot Phi>,

    I = integral dt [<P, O dot Phi>
                      - (J/2)<P,Q P> - (g/2)<Phi,Q Phi>],
    J,g > 0.                                               (7)

This determines the kinetic form instead of assigning an independent
canonical bracket to the prepotentials. On the gauge quotient,

    O dot Phi = J Q P,
    O dot P   = -g Q Phi,
    ddot Phi + J g |v|² Phi = 0.                           (8)

The physical energy is positive. The opposite signs of the two
eigenvalues of O do not give a negative-energy polarization: the
canonical momentum orientation changes with that sign.

There are four physical first-order coordinates, or two canonical
pairs. This directly avoids the extra free pair and incorrect
brackets in [the independent-mediator example](CONSTRAINED_MEDIATOR_TEST.md).
It is an alternative action, not a repair obtained by changing
coordinates in the old compact-spin Hamiltonian.

## 3. Explicit finite-range lattice operators

Set lattice spacing to one for the stencil construction. Use six
component coordinates in order xx, yy, zz, xy, yz, zx, with basis
E_alpha having off-diagonal entries one. Thus
Z = sum_alpha z_alpha E_alpha; the off-diagonal Frobenius weights
must be retained. Define the component matrices

    Qc_alpha,beta(v) = <E_alpha, Q(v) E_beta>,
    Oc_alpha,beta(v) = <E_alpha, O(v) E_beta>.

For k in the full cubic Brillouin zone, set

    v_i = 2 sin(k_i/2),       w_i = exp(i k_i),

    d_xx = (1,0,0),          d_yy = (0,1,0),
    d_zz = (0,0,1),          d_xy = (1/2,1/2,0),
    d_yz = (0,1/2,1/2),      d_zx = (1/2,0,1/2),
    T_alpha,alpha = exp(i d_alpha.k),
    eta = exp[i(k_x+k_y+k_z)/2].

The two prepotentials occupy staggered positions differing by the
common half-cell shift (1/2,1/2,1/2). Set

    Qlat(w) = T* Qc(v) T,
    Olat(w) = eta T* Oc(v) T.                             (9)

Despite the half phases in this formula, both final matrices are
Laurent polynomials in the integer translations w_i. To verify
locality exactly, put t_i = exp(i k_i/2) and substitute
v_i = (t_i - t_i^(-1))/i. After applying the displayed phases, every
monomial has an even power of every t_i. Replacing t_i² by w_i
gives real rational coefficients and finite integer shifts.

[The script](scripts/prepotential_lattice_bridge_audit.py) constructs
and checks all these coefficients. The complete stencils are in
[the report](data/prepotential_lattice_bridge_audit.json):

- Qlat has 588 nonzero component/shift terms, with coefficient
  denominators at most two.
- Olat has 252 such terms, all with integer coefficients.
- Every displacement has Manhattan length at most four lattice steps.

These are uniform interaction ranges for this classical action.
They are not microscopic spin operator-norm bounds.

## 4. Gauge identities hold exactly on every periodic lattice

Let b_i = 1 - w_i^(-1). The four-column lattice gauge map is

    (G xi)_ii = 2 b_i xi_i,
    (G xi)_ij = b_i xi_j + b_j xi_i,      i != j,
    (W sigma)_ii = w_i^(-1) sigma,
    (W sigma)_ij = 0,                    i != j,
    D = [G,W].                                             (10)

The shifted Weyl column W is part of the chosen staggering.
Both prepotentials use this gauge map. Exact Laurent identities give

    Qlat D = 0,
    Olat D = Olat* D = 0,
    Qlat* = Qlat,
    Olat* = (w_x w_y w_z)^(-1) Olat.                       (11)

Star means transpose together with w_i -> w_i^(-1); coefficients
are real. Olat need not be self-adjoint because it connects the two
different staggered fields. Its adjoint must be retained in the
kinetic form.

For real lattice vectors z = (P,Phi), the actual action is

    I_lat = integral dt [P^T Olat dot Phi
                         - (J/2)P^T Qlat P
                         - (g/2)Phi^T Qlat Phi].           (12)

Its presymplectic matrix and energy Hessian are

    F = [[0,Olat],[-Olat^T,0]],
    H'' = diag(J Qlat, g Qlat),
    F dot z = H'' z.                                      (13)

The identities (11) make time-dependent gauge shifts null directions
of both structures. Consistency follows because the energy gradient
lies in the range of F. No inverse Laplacian was silently added to
the energy, and no bracket was retained from an unrelated reduction.

## 5. Full spectrum, positivity, and the homogeneous limitation

At every nonzero real lattice momentum, (9) is related to the
continuum symbols by invertible component scalings and unitary
phases. Therefore D has rank four, Qlat and Olat have rank two,
and the physical restriction of F has rank four.

Undoing these scalings and phases reduces (13) to (8). With spacing a,
use O_a = a^(-3) Olat and Q_a = a^(-4) Qlat. The two frequencies are

    omega(k) = sqrt(Jg) (2/a)
               sqrt[sum_i sin²(a k_i/2)].                 (14)

Only k = 0 is a zero within one Brillouin zone, with its identified
boundaries. In particular, its corners do not give the extra soft
branches of centered differences. At fixed physical k,

    |omega(k) - sqrt(Jg)|k||
        <= sqrt(Jg) a² |k|³/24.                           (15)

This follows from |sin x - x| <= |x|³/6 and the Euclidean norm
inequality. It is a dispersion convergence bound for this supplied
linear lattice theory.

On a periodic lattice with V sites, the nonzero-momentum physical
phase space has dimension 4(V-1), or 2(V-1) canonical pairs.
Dense real-space reductions independently verify its full spectrum.

At k = 0, both Qlat and Olat vanish. All twelve homogeneous
prepotential coordinates are null in this action, and (2) produces
neither a homogeneous h nor a homogeneous pi. The six homogeneous
metric canonical pairs of the Einstein target have not been supplied.
This matters for the trace/expansion balance established in
[the nonlinear torus benchmark](NONLINEAR_TENSOR_BACKREACTION.md).
The nonzero-mode theorem cannot be extended to full periodic
Einstein initial data by simply discarding that issue.

## 6. The reconstructed metric has a positive massless pole

On the physical TT subspace, the inverse of F determines the
prepotential brackets. Applying (2) to those brackets gives

    {h_alpha,pi_beta} = delta_alpha,beta,
    {h_alpha,h_beta} = {pi_alpha,pi_beta} = 0,              (16)

where alpha,beta label the two physical polarizations. Thus the
same construction that gives the energy also recovers the correct
metric canonical structure.

At fixed finite lattice size, excluding the homogeneous sector,
ordinary Gaussian quantization of these reduced pairs is well defined.
For a TT metric source its Euclidean response is

    <h_alpha h_beta>(omega_E,v)
       = J delta_alpha,beta / (omega_E² + Jg |v|²).        (17)

For spacing a, v_i means 2 sin(a k_i/2)/a. Inverting the full
first-order prepotential kernel with a metric source reproduces
(17) independently; it is not obtained by assigning guessed
prepotential commutators. Both residues are positive.

Equation (17) is a pole of the specified free lattice action.
It is not a pole computed in the original finite-spin model or
the convex scalar measure. No common matter cone, universal
source coupling, or nonlinear gravitational vertices have been
derived from it.

## 7. Where locality and microscopic realization still differ

In orthonormal TT variables, the inverse kinetic form scales as

    ||F_phys^(-1)|| = |v|^(-3).                            (18)

The prepotentials consequently do not have independent onsite
canonical brackets. Assigning those brackets would change (12)
and lose (14). A regular bounded coordinate change of the old
canonical tensor code does not implement this new action.

Some gauge-invariant observables nevertheless have local brackets.
On the finite real lattice define

    U = Olat Phi,       V = Olat^T P.

Using the correctly reduced bracket gives

    {U,V} = Olat,       {U,U} = {V,V} = 0.                 (19)

The gauge projectors cancel in this identity because both sides
of Olat annihilate its kernel. The right-hand side has the finite
range already listed. Nonlocal potential brackets therefore do
not by themselves demonstrate nonlocal physical propagation.
Conversely, (19) alone does not construct all local observable
algebras or a finite-dimensional onsite Hilbert space.

The primary-constraint description makes the distinction explicit.
If all twelve prepotential coordinates are first given ordinary
canonical momenta Pi_P, Pi_Phi, action (12) imposes

    Pi_P = 0,       Pi_Phi - Olat^T P = 0.                (20)

Their bracket matrix is F. Its nonzero part is second class;
it must be reduced, not imposed as commuting state-annihilation
conditions. The null part generates the redundancies of the action.
For V sites this gives 4(V-1) second-class constraints and 8V+4
first-class ones, leaving 4(V-1) physical phase dimensions.
The energy has no component along the null directions, so this
linear consistency algorithm requires no extra secondary constraints.

This is a consistent constrained classical realization with a
standard reduced Gaussian quantization. A protected realization
of (20) inside the full finite-spin Hilbert space remains absent.
It is not a new commuting-projector spin Hamiltonian.

## 8. Model decision

The previous mediator failure is repaired at the action level:
constraints, kinetic form, positive energy, and the two physical
linear waves now agree in one explicitly specified lattice theory.
The key change is the derivative-dependent kinetic form, not a
positive inverse Laplacian bolted onto independently canonical
auxiliary variables.

This gives a concrete microscopic matching target. A candidate
collective spin construction must produce the form (13), its
gauge quotient, and the energy (12) in the same low-energy sector.
Matching only its energy expectation or only a spin-two label
would not suffice. If a variational-state construction is used,
its Berry curvature and physical state identification must
reproduce the kinetic reduction as well.

The nonlinear geometric constraint algebra, homogeneous sector,
local state selection and refinement, protected finite-spin
realization, matter coupling, and Lorentzian interacting continuum
remain to be constructed. The fixed-species matter curvature
remainder and Standard Model recovery are also unresolved.
This is a stronger linear benchmark, not a completed TOE.

## 9. Verification

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/prepotential_lattice_bridge_audit.py

Exact symbolic checks verify the real local stencils and all
gauge/adjoint identities. One hundred numerical cases cover:

- 48 full-zone momentum blocks, including corners, with the
  complete reduced kinetic form and physical spectrum.
- Four independent dense periodic-lattice reductions at side
  lengths 2, 3, 4, and 5, including positivity, every physical
  frequency, null directions, and the local current bracket.
- 12 continuum error and inverse-bracket scaling cases.
- 36 metric-source kernel inversions and canonical-bracket
  reconstructions.

The analytical identities establish the stated general linear
result; numerical checks test signs, staggering and reduction.
No microscopic phase or nonlinear limit is inferred from these
finite cases. No Lean source is changed or theorem added.
