# Projected tensor states: repaired gauge rays and a shared vacuum

Date: 2026-09-11

Projection can remove the distinguishable gauge directions found in
the preceding coherent-spin construction. This is exact in a
six-qudit tensor-constraint benchmark and in the noncompact Gaussian
reduction. The finite logical Gaussian still needs a controlled
cutoff to recover the canonical Berry coefficient.

A second result changes the interpretation of the state target:
the positive linear-wave and cubic-wave Gaussian tensor Hamiltonians
have exactly the same vacuum and displaced-state geometry. Their
unequal-time responses differ. Thus recovering the desired correlated
vacuum would not, by itself, repair the compact model's wave dynamics.

The full spatial finite-spin projection, its selected thermodynamic
phase, and Einstein dynamics remain unproved. No TOE is established.

## 1. Projection changes the state geometry

Let Pi be an orthogonal projector and let |psi(z)> be normalized.
Where w(z)=<psi|Pi|psi> > 0, define

    |chi(z)> = Pi|psi(z)>/sqrt(w(z)).

Its quantum geometric tensor is

    Gamma_chi,ab
      = <partial_a psi|Pi|partial_b psi>/w
        - <partial_a psi|Pi|psi><psi|Pi|partial_b psi>/w².  (1)

Consequently projection can remove tangents that changed the
unprojected ray. It can also change the remaining Berry form and
metric, so these must be recalculated. The horizontal derivative
obeys ||partial_a chi||_horizontal <= ||partial_a psi||/sqrt(w).
A small projection probability therefore matters for approximation
errors and preparation; normalization does not remove that issue.

Projection and group averaging of coherent states have established
precedent, for example
[Hall's constrained-state construction](https://arxiv.org/pdf/quant-ph/0012050).
Its Yang--Mills theorem is not imported as a gravity theorem.
The finite-code and Gaussian statements below follow directly
from their displayed projectors and integrals.

## 2. An exact finite-qudit gauge repair

Use six odd-prime p-state qudits in component order
xx, yy, zz, xy, yz, zx. Impose the commuting checks

    X_zz, X_yz, X_zx,       Z_xx Z_yy.                    (2)

These give the constraint pattern for a nonzero tensor momentum
along z: three vector checks and one scalar check. The resulting
code has dimension p². This is a single-mode algebraic benchmark;
it is not the many-site spatial tensor-code calculation.

Write n=-(p-1)/2,...,(p-1)/2 and epsilon=sqrt(2 pi/p).
Give each qudit the normalized finite Gaussian

    psi_n(h,pi) = N(h) exp[-(epsilon n-h)²/(2 sigma²)
                            + i pi(epsilon n-h/2)].       (3)

These are genuine finite vectors, with no assumption of exact
continuous displacement covariance at the edge of the qudit.
The three X projections replace their qudits by |+>, up to scalar
overlaps. The Z projection leaves only (n_xx,n_yy)=(n,-n).
After normalization the two logical wavefunctions are Gaussians
with:

    q1,n = sqrt(2) epsilon n,
    h1 = (h_xx-h_yy)/sqrt(2),
    pi1 = (pi_xx-pi_yy)/sqrt(2),

    q2,n = epsilon n,       h2=h_xy,       pi2=pi_xy.       (4)

Both have the same width parameter sigma² as (3).

The output ray is exactly independent of h_zz,h_yz,h_zx and of
the common shift pi_xx -> pi_xx+a, pi_yy -> pi_yy+a.
These were the false gauge directions in the previous local
coherent-state test. Their projected quantum metric is now zero.

The scalar statement uses centered representatives with
n_xx+n_yy=0, not merely a nonzero multiple of p. Since their sum
has magnitude at most p-1, the modular check enforces that exact
equality here. General spatial checks have more terms and can
admit nonzero integer multiples of p. This example does not prove
continuous gauge-ray identification for all of those checks.

The projection probability is also explicit. If psi_a denotes
the six normalized input vectors, then

    w = [sum_n |psi_xx(n) psi_yy(-n)|²]
        product_(a=zz,yz,zx) |<+|psi_a>|².                 (5)

Direct vectors at p=3,5,7 verify (4), (5), every check, and the
gauge fidelities. At p=5 each qudit fits the existing four-spin
quintet. Projection is a specified nonunitary operation; these
identities do not supply a deterministic local preparation.

## 3. The finite Berry coefficient must still be controlled

For either normalized logical Gaussian, use q_n=d n and h=pi=0.
Its variance is

    V_d = sum_n q_n² exp(-q_n²/sigma²)
          / sum_n exp(-q_n²/sigma²).

Direct normalized derivatives give the Berry coefficient

    eta = 2 V_d/sigma²,       F_pi,h = eta.                (6)

Thus the gauge repair is exact at finite p, while the canonical
coefficient eta=1 is a limit. A state quotient and its canonical
normalization are separate tests.

There is a useful explicit error bound. Put

    M=(p-1)/2,       b=d²/sigma²,
    t=M sqrt(b),     a=pi²/b,       r=exp(-a).

At the centered state, 0 <= eta <= 1. If b<=1 and t>=1, then

    1-eta <= min{1,
       4a r(1+r)/(1-r)³
       + e [2t exp(-t²)+sqrt(pi) erfc(t)]}.                (7)

Otherwise the bound 1 is valid. Here e is Euler's number.
The first term controls sampling aliasing; the second controls
the finite coordinate window.

For clarity, the derivation does not rely on a fit. Poisson
summation of the infinite Gaussian lattice gives

    1-eta_infinity
      = 4a [sum_(m>=1) m² exp(-a m²)]
             / [1+2 sum_(m>=1) exp(-a m²)].

Bound exp(-a m²) by r^m and sum m²r^m. Truncating the even
distribution to |n|<=M lowers its second moment. When t>=1,
n² exp(-b n²) is decreasing in the discarded tail, so an
integral bounds that tail. For b<=1, the retained partition sum
is at least e^(-1)/sqrt(b). These estimates give (7).

For a critical vacuum width sigma²=1/(alpha |k|), alpha>0,
the controlled window is

    1/p << alpha |k| << p.                               (8)

At fixed p and k -> 0, the finite distribution becomes uniform,
and instead

    eta ~ d²(p²-1) alpha |k|/6 -> 0.                     (9)

Also eta <= 2 d² M²/sigma² at every width.
The logical mode then loses its canonical Berry coefficient.
For the simple factorized mode encoding at k_min proportional
to 1/L, taking p/L -> infinity suffices for the infrared side of
(8), with the sampling side controlled as well.

This is a limitation of these finite logical Gaussians. A soft
mode distributed collectively over many fixed-size spatial
spins can have a much larger range than one qudit. No general
claim that every local spin dimension must grow with L follows.

## 4. The complete Gaussian gauge reduction

At a fixed finite lattice, consider the real canonical mode space.
After accounting for the Frobenius component weights, let

    A = im G,       C = im B^T,
    T = (A direct-sum C)^perp.

The compatibility BG=0 makes A and C orthogonal. A contains the
spatial coordinate gauge directions, C the scalar momentum gauge
directions, and T the physical coordinates, including whatever
homogeneous sector is retained separately.

The noncompact constraints require q_C=0 and p_A=0.
On suitable test wavefunctions a rigging map is

    (R_phys psi)(x_T) = integral_A psi(x_T+y) dy.           (10)

Restriction to x_C=0 is implicit. This integrates the coordinate
gauge orbit and imposes the scalar coordinate constraint. It is
not a bounded orthogonal projector on the original L² space:
the noncompact gauge volume and continuous constraint spectrum
require a separate physical inner product.

Take a Gaussian with positive precision W, commuting with these
orthogonal projectors, and constrained coherent labels
h_C=0, pi_A=0. The integral is elementary. After normalization,

    Psi_phys(x_T) proportional to
      exp[-(x_T-h_T)^T W_T (x_T-h_T)/2
          + i pi_T.(x_T-h_T/2)].                         (11)

It is independent of h_A and pi_C. Its Berry form is canonical
on T, and its quantum metric is

    g_phys = (1/2)[dh_T^T W_T dh_T
                         + dpi_T^T W_T^(-1) dpi_T].       (12)

Substituting h=S Phi and pi=R P restores the prepotential Berry
form while removing all the distinguishable gauge tangents.
For W_T=alpha |k| I, its nonzero-mode metric is

    g_phys = (|k|³/2)
       [alpha^(-1) dP_TT² + alpha dPhi_TT²].              (13)

This is the correlated-state geometry targeted by the preceding
global encoding. It is derived here by Gaussian reduction, not
by assigning a new independent bracket to the prepotentials.

## 5. Projection alone does not generate the critical width

In (11), projection retains the physical precision W_T. A
spatial product Gaussian with constant width does not acquire
the precision alpha |k| merely by removing gauge variables.

The conclusion has a more general Gaussian bound. If the input
precision satisfies

    0 < w_- I <= W <= w_+ I

uniformly in size, its physical precision after integrating A
and setting C=0 is the Schur complement

    W_eff = W_TT - W_TA W_AA^(-1) W_AT,
    w_- I <= W_eff <= w_+ I.                             (14)

The lower bound follows by minimizing the positive quadratic
form over A at fixed x_T. The upper bound uses the trial y_A=0.
Hence such a uniformly bounded-precision Gaussian cannot become
critical with W_eff proportional to |k| -> 0 by this projection.

The result is confined to the stated Gaussian reduction. It
does not exclude a non-Gaussian projected spin state developing
long-range correlations or a different critical phase.

## 6. The local cubic parent already has the target Gaussian vacuum

There is a constructive source for the critical width within the
continuous tensor benchmark. On each nonzero physical tensor mode,
compare

    H1(k) = (J/2) pi² + (g/2)|k|² h²,
    H3(k) = (J/2)|k|² pi² + (g/2)|k|⁴ h²,
    J,g>0.                                                (15)

On the actual lattice, replace k_i by v_i=2 sin(k_i/2), with
spacing restored when needed. H3 is the positive Gaussian
expansion of the local curl/double-curl tensor construction
in [the compact dynamics note](COMPACT_TENSOR_DYNAMICS.md).
That note did not establish the phase of its fixed-p spin model.

For H=(A pi²+B h²)/2, the normalized ground wavefunction has
precision sqrt(B/A). Both Hamiltonians in (15) therefore have

    Psi_0(h) proportional to exp[-alpha |k| h²/2],
    alpha = sqrt(g/J).                                   (16)

Their Gaussian vacuum vectors are exactly identical mode by
mode at finite volume after excluding the homogeneous sector.
All equal-time Gaussian correlations and the geometry of the
same displaced-state family agree. This includes the physical
metric (13).

The local continuous cubic parent consequently supplies the
desired Gaussian state geometry. It does not supply linear
Einstein dynamics, and this Gaussian statement is not a proof
that the compact five-state model selects that vacuum.

## 7. Unequal-time response distinguishes the two theories

The complete Euclidean metric responses are

    G1(omega_E,k) = J/(omega_E² + Jg |k|²),
    G3(omega_E,k) = J |k|²/(omega_E² + Jg |k|^6).           (17)

Both have the same equal-time integral,

    integral d omega_E/(2 pi) G_a
        = (1/2)sqrt(J/g)/|k|.

But their frequencies are sqrt(Jg)|k| and sqrt(Jg)|k|³.
Their static responses also differ:

    G1(0,k)=1/(g |k|²),       G3(0,k)=1/(g |k|⁴).          (18)

At positive Euclidean time their correlations decay with those
different frequencies. A common regular change of time cannot
remove a relative factor |k|² for all modes.

Thus a successful state-preparation or equal-time entanglement
test is insufficient to establish the Einstein response. The
Hamiltonian's action on those physical states must also be
derived. The previously demonstrated compact-code derivative
obstruction remains relevant even if its vacuum geometry is
eventually proved.

## 8. Updated construction target

Projection now has a verified role: it can remove the false
gauge-ray directions. The finite compact benchmark shows this
without an infinite-dimensional Hilbert space, while its Berry
normalization exposes the required cutoff control. Gaussian
reduction gives the complete target state quotient but retains
the input physical width.

The next microscopic construction must select a suitable
projected or correlated state in the full spatial spin system
and derive its unequal-time evolution. Finding the critical
vacuum alone will not distinguish H1 from H3. A proposed repair
must change the actual physical dynamics or constraint structure
consistently, rather than infer that change from matching the
vacuum.

The existing compact parent leaves an extensive code space
degenerate; projection into it does not select a unique vacuum.
The probability (5) and nonunitary normalization also do not
provide an efficient preparation theorem. No controlled
thermodynamic finite-spin phase follows from the six-qudit
examples or the noncompact Gaussian integral.

Nonlinear refoliation, homogeneous Einstein data, universal
matter coupling, local refinement and physical locality,
fixed-species matter curvature control, Standard Model
dynamics, and the original TOE objective remain open.

## 9. Verification

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/projected_tensor_vacuum_audit.py

[The script](scripts/projected_tensor_vacuum_audit.py) records
[the report](data/projected_tensor_vacuum_audit.json).
Sixty-four numerical cases check six full six-qudit projections,
36 finite logical Berry coefficients and analytical bounds,
16 Gaussian physical reductions and precision bounds, and
six comparisons of the complete linear/cubic spectral responses.
Additional small-|k| checks verify the fixed-prime saturation
formula. The projection and Gaussian conclusions are established
by the explicit analytical formulas above.

No finite-spin phase or nonlinear gravitational limit is
extrapolated from these cases. No Lean source is changed or
theorem added.
