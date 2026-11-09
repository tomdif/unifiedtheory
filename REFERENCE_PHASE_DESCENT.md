# Phase consistency between redundant reference descriptions

Date: 2026-09-10

**Proved at the finite weak-field scope:** two flat-reference/fluctuation
pairs representing the same real link potential have an explicit determinant
transition phase. A canonical mean reference and a curvature-integral phase
adjustment make their determinant sections identical. The adjusted connection
descends through this redundancy, retains the projector curvature, and
preserves the previously constructed gauge Ward equation.

The unadjusted phases need not agree. The construction below removes their
measured nonzero discrepancy; it does not assume that discrepancy is zero.
Seventeen Lean results support the finite splitting and phase algebra and a
component form of the integration argument. The full Kato/differential
argument is analytic and independently checked, not fully Lean-formalized.

Uniform locality **after this new phase adjustment** is not established here.
Nor does this prove compatibility with every compact logarithm lift, nonzero
flux sector, or the required lattice symmetries. The complete physical
fermion measure and TOE therefore remain open.

## 1. The precise redundancy and a controlled canonical representative

Write a real potential as

\[
W=b+A,\qquad b_\mu=\theta_\mu/L_\mu.
\]

Here `b` is spatially constant. For any spatially constant `r`, the pairs
`(b,A)` and `(b+r,A-r)` represent exactly the same `W`, not merely
gauge-equivalent fields. This section concerns this equality of real
potentials. Integer changes of link logarithms are an additional issue.

Let `mean A_mu` be the spatial average in direction `mu`. Define

\[
\bar b=b+\operatorname{mean}A=\operatorname{mean}W,
\qquad \bar A=A-\operatorname{mean}A=W-\operatorname{mean}W.
\tag{1}
\]

Then `mean Abar=0`, `bbar+Abar=W`, and both outputs depend only on `W`.
These claims are proved for the actual finite mean in the Lean module.
Also `|mean A_mu|<=epsilon` and `||Abar||infinity<=2epsilon` when
`||A||infinity<=epsilon`.

To keep the entire canonical interpolation in the proved Wilson-gap domain,
take `epsilon<1/48` for the supplied charges `|q|<=6`. All interpolated
fluctuations then have norm at most `2epsilon`, giving the conservative gap
`1-48epsilon>0`. The existing value `epsilon=.018` satisfies this condition.
The flat reference itself remains unrestricted. Gauge orbits of bounded
representatives remain gapped by unitary covariance.

## 2. Construct the transition phase from the projector

Let `s_i` be the normalized determinant section obtained from the paired
flat orientation, radial Kato transport based at `b_i`, and the existing
scalar correction `exp(-i C_i)`, where `C_i=C_theta_i(A_i)`.
Use the connection convention `beta=i Tr(V†dV)`. The previous construction
gives

\[
\beta=\beta_{\rm rad}+dC,\qquad
\beta_{\rm rad}(\delta b,\delta A)
=\int_0^1\mathcal F_{b+tA}(A,\delta b+t\delta A)\,dt,
\tag{2}
\]

with `F_W(eta,zeta)=i Tr P[P'_eta,P'_zeta]`, summed over species with their
multiplicities. Only the gapped Wilson projector is differentiated; the
physical Dirac operator is not inverted. Local paired frames suffice:
their determinant orientation is independent of the pivot vector.

For two descriptions with `b_i+A_i=b_j+A_j=W`, put `r=b_j-b_i` and
interpolate within the fibre over `W`:

\[
b_s=b_i+s r,\quad A_s=A_i-s r,\quad
W_{s,t}=b_s+t A_s.
\]

The top edge `t=1` is the fixed field `W`; the bottom edge lies in the flat
family. Define the explicit curvature integral

\[
I_{ij}=\int_0^1\!ds\int_0^1\!dt\,
 (1-t)\mathcal F_{W_{s,t}}(A_s,r).
\tag{3}
\]

This is the radial connection integrated along the fibre: its tangent has
`delta b=r`, `delta A=-r`, so the second argument of (2) is `(1-t)r`.
The integral is smooth and real on the stated gapped domain.

The determinant transition is

\[
\boxed{\tau_{ij}=\exp[-i(I_{ij}+C_j-C_i)]},\qquad s_j=s_i\tau_{ij}.
\tag{4}
\]

**Proof of (4).** Along the fibre, the endpoint projector is constant.
Any two orthonormal frames of its range differ by a unitary matrix `T(s)`.
Jacobi's determinant identity gives
`d log det T = Tr(T†dT) = -i beta`. Integrating from `i` to `j` gives the
exponential of minus the connection integral. Equation (2) contributes
`I_ij`, and the exact scalar differential contributes `C_j-C_i`.
At the flat bottom edge the determinant section is horizontal by its paired
orientation. Thus no additional reference phase is omitted. This proves
the formula without selecting a branch of `arg det T`.

## 3. Why the phase composes and the connection descends

Let `pi(b,A)=b+A`. The projector curvature is closed, and the flat reference
has zero determinant curvature. The radial homotopy formula therefore gives

\[
d\beta=\pi^*\mathcal F.
\tag{5}
\]

If a tangent vector changes only the description, then `d pi` sends it to
zero. Hence (5) vanishes whenever one of its arguments is such a fibre
direction. In particular, the restriction of `beta` to each fibre is closed.
The allowed lifted reference vectors form a convex set (the fluctuation
bound is a convex constraint). Integrals within it are path independent.
Thus, for any three admissible descriptions of the same potential,

\[
I_{ij}+I_{jk}=I_{ik},\qquad
\tau_{ij}\tau_{jk}=\tau_{ik}.
\tag{6}
\]

The first equality is an equality of real integrals, not only of their
exponentials. The scalar `C` terms telescope. The matrix identity
`(V_i†V_j)(V_j†V_k)=V_i†V_k` supplies an independent check of the resulting
determinant composition law; it is not a substitute for constructing (3).

Choose the canonical description (1), denoted `0`, and define

\[
f_i=I_{0i}+C_i-C_0,\qquad
s_i^{\rm desc}=e^{i f_i}s_i.
\tag{7}
\]

Using (4) and (6),

\[
s_j^{\rm desc}
=s_i\exp[-i(I_{ij}+C_j-C_i)]e^{i f_j}
=s_i e^{i f_i}=s_i^{\rm desc}.
\]

This proves equality of the determinant sections. Multiplying the
determinant section by a unit complex number preserves its norm. If an
ordinary frame realization is wanted, multiply one column by that phase;
no rank-dependent root or global smooth full frame is required.

The connection becomes `beta_desc=beta-df`. For completeness, the full
descent statement also follows directly by two-parameter differentiation.
Let `R_s(z)` interpolate from the canonical representative `R_0(z)` to
`R_1(z)=z`, keeping `pi(R_s(z))=pi(z)`. For any smooth test curve `z(u)`,
the commuting `s,u` derivatives and (5) imply

\[
\partial_s\{\beta(\partial_uR_s)\}
-\partial_u\{\beta(\partial_sR_s)\}
=d\beta(\partial_sR_s,\partial_uR_s)=0.
\]

Integrating in `s` gives

\[
\boxed{\beta-df=R_0^*\beta=\pi^*\beta_{\rm can}}.
\tag{8}
\]

Thus the corrected connection depends on the physical real potential and
its variation. It annihilates description-only tangents and has the same
projector curvature. Smoothness of the finite constructions and the uniform
gap justify these differentiations and integrations. The Lean FTC lemma
checks the endpoint integration step with its derivative hypothesis explicit;
the actual matrix/differential-geometric assembly above remains analytic.

## 4. The adjustment preserves the gauge Ward equation

Let `B_grad omega` be a real periodic gauge gradient. Its spatial average
vanishes by a permutation of the finite site sum, so the canonical reference
in (1) is unchanged by this gauge transformation. The reference difference
`r` between two descriptions is unchanged as well.

In the triangle (3), `A_s` becomes `A_s+B_grad omega` and `W_s,t` becomes
`W_s,t+t B_grad omega`. Gauge covariance leaves the curvature kernels
unchanged; their first argument acquires the extra gauge tangent. The
previous exact curvature/Ward identity is

\[
\mathcal F(B_{\rm grad}\omega,\eta)
=\langle\omega,\delta_\eta\rho\rangle.
\]

Since `partial_s rho(W_s,t)=(1-t) delta_r rho(W_s,t)`, it follows that

\[
I'_{ij}-I_{ij}=\langle\omega,\bar\rho_j-\bar\rho_i\rangle,
\qquad \bar\rho_i=\int_0^1\rho(b_i+tA_i)\,dt.
\]

Meanwhile, the existing scalar correction satisfies
`C_i'-C_i=-<omega,rhobar_i>`. These terms cancel in `f_i`, giving
`f_i'=f_i`. Hence `df_i(B_grad omega)=0`, and

\[
\beta_{\rm desc}(B_{\rm grad}\omega)
=\beta(B_{\rm grad}\omega)=-\langle\omega,\rho(W)\rangle.
\tag{9}
\]

This establishes Ward preservation for the new adjustment, including finite
real gauge transformations along the gapped gauge orbit.

## 5. What this proof does and does not settle

Equations (3)–(9) resolve phase and connection consistency under the stated
flat-reference redundancy. The construction uses the actual overlap
projector and the previously built scalar correction. It does not merely
postulate transition phases satisfying a cocycle.

The mean in (1) depends on all links, and the new curvature integral is a
global scalar functional. Smoothness and exact descent do not prove uniform
spatial locality of its differentiated contribution to the current. The
earlier seam estimate for the Ward primitive alone is insufficient to assert
that result for `df`: the curvature integral and canonical retraction must
also be controlled. That locality obligation is left open rather than
inferred from a finite Ward solve or small numerical values.

The proof is on real potential lifts in the controlled zero-flux domain.
All compact logarithm identifications, the intended lattice symmetries,
nonzero flux sectors, non-Abelian dynamics, and the physical continuum/GR
bridges remain additional work. No physical TOE is established by this
phase theorem.

## 6. Independent checks and reproducibility

The audit uses three explicit descriptions of a single seeded field on
`2^4`, with all five supplied hypercharges and multiplicities. It computes
(3) using projector derivatives, and compares (4) with a separate calculation
of the determinant overlaps of radially transported frames. The scalar
corrections are computed independently by the full finite descent.

The raw triangle fluxes include `-1.29873e-7`; the discrepancy is nonzero.
The additive flux cocycle residual is about `1.51e-19`, and the 8-to-12-node
triangle quadrature change is about `2.55e-20`. For that largest raw flux,
32, 64, and 128 Kato steps give errors `2.42e-11`, `6.05e-12`, and `1.51e-12`.
The completed scalar adjustments relative to the canonical reference are
`1.53247e-7` and `-5.01131e-7` radians. A corrected but not yet descended
transition differs by about `6.544e-7` radians. After applying (7), the
maximum transition error at 128 steps is `1.52e-12`. The triangle gauge-change
identity has residual `7.33e-14`; the canonical adjustment's finite gauge
change is `8.22e-15`. These checks resolve the nonzero original discrepancy.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/reference_phase_descent_audit.py
lake env lean UnifiedTheory/Audit/KFCausalReferencePhaseDescent.lean
lake build
```

Lean commands must run sequentially with other Lean jobs in this repository.
The report is `data/reference_phase_descent_audit.json`, with source hashes.
Numerical residuals are diagnostics, not all-volume proof certificates.

The distinction between determinant transitions and full frame transitions
is standard in lattice chiral-measure reconstruction; see section 8 of
[Lüscher's Abelian construction](https://arxiv.org/abs/hep-lat/9811032).
The contribution here is the explicit reference-comparison integral,
canonical phase adjustment, and their checks for this repository's current.
