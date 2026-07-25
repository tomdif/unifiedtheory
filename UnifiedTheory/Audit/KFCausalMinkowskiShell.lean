/-
  Audit/KFCausalMinkowskiShell.lean   (Volume sector → flat-Minkowski witness / interface)

  A flat-spacetime WITNESS for the geometric interface the causal-set application still
  depends on -- and an honest account of what the attempt closes and what it exposes.

  The remaining tier is not one published citation but a GEOMETRIC INTERFACE that must
  supply: (1) the Alexandrov interval-volume function `V(τ)`; (2) the pushforward of
  spacetime volume onto constant-`v` shells; (3) the shell's fractional-power expansion
  `w(v) = A v^{α-1} + …` with `α = 2/d`; (4) uniform remainder control; (5) the
  boundedness/support condition `laplace_tail_bound` needs; and, for a d'Alembertian on
  `φ`, (6) the Taylor expansion of `φ`, the ANGULAR integration, and the curvature terms
  that actually produce the `□φ`, `Rφ`, and residue coefficients.

  WHAT CLOSES unconditionally in flat Minkowski (this file):
    * `intervalVolume_homogeneous` / `intervalVolume_eq` : the interval volume is
      homogeneous of degree `d`, `V(τ) = C_d τ^d`, from scale-covariance (`I(τ) = τ • I₁`)
      and Haar scaling -- point (1)'s structural core, proved, dimension-general.

  WHAT THE ATTEMPT EXPOSES (as anticipated -- the failure is informative):
    * The shell density `w(v)` and the coefficients `A`, `□φ`, `Rφ`, residue are NOT
      supplied by the volume formula.  They come from the coarea PUSHFORWARD and the
      ANGULAR integration of the Taylor-expanded field (the angular integral of
      `ξ^μ ξ^ν` is what yields `η^{μν} ∂_μ∂_ν φ = □φ`).  So the abstract `v^{α-1}` shell
      hypothesis BUNDLES the angular/Taylor reduction; it is not a naive volume
      pushforward.  `ShellInterface` below makes exactly these assumed fields explicit,
      so the conditionality is legible rather than hidden.

  Honest status: tier 3 is a proved analytic theorem; the flat-Minkowski instantiation
  closes the volume-form piece but shows the shell/angular data is a genuine further
  interface, not a corollary of the diamond volume.  The next gate remains: supply that
  interface (angular integration in a fixed dimension), then bounded curvature.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory Module Pointwise

namespace UnifiedTheory.Audit.KFCausalMinkowskiShell

/-- **Interval-volume homogeneity (flat-Minkowski witness, point 1).**  For a causal
interval that is scale-covariant, `I(τ) = τ • I₁`, the `d`-dimensional Lebesgue volume
scales as `τ^d`: `volume (τ • I₁) = τ^d · volume I₁`.  This is the structural core of the
Alexandrov formula `V(τ) = C_d τ^d`, proved unconditionally in every dimension from Haar
scaling. -/
theorem intervalVolume_homogeneous {d : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (I : Set (EuclideanSpace ℝ (Fin d))) :
    volume (τ • I) = ENNReal.ofReal (τ ^ d) * volume I := by
  rw [Measure.addHaar_smul_of_nonneg (μ := volume) hτ I, finrank_euclideanSpace_fin]

/-- **Interval volume equals `C_d τ^d`.**  With `C_d := vol(I₁)` (the unit-interval
volume), the interval volume is exactly `V(τ) = C_d · τ^d` (real-valued form). -/
theorem intervalVolume_eq {d : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (I₁ : Set (EuclideanSpace ℝ (Fin d))) :
    (volume (τ • I₁)).toReal = (volume I₁).toReal * τ ^ d := by
  rw [intervalVolume_homogeneous τ hτ I₁, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **The geometric interface, made explicit.**  Every field here is a thing the flat-
Minkowski (or bounded-curvature) instantiation must SUPPLY; none is a corollary of the
interval volume alone.  Bundling the shell density and the angular-derived operator
coefficients into named fields is exactly the point: it shows what the abstract
`v^{α-1}` hypothesis was hiding.

  * `Cvol`, `hVol`     — the Alexandrov volume law `V(τ) = Cvol · τ^d` (point 1, CLOSED
                          above by `intervalVolume_eq`; recorded here as the supplied datum).
  * `α`, `hα`          — the shell exponent, CLAIMED `α = 2/d` (point 3; verifying it is
                          the angular computation, NOT settled by `intervalVolume_eq`).
  * `A`, `Crem`, `η`   — the local shell expansion `w(v) = A v^{α-1} + O(v^{α+η-1})` and
                          its uniform remainder (points 2–4), the input to
                          `laplace_remainder_bound`.
  * `Mtail`            — the far-region bound (point 5), the input to `laplace_tail_bound`.
  * `boxCoeff`, `RCoeff`, `residCoeff` — the coefficients of `□φ`, `Rφ`, and the `ℓ²`
                          residue (point 6).  These come from the ANGULAR integration of
                          the Taylor-expanded field, NOT from `V`; listing them as
                          separate data is the honest content of the witness. -/
structure ShellInterface (d : ℕ) where
  Cvol : ℝ
  V : ℝ → ℝ
  hVol : ∀ τ : ℝ, 0 ≤ τ → V τ = Cvol * τ ^ d
  α : ℝ
  hα : α = 2 / (d : ℝ)
  A : ℝ
  Crem : ℝ
  η : ℝ
  Mtail : ℝ
  boxCoeff : ℝ
  RCoeff : ℝ
  residCoeff : ℝ

/-- The interface's own volume law is consistent with the proved flat-space fact: the
`intervalVolume_eq` witness populates `V` and `Cvol` for a concrete unit interval `I₁`. -/
theorem shellInterface_volume_witness {d : ℕ} (I₁ : Set (EuclideanSpace ℝ (Fin d))) (τ : ℝ) (hτ : 0 ≤ τ) :
    (volume (τ • I₁)).toReal = (volume I₁).toReal * τ ^ d :=
  intervalVolume_eq τ hτ I₁

#print axioms intervalVolume_homogeneous
#print axioms intervalVolume_eq
#print axioms shellInterface_volume_witness

end UnifiedTheory.Audit.KFCausalMinkowskiShell
