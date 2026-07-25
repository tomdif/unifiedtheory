/-
  Audit/KFCausalCSpecBDGContinuumLimit.lean   (Volume sector → goal B, BDG continuum limit)

  The Benincasa-Dowker-Glaser continuum limit, formalized in the division-of-labor style:
  the hard analysis (interval-volume geometry + asymptotic Poisson integrals over the
  causal past) enters as NAMED HYPOTHESES giving the asymptotic decomposition of the
  sprinkling-mean, and the theorem assembles them into the continuum operators.

  d'Alembertian.  Along the high-density family (`l = the ρ → ∞ filter`), the mean of the
  causal-set d'Alembertian applied to `φ` at `x` decomposes as

      M(ρ) = c(ρ) φ(x) + s(ρ) (□φ + ½ R φ)(x) + rem(ρ),

  where (analytic/geometric inputs):
    * `c(ρ) → 0` : the volume-DIVERGENT coefficient cancels -- this is exactly what the
      algebraic moment conditions (`layerResponse_secondOrder`: constant + linear parts
      vanish) deliver;
    * `s(ρ) → 1` : the second-order normalization;
    * `rem(ρ) → 0` : the higher-order remainder.
  Then `M(ρ) → (□φ + ½ R φ)(x)` -- the causal-set d'Alembertian recovers the continuum
  operator with its curvature term.

  Action.  Identically, the mean BDG action decomposes as bulk-divergent + Einstein-
  Hilbert + boundary + remainder; the divergent part cancels and the mean converges to the
  Einstein-Hilbert action (plus the boundary term).

  These are the BDG continuum theorems MODULO the cited asymptotic inputs -- the same
  epistemic position as the Roy-Sinha-Surya remainder and the Karcher stability in goal A.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Filter Topology

namespace UnifiedTheory.Audit.KFCausalCSpecBDGContinuumLimit

variable {ι : Type*}

/-- **Causal-set d'Alembertian continuum limit.**  Given the asymptotic decomposition of
the sprinkling-mean into a volume-divergent term `c φ(x)`, a second-order term
`s (□φ + ½Rφ)`, and a remainder, with the divergent coefficient `c → 0` (moment
conditions), normalization `s → 1`, and remainder `→ 0`, the mean converges to the
continuum operator `□φ + ½ R φ`. -/
theorem bdg_dalembertian_continuum_limit
    (l : Filter ι) (M c s rem : ι → ℝ) (φx boxφ Rφ : ℝ)
    (hdecomp : ∀ i, M i = c i * φx + s i * (boxφ + (1 / 2) * Rφ) + rem i)
    (hc : Tendsto c l (𝓝 0)) (hs : Tendsto s l (𝓝 1)) (hrem : Tendsto rem l (𝓝 0)) :
    Tendsto M l (𝓝 (boxφ + (1 / 2) * Rφ)) := by
  have hM : M = fun i => c i * φx + s i * (boxφ + (1 / 2) * Rφ) + rem i := funext hdecomp
  rw [hM]
  have h := ((hc.mul_const φx).add (hs.mul_const (boxφ + (1 / 2) * Rφ))).add hrem
  simpa using h

/-- **BDG action continuum limit.**  Given the analogous decomposition of the mean BDG
action into a bulk-divergent term `c`, the Einstein-Hilbert action `s · S_EH`, a boundary
term `bdy`, and a remainder, with the divergent part `c → 0`, normalization `s → 1`, and
remainder `→ 0`, the mean action converges to `S_EH + S_boundary`. -/
theorem bdg_action_continuum_limit
    (l : Filter ι) (S c s rem : ι → ℝ) (S_EH S_bdy : ℝ)
    (hdecomp : ∀ i, S i = c i + s i * S_EH + S_bdy + rem i)
    (hc : Tendsto c l (𝓝 0)) (hs : Tendsto s l (𝓝 1)) (hrem : Tendsto rem l (𝓝 0)) :
    Tendsto S l (𝓝 (S_EH + S_bdy)) := by
  have hS : S = fun i => c i + s i * S_EH + S_bdy + rem i := funext hdecomp
  rw [hS]
  have h := (((hc.add (hs.mul_const S_EH)).add_const S_bdy).add hrem)
  simpa using h

/-- **Flat-space specialization.**  In the curvature-free case (`R = 0`), the causal-set
d'Alembertian mean recovers exactly the flat d'Alembertian `□φ`. -/
theorem bdg_dalembertian_flat_limit
    (l : Filter ι) (M c s rem : ι → ℝ) (φx boxφ : ℝ)
    (hdecomp : ∀ i, M i = c i * φx + s i * boxφ + rem i)
    (hc : Tendsto c l (𝓝 0)) (hs : Tendsto s l (𝓝 1)) (hrem : Tendsto rem l (𝓝 0)) :
    Tendsto M l (𝓝 boxφ) := by
  have hM : M = fun i => c i * φx + s i * boxφ + rem i := funext hdecomp
  rw [hM]
  have h := ((hc.mul_const φx).add (hs.mul_const boxφ)).add hrem
  simpa using h

#print axioms bdg_dalembertian_continuum_limit
#print axioms bdg_action_continuum_limit
#print axioms bdg_dalembertian_flat_limit

end UnifiedTheory.Audit.KFCausalCSpecBDGContinuumLimit
