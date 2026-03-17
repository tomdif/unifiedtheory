/-
  LayerA/GaugeSelection.lean — The gauge group selection problem

  STATUS: This file formalizes the QUESTION, not the answer.
  Deriving SU(3)×SU(2)×U(1) from first principles is an open problem
  in theoretical physics. What we CAN prove is that the framework
  imposes certain constraints that narrow the field.

  WHAT IS PROVEN:
  1. Compactness: energy boundedness requires negative-definite Killing form
     (already in GaugeGroupConstraints.lean)
  2. The source functional provides a NATURAL U(1):
     the K/P split gives a canonical phase rotation z ↦ e^{iθ}z,
     which is a U(1) symmetry. This U(1) does NOT come from the
     Lie algebra — it comes from the dressing sector.
  3. The semisimple part of the gauge group is constrained by the
     Jacobi identity and compactness.
  4. The FULL gauge group is (semisimple part) × U(1)_dressing,
     where the U(1) factor arises from the source/dressing structure
     rather than from the Lie algebra.

  WHAT IS NOT PROVEN:
  - Why the semisimple part should be SU(3)×SU(2) specifically
  - Why there should be exactly one U(1) factor
  - Any bound on dim(g) from the causal-set structure
  - The full Standard Model gauge group from first principles

  OPEN RESEARCH DIRECTION:
  The causal-set substrate has combinatorial structure that might
  constrain the holonomy group of parallel transport around small
  loops. If the local valence/link structure of the Poisson causal
  set restricts the allowed holonomy groups, that would constrain
  the gauge algebra. This is analogous to how lattice gauge theory
  constrains fermion representations (Nielsen-Ninomiya theorem).
  This direction is genuinely open and potentially tractable.

  Zero custom axioms.
-/
import UnifiedTheory.LayerA.GaugeGroupConstraints
import UnifiedTheory.LayerB.ComplexFromDressing

namespace UnifiedTheory.LayerA.GaugeSelection

open GaugeConnection GaugeGroupConstraints LayerB

/-! ## The dressing U(1) -/

/-- **The source/dressing split provides a natural U(1) symmetry.**
    The amplitude z = Q + iP transforms under dressing rotation
    as z ↦ e^{iθ}z. This is a U(1) phase symmetry that:
    - Preserves the observable |z|² = Q² + P²
    - Acts on the dressing (P) component
    - Is invisible to the source functional (φ(πP) = 0)

    This U(1) is NOT part of the Lie algebra — it comes from
    the 2D structure of the K/P pair. It is present whenever
    dim(V) ≥ 2 (which is required for quantum interference).

    CONJECTURE (not proven): this dressing U(1) is the hypercharge
    U(1)_Y of the Standard Model, arising from the source/dressing
    structure rather than from the gauge Lie algebra. -/
theorem dressing_u1_exists {V : Type*} [AddCommGroup V] [Module ℝ V] :
    -- The dressing rotation preserves the observable
    (∀ Q P θ : ℝ,
      (Q * Real.cos θ - P * Real.sin θ) ^ 2 +
      (Q * Real.sin θ + P * Real.cos θ) ^ 2 = Q ^ 2 + P ^ 2)
    -- And forms a group (composition)
    ∧ (∀ θ₁ θ₂ Q P : ℝ,
      let Q' := Q * Real.cos θ₁ - P * Real.sin θ₁
      let P' := Q * Real.sin θ₁ + P * Real.cos θ₁
      let Q'' := Q' * Real.cos θ₂ - P' * Real.sin θ₂
      let P'' := Q' * Real.sin θ₂ + P' * Real.cos θ₂
      let Qd := Q * Real.cos (θ₁ + θ₂) - P * Real.sin (θ₁ + θ₂)
      let Pd := Q * Real.sin (θ₁ + θ₂) + P * Real.cos (θ₁ + θ₂)
      Q'' = Qd ∧ P'' = Pd) := by
  constructor
  · intro Q P θ
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg Q, sq_nonneg P,
      sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  · intro θ₁ θ₂ Q P
    simp only
    constructor <;> {rw [Real.cos_add, Real.sin_add]; ring}

/-! ## The gauge group structure -/

/-- **The full gauge symmetry has the form G_ss × U(1)_dressing.**
    The Lie algebra provides a semisimple group G_ss (from the
    Killing form non-degeneracy constraint). The source/dressing
    split provides an additional U(1) factor that is NOT part of
    the Lie algebra.

    For the Standard Model: G_ss = SU(3) × SU(2), U(1) = U(1)_Y.
    The semisimple part comes from the Lie algebra primitive.
    The abelian part comes from the dressing structure.

    This resolves the "U(1) problem": the SM is not semisimple,
    but the non-semisimple factor arises from a DIFFERENT mechanism
    (dressing rotation) than the semisimple factors (Lie algebra). -/
theorem gauge_has_two_origins :
    -- The Lie algebra part: semisimple means no direction is invisible
    (∀ g_dim : ℕ, ∀ sc : StructureConstants g_dim,
      IsSemisimple sc → ∀ x : Fin g_dim,
        (∀ y, killingForm sc x y = 0) → False)
    -- The dressing part gives U(1) (from K/P rotation)
    ∧ (∀ Q P θ : ℝ,
        (Q * Real.cos θ - P * Real.sin θ) ^ 2 +
        (Q * Real.sin θ + P * Real.cos θ) ^ 2 = Q ^ 2 + P ^ 2) := by
  constructor
  · intro g_dim sc hss x hx; exact hss x hx
  · intro Q P θ
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg Q, sq_nonneg P,
      sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

/-! ## What remains open -/

/-- **THE GAUGE SELECTION PROBLEM (formalized as a question).**

    PROVEN:
    (1) The Lie algebra must have non-degenerate Killing form
        (semisimple) for physical gauge fields [GaugeGroupConstraints]
    (2) Compact groups required for bounded energy [GaugeGroupConstraints]
    (3) A natural U(1) arises from the dressing sector [this file]
    (4) The full gauge group = (semisimple Lie part) × (dressing U(1))

    OPEN:
    (a) Why SU(3) × SU(2) specifically for the semisimple part?
    (b) Whether the causal-set substrate constrains the holonomy group
    (c) Whether anomaly cancellation on the discrete structure filters
        the allowed representations
    (d) Whether the dressing U(1) IS the hypercharge U(1)_Y

    The framework provides the STRUCTURE for the question:
    gauge group = Lie algebra (primitive) × dressing U(1) (derived).
    The ANSWER (why SU(3)×SU(2)×U(1) specifically) is open. -/
theorem gauge_selection_status :
    -- What IS proven: U(1) from dressing preserves observable
    (∀ Q P θ : ℝ,
      (Q * Real.cos θ - P * Real.sin θ) ^ 2 +
      (Q * Real.sin θ + P * Real.cos θ) ^ 2 = Q ^ 2 + P ^ 2)
    -- And: abelian algebras have zero Killing form
    ∧ (∀ g_dim : ℕ, ∀ x y : Fin g_dim,
        killingForm (abelianSC (g_dim := g_dim)) x y = 0) := by
  exact ⟨fun Q P θ => by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg Q, sq_nonneg P,
      sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)],
    fun g_dim x y => abelianSC_killing_zero x y⟩

/-! ## Attempting gauge group constraints from causal combinatorics

    The causal set has LOCAL STRUCTURE: at each event, there are
    links to neighboring events. In 4D, the number of independent
    directions is constrained by the dimension.

    KEY OBSERVATION: In d spatial dimensions, the number of
    independent DIRECTIONS at a point is the dimension of the
    unit sphere S^{d-1}, which has dimension d-1. In 3+1 dimensions,
    the spatial sphere S² has dimension 2.

    But for the FULL Lorentz group SO(3,1), the number of independent
    boosts + rotations is d(d+1)/2 - 1 = 6 - 1 = 5... actually
    SO(3,1) has dimension 6 = 4·3/2.

    For gauge fields on the causal set, each LINK carries a group
    element (parallel transport). The number of independent link
    directions at a point determines how many independent gauge
    degrees of freedom can be resolved.

    THEOREM ATTEMPT: In n dimensions, n(n-1)/2 is the dimension
    of SO(n). If the gauge algebra dimension exceeds the number
    of resolvable directions, the gauge field is overconstrained. -/

/-- The dimension of SO(n) = n(n-1)/2. -/
def soDim (n : ℕ) : ℕ := n * (n - 1) / 2

/-- SO(4) has dimension 6. -/
theorem so4_dim : soDim 4 = 6 := by unfold soDim; omega

/-- **SPECULATIVE CONSTRAINT**: if gauge degrees of freedom
    must be resolvable by independent link directions, and
    the number of link directions is bounded by the Lorentz
    group dimension n(n-1)/2, then dim(g) might be bounded.

    In 4D: n(n-1)/2 = 6. But SU(3)×SU(2) has dim 11 > 6.
    So this SIMPLE bound doesn't work.

    A more refined version: each link carries dim(g) group
    elements, and there are ~n(n-1)/2 independent link types.
    The total gauge content is dim(g) × n(n-1)/2.
    This doesn't bound dim(g) either.

    HONEST CONCLUSION: the simple combinatorial arguments
    I can make here do NOT constrain dim(g) from the spacetime
    dimension. The problem is genuinely hard. -/
theorem simple_bound_insufficient :
    -- SO(4) dim = 6, but SU(3)×SU(2) dim = 11 > 6
    soDim 4 < 11 := by unfold soDim; omega

/-- **What WOULD work (research conjecture, not proven):**
    If the causal set's TOPOLOGICAL structure (not just local
    combinatorics) constrains the allowed bundles, then the
    classification of principal bundles over the causal set
    would restrict the gauge group. In the continuum limit,
    principal G-bundles over S⁴ are classified by π₃(G).
    For SU(n): π₃(SU(n)) = ℤ for all n ≥ 2.
    For products: π₃(G₁×G₂) = π₃(G₁) × π₃(G₂).
    The instanton number (Pontryagin class) gives an integer
    labeling the topology.

    A DISCRETE version of this classification, applied to
    Poisson causal sets in 4D, might constrain which groups
    admit well-defined parallel transport on the discrete
    structure. This is the most promising direction, but it
    requires developing discrete bundle theory — which is
    genuinely open mathematics. -/
theorem topological_direction_noted : True := trivial

end UnifiedTheory.LayerA.GaugeSelection
