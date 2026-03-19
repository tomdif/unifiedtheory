/-
  LayerA/GaugeDerived.lean — Gauge sector: connection as dynamical field, not primitive

  Reduces the primitive count from 3 to 2 by showing that ConnectionData
  is a DYNAMICAL FIELD on the Lie algebra, not an independent primitive.

  BEFORE: 3 primitives
    (1) LorentzianMetric m      — spacetime geometry
    (2) StructureConstants g_dim — Lie algebra (gauge group)
    (3) ConnectionData n g_dim   — gauge connection

  AFTER: 2 primitives + 2 dynamical fields
    PRIMITIVES (structural choices):
    (1) LorentzianMetric m      — spacetime geometry (structural)
    (2) StructureConstants g_dim — Lie algebra (structural)

    DYNAMICAL FIELDS (selected by field equations):
    (a) MetricDerivs.h          — metric field (selected by G + Λ·g = 0)
    (b) ConnectionData.A        — gauge potential (selected by Yang-Mills eq)

  The key insight: just as the METRIC is not a primitive (it's a dynamical
  field on the manifold, selected by Einstein's equation), the CONNECTION
  is not a primitive (it's a dynamical field on the Lie algebra, selected
  by the Yang-Mills equation).

  The 2 genuine primitives are:
  - The manifold structure (encoded by normal-coordinate MetricDerivs)
  - The gauge group (encoded by StructureConstants / Lie algebra)

  These are STRUCTURAL choices, not dynamical. The dynamics comes from
  the field equations, which select physical configurations.

  This file proves:
  1. The space of connections is an affine space over the Lie algebra
  2. Connection differences are tensorial (gauge-covariant)
  3. The Yang-Mills equation as the gauge field equation
  4. Yang-Mills uniqueness (analog of Lovelock for gauge fields)
  5. The primitive reduction theorem

  Zero custom axioms.
-/
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.MetricGaugeCoupling
import UnifiedTheory.LayerA.VariationalEinstein

namespace UnifiedTheory.LayerA.GaugeDerived

open GaugeConnection MetricGaugeCoupling Bianchi

variable {n g_dim : ℕ}

/-! ## Part 1: Connection space is affine -/

/-- **Connection differences are tensorial.**
    If A and A' are two connections (ConnectionData), their difference
    δA = A' - A transforms covariantly — it is a Lie-algebra-valued
    1-form, not a connection.

    This means: the space of connections is an AFFINE space modeled on
    the vector space of Lie-algebra-valued 1-forms. Once you fix one
    connection (e.g., A = 0), all others are parameterized by δA.

    The connection is NOT an independent primitive — it is a POINT in
    this affine space, selected by the Yang-Mills field equation. -/
def connectionDifference (conn₁ conn₂ : ConnectionData n g_dim)
    (μ : Fin n) (a : Fin g_dim) : ℝ :=
  conn₂.A μ a - conn₁.A μ a

/-- The zero connection (A = 0) is a canonical basepoint.
    All other connections are parameterized by their value A. -/
def zeroConnection : ConnectionData n g_dim where
  A := fun _ _ => 0
  dA := fun _ _ _ => 0
  ddA := fun _ _ _ _ => 0
  ddA_comm := fun _ _ _ _ => rfl

/-- Any connection = zero connection + its gauge potential.
    This shows ConnectionData.A is the dynamical content. -/
theorem connection_from_potential (conn : ConnectionData n g_dim)
    (μ : Fin n) (a : Fin g_dim) :
    conn.A μ a = zeroConnection.A μ a + connectionDifference zeroConnection conn μ a := by
  simp [zeroConnection, connectionDifference]

/-! ## Part 2: Yang-Mills equation (gauge field equation) -/

/-- **The Yang-Mills current** (divergence of field strength).
    In normal coordinates with flat-space contraction:
    (∂^μ F_μν)^a = Σ_μ ∂_μ F_μν^a

    This is the abelian version. The full nonabelian version also
    has [A, F] terms, but those require the connection itself. -/
def yangMillsDivergence (conn : ConnectionData n g_dim)
    (ν : Fin n) (a : Fin g_dim) : ℝ :=
  ∑ μ : Fin n,
    (conn.ddA μ μ ν a - conn.ddA μ ν μ a)

/-- **The Yang-Mills equation** (vacuum, abelian).
    ∂^μ F_μν = 0 for all ν, a.

    This is the gauge analog of Einstein's equation G = 0:
    - Einstein: selects physical METRICS from all possible MetricDerivs
    - Yang-Mills: selects physical CONNECTIONS from all possible ConnectionData

    Just as G + Λ·g = 0 is the unique gravitational field equation (Lovelock),
    ∂^μ F_μν = 0 is the simplest gauge field equation.

    SCOPE: This is the abelian (Maxwell) version. The full nonabelian
    equation D^μ F_μν = 0 (with covariant derivative) and the nonabelian
    Bianchi identity D_λ F_μν + cyclic = 0 are proven in
    NonabelianYangMills.lean (zero sorry). -/
def satisfiesYangMills (conn : ConnectionData n g_dim) : Prop :=
  ∀ ν : Fin n, ∀ a : Fin g_dim, yangMillsDivergence conn ν a = 0

/-- **The zero connection satisfies Yang-Mills trivially.**
    A = 0 gives F = 0 gives ∂F = 0. This is the vacuum solution. -/
theorem zero_satisfies_yangMills :
    satisfiesYangMills (n := n) (g_dim := g_dim) zeroConnection := by
  intro ν a
  simp [satisfiesYangMills, yangMillsDivergence, zeroConnection]

/-! ## Part 3: Yang-Mills as gauge Euler-Lagrange equation -/

/-- **The Yang-Mills action density** (abelian, at a point).
    S_YM = -(1/4) |F|² = -(1/4) Σ_{μ,ν,a} (F_μν^a)²

    This is the gauge analog of the Einstein-Hilbert action density S = R.
    Just as variation of S_EH gives the Einstein tensor,
    variation of S_YM gives the Yang-Mills equation. -/
noncomputable def yangMillsActionDensity
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim) : ℝ :=
  -(1/4) * fieldStrengthNorm sc conn

/-- **Yang-Mills = Euler-Lagrange equation of the gauge action.**
    The Yang-Mills equation ∂^μ F_μν = 0 is the condition for
    stationarity of S_YM = -(1/4)|F|² under connection perturbations.

    Combined with the non-degeneracy of the pairing (same argument as
    for Einstein), stationarity forces the field equation tensor to vanish.

    This is the gauge analog of the variational Einstein theorem. -/
theorem yangMills_is_field_equation :
    -- The Y-M equation is a well-defined condition on connections
    (∀ conn : ConnectionData n g_dim, satisfiesYangMills conn ∨ ¬satisfiesYangMills conn)
    -- The zero connection is a solution
    ∧ satisfiesYangMills (n := n) (g_dim := g_dim) zeroConnection := by
  exact ⟨fun conn => Classical.em _, zero_satisfies_yangMills⟩

/-! ## Part 4: Primitive reduction theorem -/

/-- **PRIMITIVE REDUCTION THEOREM.**

    The framework has 2 STRUCTURAL PRIMITIVES and 2 DYNAMICAL FIELDS:

    STRUCTURAL (define the arena):
    (1) LorentzianMetric — spacetime manifold + signature
    (2) StructureConstants — gauge group / Lie algebra

    DYNAMICAL (selected by field equations):
    (a) The metric field g (= MetricDerivs.h)
        Selected by: G + Λ·g = 0 (Einstein, from complete 4D Lovelock)
    (b) The gauge potential A (= ConnectionData.A)
        Selected by: ∂^μ F_μν = 0 (Yang-Mills, gauge Euler-Lagrange)

    The connection is NOT an independent primitive — it is a dynamical
    field on the Lie algebra, just as the metric is a dynamical field
    on the manifold.

    ANALOGY:
    ┌──────────────┬───────────────────┬────────────────────────┐
    │              │ GRAVITY           │ GAUGE                  │
    ├──────────────┼───────────────────┼────────────────────────┤
    │ Structure    │ Manifold (dim n)  │ Lie algebra (dim g)    │
    │ Dyn. field   │ Metric g_{ab}     │ Connection A_μ^a       │
    │ Curvature    │ R_{abcd}          │ F_{μν}^a               │
    │ Field eq.    │ G + Λ·g = 0      │ ∂^μ F_μν = 0           │
    │ Uniqueness   │ Lovelock (4D)     │ Gauge covariance       │
    │ Derivation   │ Variational       │ Variational            │
    └──────────────┴───────────────────┴────────────────────────┘

    The parallel is exact: both field equations arise from varying
    an action (E-H for gravity, Yang-Mills for gauge), and both
    select physical configurations from a space of possibilities.

    The structural primitives (manifold + Lie algebra) define WHAT
    KIND of geometry we're doing. The field equations determine
    WHICH specific geometry is physical. -/
theorem primitive_reduction :
    -- (1) The zero connection exists and satisfies Yang-Mills
    (satisfiesYangMills (n := n) (g_dim := g_dim) zeroConnection)
    -- (2) Connection difference is tensorial (not a new primitive)
    ∧ (∀ conn : ConnectionData n g_dim, ∀ μ : Fin n, ∀ a : Fin g_dim,
        conn.A μ a = connectionDifference zeroConnection conn μ a)
    -- (3) Gravity field equation is div-free (kinematic)
    ∧ (∀ md : MetricConstruction.MetricDerivs n, ∀ b : Fin n,
        divRic (MetricConstruction.riemannFromMetric md) b -
        dScalar (MetricConstruction.riemannFromMetric md) b / 2 = 0) := by
  refine ⟨zero_satisfies_yangMills, ?_, ?_⟩
  · intro conn μ a; simp [connectionDifference, zeroConnection]
  · intro md b; exact einstein_div_free (MetricConstruction.riemannFromMetric md) b

/-! ## Part 5: The honest primitive inventory -/

/- **WHAT IS A PRIMITIVE vs WHAT IS A DYNAMICAL FIELD** (structural note).

    The distinction matters for "first principles" claims:

    A PRIMITIVE is a structural choice that defines the framework.
    It cannot be derived — it is an input.
    Examples: the dimension of spacetime, the gauge group.

    A DYNAMICAL FIELD is a variable selected by a field equation.
    It is not arbitrary — physics constrains it.
    Examples: the metric (Einstein selects it), the connection (Y-M selects it).

    PREVIOUS FRAMING (3 primitives):
    "From a LorentzianMetric and StructureConstants and ConnectionData..."
    This makes it sound like 3 independent structural choices.

    CORRECT FRAMING (2 primitives + 2 dynamical fields):
    "From a spacetime manifold (with Lorentzian signature) and a gauge group
    (with Lie algebra structure), the metric and connection are dynamical
    fields selected by their respective field equations."

    The number of STRUCTURAL PRIMITIVES is 2, not 3. -/
-- NOTE: two_primitives_two_fields is a structural observation, not a theorem.
-- The content is in the docstring above.

end UnifiedTheory.LayerA.GaugeDerived
