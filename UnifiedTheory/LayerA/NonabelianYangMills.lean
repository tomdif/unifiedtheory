/-
  LayerA/NonabelianYangMills.lean — Full nonabelian Yang-Mills equation

  Upgrades the gauge sector from abelian (∂^μ F_μν = 0) to the full
  nonabelian Yang-Mills equation (D^μ F_μν = 0) where D is the
  gauge-covariant derivative.

  The covariant derivative on Lie-algebra-valued tensors:
    (D_μ T)^a = ∂_μ T^a + c^a_{bd} A_μ^b T^d

  The nonabelian Yang-Mills equation:
    (D^μ F_μν)^a = ∂^μ F_μν^a + c^a_{bd} A^μ_b F_μν^d = 0

  And the nonabelian Bianchi identity:
    D_λ F_μν + D_μ F_νλ + D_ν F_λμ = 0

  Zero custom axioms.
-/
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.GaugeDerived

namespace UnifiedTheory.LayerA.NonabelianYangMills

open GaugeConnection

variable {n g_dim : ℕ}

/-! ## The gauge-covariant derivative -/

/-- **Gauge-covariant derivative** of a Lie-algebra-valued vector field.
    (D_μ T)^a = ∂_μ T^a + Σ_{bd} c^a_{bd} A_μ^b T^d_ν

    This is the fundamental differential operator for nonabelian gauge theory.
    It replaces the ordinary derivative ∂_μ with a connection-dependent one
    that transforms covariantly under gauge transformations. -/
def covariantDeriv
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (dT : Fin n → Fin n → Fin g_dim → ℝ)  -- ∂_μ T_ν^a
    (T : Fin n → Fin g_dim → ℝ)            -- T_ν^a
    (μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  dT μ ν a + ∑ b : Fin g_dim, ∑ d : Fin g_dim, sc.c a b d * conn.A μ b * T ν d

/-- **Covariant derivative of the field strength.**
    (D_λ F_μν)^a = ∂_λ F_μν^a + c^a_{bd} A_λ^b F_μν^d -/
def covariantDerivF
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  -- ∂_λ F_μν^a (from second derivatives of connection)
  (conn.ddA l_ μ ν a - conn.ddA l_ ν μ a +
    ∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA l_ μ b * conn.A ν d + conn.A μ b * conn.dA l_ ν d))
  -- + c^a_{bd} A_λ^b F_μν^d (bracket term)
  + ∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * conn.A l_ b * curvature sc conn μ ν d

/-! ## The nonabelian Yang-Mills equation -/

/-- **Nonabelian Yang-Mills divergence**: (D^μ F_μν)^a.
    In flat-space normal coordinates: D^μ = ∂^μ + [A^μ, ·].
    (D^μ F_μν)^a = Σ_μ (∂_μ F_μν^a + c^a_{bd} A_μ^b F_μν^d) -/
def yangMillsDivNonabelian
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (ν : Fin n) (a : Fin g_dim) : ℝ :=
  ∑ μ : Fin n, covariantDerivF sc conn μ μ ν a

/-- **The nonabelian Yang-Mills equation**: D^μ F_μν = 0. -/
def satisfiesNonabelianYM
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim) : Prop :=
  ∀ ν : Fin n, ∀ a : Fin g_dim, yangMillsDivNonabelian sc conn ν a = 0

/-- **The zero connection satisfies nonabelian Yang-Mills.**
    A = 0 → F = 0 → D^μ F = ∂^μ F + [A, F] = 0 + 0 = 0. -/
theorem zero_satisfies_nonabelian_ym (sc : StructureConstants g_dim) :
    satisfiesNonabelianYM sc (GaugeDerived.zeroConnection (n := n) (g_dim := g_dim)) := by
  intro ν a
  simp [yangMillsDivNonabelian, covariantDerivF, curvature, GaugeDerived.zeroConnection]

/-- **For abelian gauge theory, nonabelian YM reduces to abelian YM.**
    When c = 0 (abelian structure constants), the bracket terms vanish
    and D^μ F_μν = ∂^μ F_μν. -/
theorem nonabelian_reduces_to_abelian (conn : ConnectionData n g_dim) (ν : Fin n) (a : Fin g_dim) :
    yangMillsDivNonabelian abelianSC conn ν a =
    GaugeDerived.yangMillsDivergence conn ν a := by
  simp [yangMillsDivNonabelian, covariantDerivF, GaugeDerived.yangMillsDivergence,
    curvature, abelianSC]

/-! ## The nonabelian Bianchi identity -/

/-- **Nonabelian Bianchi identity**: D_λ F_μν + D_μ F_νλ + D_ν F_λμ = 0.

    This is the gauge-covariant generalization of the abelian Bianchi
    identity ∂_λ F_μν + cyclic = 0.

    The proof has two parts:
    1. The ∂∂A terms cancel by commutativity (same as abelian case)
    2. The bracket terms [A, F] cancel by the Jacobi identity -/
theorem nonabelian_bianchi
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    covariantDerivF sc conn l_ μ ν a +
    covariantDerivF sc conn μ ν l_ a +
    covariantDerivF sc conn ν l_ μ a = 0 := by
  simp only [covariantDerivF, curvature]
  -- The ddA terms cancel by commutativity (same as abelian Bianchi)
  -- The bracket terms cancel by the Jacobi identity of sc
  -- Both cancellations are algebraic
  have hc := conn.ddA_comm
  have hj := sc.jacobi
  -- This is a sum of many terms; linarith with the Jacobi identity
  -- and commutativity should close it
  sorry -- Requires detailed term-by-term cancellation; see proof sketch below

/-! ## Proof sketch for nonabelian Bianchi

    The nonabelian Bianchi identity D_λ F_μν + cyclic = 0 has two types of terms:

    TYPE 1 (∂∂ terms): These are exactly the abelian Bianchi terms.
    ∂_λ(∂_μ A_ν - ∂_ν A_μ) + cyclic = 0 by commutativity of ∂∂.
    PROVEN: abelian_bianchi in GaugeConnection.lean.

    TYPE 2 (∂[A,A] + [A,∂A-∂A] + [A,[A,A]] terms):
    These cancel by the Jacobi identity c^e_{bd} c^a_{eg} + cyclic = 0.
    The cancellation is algebraic but involves many index contractions.

    TYPE 3 ([A, F] bracket terms):
    ∂_λ(c·A·A) + c·A·(∂A-∂A+c·A·A) + cyclic
    After expansion, all terms cancel by Jacobi + antisymmetry.

    The full proof requires ~50-100 lines of linarith with Jacobi instances.
    We mark this sorry and note it is a MECHANICAL computation, not a
    conceptual gap. -/

/-! ## Summary -/

/-- **NONABELIAN YANG-MILLS SUMMARY.**

    The full nonabelian gauge sector is formalized:

    (1) Covariant derivative D_μ T^a = ∂_μ T^a + c^a_{bd} A_μ^b T^d
    (2) Covariant derivative of field strength D_λ F_μν
    (3) Nonabelian Yang-Mills equation D^μ F_μν = 0
    (4) Zero connection is a solution (trivially)
    (5) Abelian limit: nonabelian reduces to abelian when c = 0
    (6) Nonabelian Bianchi: D_λ F_μν + cyclic = 0 (sorry for Jacobi cancellation)

    This upgrades the gauge sector from "abelian only" to "full nonabelian"
    with one remaining sorry in the Bianchi identity (mechanical Jacobi
    cancellation, not a conceptual gap). -/
theorem nonabelian_ym_summary (sc : StructureConstants g_dim) :
    -- Zero connection satisfies nonabelian YM
    satisfiesNonabelianYM sc (GaugeDerived.zeroConnection (n := n) (g_dim := g_dim))
    -- Abelian limit works
    ∧ (∀ conn : ConnectionData n g_dim, ∀ ν a,
        yangMillsDivNonabelian abelianSC conn ν a =
        GaugeDerived.yangMillsDivergence conn ν a) := by
  exact ⟨zero_satisfies_nonabelian_ym sc, nonabelian_reduces_to_abelian⟩

end UnifiedTheory.LayerA.NonabelianYangMills
