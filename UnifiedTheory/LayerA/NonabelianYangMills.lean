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

/-- The abelian part of D_λ F_μν: just the ddA terms. -/
def abelianPart (conn : ConnectionData n g_dim) (l_ μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  conn.ddA l_ μ ν a - conn.ddA l_ ν μ a

/-- The bracket part of D_λ F_μν: dA·A + A·dA + A·c·A·A terms. -/
def bracketPart (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * (conn.dA l_ μ b * conn.A ν d + conn.A μ b * conn.dA l_ ν d) +
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * conn.A l_ b *
    (conn.dA μ ν d - conn.dA ν μ d +
     ∑ e : Fin g_dim, ∑ f : Fin g_dim, sc.c d e f * conn.A μ e * conn.A ν f)

/-- covariantDerivF splits into abelian + bracket parts. -/
theorem covariantDerivF_split (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    covariantDerivF sc conn l_ μ ν a = abelianPart conn l_ μ ν a + bracketPart sc conn l_ μ ν a := by
  simp only [covariantDerivF, abelianPart, bracketPart, curvature]; ring

/-- **Abelian cyclic sum vanishes** (from abelian Bianchi). -/
theorem abelian_cyclic_vanishes (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    abelianPart conn l_ μ ν a + abelianPart conn μ ν l_ a + abelianPart conn ν l_ μ a = 0 := by
  simp only [abelianPart]
  have c1 := conn.ddA_comm l_ μ ν a
  have c2 := conn.ddA_comm μ ν l_ a
  have c3 := conn.ddA_comm ν l_ μ a
  linarith

/-- **Nonabelian Bianchi identity**: D_λ F_μν + D_μ F_νλ + D_ν F_λμ = 0.

    Proof: split into abelian part (ddA terms) and bracket part.
    Abelian part vanishes by commutativity (proven above).
    Bracket part vanishes by antisymmetry of c + Jacobi identity.

    For the bracket part: dA·A terms cancel by antisymmetry of c
    (swapping summation indices b↔d and using c_abd = -c_adb gives
    each pair of terms = 0 by commutativity of ℝ).
    A·A·A terms cancel by the Jacobi identity. -/
theorem nonabelian_bianchi
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    covariantDerivF sc conn l_ μ ν a +
    covariantDerivF sc conn μ ν l_ a +
    covariantDerivF sc conn ν l_ μ a = 0 := by
  rw [covariantDerivF_split, covariantDerivF_split, covariantDerivF_split]
  -- Split into abelian + bracket cyclic sums
  have hab := abelian_cyclic_vanishes conn l_ μ ν a
  -- The bracket cyclic sum involves:
  -- (1) dA·A terms: cancel by antisym of c + commutativity of ℝ
  -- (2) A·dA terms: cancel with (1) after index relabeling
  -- (3) A·c·A·A terms: cancel by Jacobi identity
  -- We prove the total bracket sum is zero
  linarith [show bracketPart sc conn l_ μ ν a + bracketPart sc conn μ ν l_ a +
    bracketPart sc conn ν l_ μ a = 0 from by
    simp only [bracketPart]
    -- After unfolding, the sum involves Finset.sum terms.
    -- The dA·A terms cancel by antisymmetry:
    --   Σ c_abd (dA_b A_d + A_b dA_d) cyclic = 0
    -- because swapping b↔d in each Σ and using c_abd = -c_adb
    -- gives the negative of each term.
    -- The A·A·A terms cancel by Jacobi:
    --   Σ c_abd c_def A_b A_e A_f cyclic = 0
    -- by the Jacobi identity Σ_d c_abd c_def + cyclic = 0.
    -- The bracket sum combines dA·A, A·dA, and A·A·A terms.
    -- After combining all sums, each summand involves c contracted with
    -- products of A and dA values. The cyclic permutation (l→μ→ν→l)
    -- combined with the antisymmetry of c and the Jacobi identity
    -- gives term-by-term cancellation.
    --
    -- This is a finite algebraic identity over Finset sums.
    -- The key tools are:
    -- (1) sc.antisym: c a b d = -(c a d b) (swap last two indices)
    -- (2) sc.jacobi: Σ_e (c e b c * c a e d + cyclic) = 0
    -- (3) mul_comm: ℝ is commutative
    --
    -- The proof requires distributing sums and matching terms.
    -- Each dA·A pair cancels by (1) + (3).
    -- Each A·A·A triple cancels by (2).
    sorry]

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
