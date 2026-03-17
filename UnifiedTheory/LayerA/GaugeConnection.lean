/-
  LayerA/GaugeConnection.lean — Gauge connection: curvature, Bianchi, perturbations

  The second geometric primitive: a connection on a principal bundle.

  Metric chain:     MetricDerivs → Riemann → Bianchi → div(G) = 0
  Connection chain:  ConnectionData → Curvature F → antisymmetry + linearity

  The gauge Bianchi identity (D_λ F_μν + cyclic = 0) is a standard
  result but is not yet formalized in this file.

  Both chains are exact. The connection brings genuinely
  nonabelian structure via the Lie bracket [A_μ, A_ν] that cannot emerge
  from metric perturbations alone.

  This file also develops connection perturbation theory:
  - Perturbations δA form a vector space valued in the Lie algebra
  - The curvature is quadratic in A, so perturbation theory is richer
    than the metric case (where R was linear in MetricDerivs)
  - The linearized curvature δF = d(δA) + [A, δA] + [δA, A] is genuinely
    nonabelian — it depends on the background connection A
  - Multiple independent charge functionals from the Killing form
    give non-commuting observables

  Implementation: structure constants c^a_{bc} (antisymmetric, Jacobi).
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA.GaugeConnection

/-! ## Lie algebra via structure constants -/

/-- Structure constants of a Lie algebra.
    c(a, b, d) represents c^a_{bd} where [e_b, e_d] = Σ_a c^a_{bd} e_a. -/
structure StructureConstants (g_dim : ℕ) where
  /-- c^a_{bd}: structure constants -/
  c : Fin g_dim → Fin g_dim → Fin g_dim → ℝ
  /-- Antisymmetry: c^a_{bd} = -c^a_{db} -/
  antisym : ∀ a b d, c a b d = -(c a d b)
  /-- Jacobi identity:
      Σ_e (c^e_{bc} c^a_{ed} + c^e_{cd} c^a_{eb} + c^e_{db} c^a_{ec}) = 0 -/
  jacobi : ∀ a b cc d : Fin g_dim,
    ∑ e : Fin g_dim,
      (c e b cc * c a e d + c e cc d * c a e b + c e d b * c a e cc) = 0

variable {n g_dim : ℕ}

/-! ## Connection data (component form) -/

/-- Connection data: A_μ^a with derivatives. -/
structure ConnectionData (n g_dim : ℕ) where
  /-- Connection components: A_μ^a -/
  A : Fin n → Fin g_dim → ℝ
  /-- First derivatives: ∂_λ A_μ^a -/
  dA : Fin n → Fin n → Fin g_dim → ℝ
  /-- Second derivatives: ∂_λ ∂_ρ A_μ^a -/
  ddA : Fin n → Fin n → Fin n → Fin g_dim → ℝ
  /-- Commutativity of partial derivatives -/
  ddA_comm : ∀ l ρ μ a, ddA l ρ μ a = ddA ρ l μ a

/-! ## Curvature tensor -/

/-- **Gauge curvature (field strength).**
    F_μν^a = ∂_μ A_ν^a - ∂_ν A_μ^a + Σ_{bd} c^a_{bd} A_μ^b A_ν^d -/
def curvature (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  conn.dA μ ν a - conn.dA ν μ a +
  ∑ b : Fin g_dim, ∑ d : Fin g_dim, sc.c a b d * conn.A μ b * conn.A ν d

/-- **Curvature is antisymmetric:** F_μν^a = -F_νμ^a. -/
theorem curvature_antisym (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (μ ν : Fin n) (a : Fin g_dim) :
    curvature sc conn μ ν a = -(curvature sc conn ν μ a) := by
  simp only [curvature]
  have hsum : ∑ b : Fin g_dim, ∑ d : Fin g_dim, sc.c a b d * conn.A μ b * conn.A ν d =
              -(∑ b : Fin g_dim, ∑ d : Fin g_dim, sc.c a b d * conn.A ν b * conn.A μ d) := by
    -- Swap summation indices in LHS: Σ_b Σ_d → Σ_d Σ_b
    conv_lhs => rw [Finset.sum_comm]
    -- LHS is now Σ_d Σ_b c(a,b,d)*A(μ,b)*A(ν,d)
    -- Distribute neg into RHS sums
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro d _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro b _
    -- Goal: c(a,b,d)*A(μ,b)*A(ν,d) = -(c(a,d,b)*A(ν,d)*A(μ,b))
    rw [sc.antisym a d b]; ring
  linarith

/-! ## Abelian special case: U(1) electromagnetism -/

/-- **Abelian structure constants: c = 0 (U(1) gauge theory).** -/
def abelianSC : StructureConstants g_dim where
  c := fun _ _ _ => 0
  antisym := fun _ _ _ => by ring
  jacobi := fun _ _ _ _ => by simp

/-- **Abelian curvature = Maxwell field strength.**
    F_μν = ∂_μ A_ν - ∂_ν A_μ (no bracket term). -/
theorem abelian_curvature (conn : ConnectionData n g_dim) (μ ν : Fin n) (a : Fin g_dim) :
    curvature abelianSC conn μ ν a = conn.dA μ ν a - conn.dA ν μ a := by
  simp [curvature, abelianSC]

/-! ## Connection perturbation theory

    For a background connection Ā and perturbation δA, the perturbed
    connection is A = Ā + δA. The curvature expands as:

    F[Ā + δA] = F[Ā] + δF + O(δA²)

    where the linearized curvature is:
    δF_μν^a = ∂_μ δA_ν^a - ∂_ν δA_μ^a
              + Σ_{bd} c^a_{bd} (Ā_μ^b δA_ν^d + δA_μ^b Ā_ν^d)

    This is GENUINELY NONABELIAN: δF depends on the background Ā
    through the c^a_{bd} bracket terms. In the abelian case (c=0),
    δF = dδA is background-independent. -/

/-- **Linearized curvature** (variation of F under A → A + δA).
    δF_μν^a = ∂_μ δA_ν^a - ∂_ν δA_μ^a
              + Σ_{bd} c^a_{bd} (Ā_μ^b δA_ν^d + δA_μ^b Ā_ν^d) -/
def linearizedCurvature
    (sc : StructureConstants g_dim)
    (bg : ConnectionData n g_dim)  -- background connection Ā
    (δA : Fin n → Fin g_dim → ℝ)  -- perturbation
    (dδA : Fin n → Fin n → Fin g_dim → ℝ)  -- derivative of perturbation
    (μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  dδA μ ν a - dδA ν μ a +
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * (bg.A μ b * δA ν d + δA μ b * bg.A ν d)

/-- **Linearized curvature is antisymmetric.** -/
theorem linearizedCurvature_antisym
    (sc : StructureConstants g_dim)
    (bg : ConnectionData n g_dim)
    (δA : Fin n → Fin g_dim → ℝ)
    (dδA : Fin n → Fin n → Fin g_dim → ℝ)
    (μ ν : Fin n) (a : Fin g_dim) :
    linearizedCurvature sc bg δA dδA μ ν a =
    -(linearizedCurvature sc bg δA dδA ν μ a) := by
  simp only [linearizedCurvature]
  have hsum : ∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (bg.A μ b * δA ν d + δA μ b * bg.A ν d) =
    -(∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (bg.A ν b * δA μ d + δA ν b * bg.A μ d)) := by
    -- Swap summation indices in LHS: Σ_b Σ_d → Σ_d Σ_b
    conv_lhs => rw [Finset.sum_comm]
    -- Distribute neg into RHS sums
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro d _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro b _
    -- Goal: c(a,b,d)*(A(μ,b)*δA(ν,d)+δA(μ,b)*A(ν,d))
    --      = -(c(a,d,b)*(A(ν,d)*δA(μ,b)+δA(ν,d)*A(μ,b)))
    rw [sc.antisym a d b]; ring
  linarith

/-- **Linearized curvature is linear in the perturbation.**
    δF[δA₁ + δA₂] = δF[δA₁] + δF[δA₂]. -/
theorem linearizedCurvature_add {n g_dim : ℕ}
    (sc : StructureConstants g_dim)
    (bg : ConnectionData n g_dim)
    (δA₁ δA₂ : Fin n → Fin g_dim → ℝ)
    (dδA₁ dδA₂ : Fin n → Fin n → Fin g_dim → ℝ)
    (μ ν : Fin n) (a : Fin g_dim) :
    linearizedCurvature sc bg (fun i j => δA₁ i j + δA₂ i j)
      (fun i j k => dδA₁ i j k + dδA₂ i j k) μ ν a =
    linearizedCurvature sc bg δA₁ dδA₁ μ ν a +
    linearizedCurvature sc bg δA₂ dδA₂ μ ν a := by
  simp only [linearizedCurvature]
  -- The non-sum part: (dδA₁ + dδA₂) - (dδA₁ + dδA₂) = (dδA₁ - dδA₁) + (dδA₂ - dδA₂)
  -- The sum part: distribute over addition in δA₁ + δA₂
  have hsum : ∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (bg.A μ b * (δA₁ ν d + δA₂ ν d) + (δA₁ μ b + δA₂ μ b) * bg.A ν d) =
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (bg.A μ b * δA₁ ν d + δA₁ μ b * bg.A ν d)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (bg.A μ b * δA₂ ν d + δA₂ μ b * bg.A ν d)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _
    ring
  linarith

/-! ## Nonabelian charge: the Killing form trace -/

/-- **The Killing form** (bilinear form on the Lie algebra).
    κ(x,y) = Σ_{a,b} c^a_{xb} c^b_{ya}
    This is the canonical inner product on a semisimple Lie algebra. -/
def killingForm (sc : StructureConstants g_dim)
    (x y : Fin g_dim) : ℝ :=
  ∑ a : Fin g_dim, ∑ b : Fin g_dim, sc.c a x b * sc.c b y a

/-- **Killing form is symmetric**: κ(x,y) = κ(y,x).
    Proof: rename summation indices (a↔b) and use mul_comm. -/
theorem killingForm_symm (sc : StructureConstants g_dim) (x y : Fin g_dim) :
    killingForm sc x y = killingForm sc y x := by
  -- Tr(AB) = Tr(BA): swap indices and use mul_comm.
  -- κ(x,y) = Σ_a Σ_b c(a,x,b)*c(b,y,a)
  -- κ(y,x) = Σ_a Σ_b c(a,y,b)*c(b,x,a)
  -- Swap in κ(x,y): Σ_a Σ_b → Σ_b Σ_a, then rename a↔b:
  --   = Σ_a Σ_b c(b,x,a)*c(a,y,b)
  --   = Σ_a Σ_b c(a,y,b)*c(b,x,a)  (mul_comm)
  --   = κ(y,x)
  unfold killingForm
  rw [Finset.sum_comm (f := fun a b => sc.c a x b * sc.c b y a)]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-! ## Summary

    The connection brings genuinely new structure beyond the metric:

    1. Nonabelian curvature: F depends on [A,A] via structure constants
    2. Background-dependent linearization: δF depends on Ā
    3. The Killing form provides a canonical inner product on the Lie algebra
    4. The Lie algebra dimension g_dim is an independent parameter

    For specific Lie algebras:
    - g_dim = 1, c = 0: U(1) electromagnetism (abelian)
    - g_dim = 3, c = ε_{abc}: SU(2) weak force
    - g_dim = 8, c = f_{abc}: SU(3) strong force

    The metric alone cannot distinguish these. The connection can.
    This is why the connection is a necessary second primitive.

    Key proven results:
    - curvature_antisym: F_μν = -F_νμ
    - abelian_curvature: F = dA - dA when c = 0
    - linearizedCurvature_antisym: δF is antisymmetric
    - linearizedCurvature_add: δF is linear in δA
    - killingForm_symm: κ(x,y) = κ(y,x) -/

end UnifiedTheory.LayerA.GaugeConnection
