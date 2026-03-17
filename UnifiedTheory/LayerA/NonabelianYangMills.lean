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

/-- **Key lemma: antisymmetric contraction with symmetric product vanishes.**
    ∑_{b,d} c(a,b,d) · (X(b) · Y(d) + X(d) · Y(b)) = 0
    when c is antisymmetric in the last two indices.
    Proof: swap b↔d in the second term, antisym gives -, mul_comm cancels. -/
theorem antisym_sym_product_vanishes
    (c : Fin g_dim → Fin g_dim → Fin g_dim → ℝ)
    (hc : ∀ a b d, c a b d = -(c a d b))
    (a : Fin g_dim) (X Y : Fin g_dim → ℝ) :
    ∑ b : Fin g_dim, ∑ d : Fin g_dim, c a b d * (X b * Y d + X d * Y b) = 0 := by
  -- Rewrite each summand: c(a,b,d)*(X(b)*Y(d) + X(d)*Y(b))
  -- = c(a,b,d)*X(b)*Y(d) + c(a,b,d)*X(d)*Y(b)
  -- The full double sum = S₁ + S₂ where
  -- S₁ = ∑_{b,d} c(a,b,d)*X(b)*Y(d)
  -- S₂ = ∑_{b,d} c(a,b,d)*X(d)*Y(b)
  -- In S₂, swap b↔d: S₂ = ∑_{d,b} c(a,d,b)*X(b)*Y(d) = ∑_{b,d} c(a,d,b)*X(b)*Y(d)
  -- By antisym: c(a,d,b) = -c(a,b,d)
  -- So S₂ = -∑_{b,d} c(a,b,d)*X(b)*Y(d) = -S₁
  -- Total: S₁ + S₂ = S₁ - S₁ = 0
  simp_rw [mul_add]
  rw [show (∑ b : Fin g_dim, ∑ d, (c a b d * (X b * Y d) + c a b d * (X d * Y b))) =
    (∑ b, ∑ d, c a b d * (X b * Y d)) + (∑ b, ∑ d, c a b d * (X d * Y b)) from by
      simp_rw [← Finset.sum_add_distrib]]
  -- Swap indices in second sum
  have : (∑ b : Fin g_dim, ∑ d, c a b d * (X d * Y b)) =
      -(∑ b, ∑ d, c a b d * (X b * Y d)) := by
    rw [Finset.sum_comm (f := fun b d => c a b d * (X d * Y b))]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro b _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro d _
    rw [hc a d b]; ring
  rw [this, add_neg_cancel]

/-- Helper: reverse cyclic permutation of a triple nested sum.
    ∑_b ∑_e ∑_f g(b,e,f) = ∑_b ∑_e ∑_f g(f,b,e). -/
private theorem sum3_rev_cycle (g : Fin g_dim → Fin g_dim → Fin g_dim → ℝ) :
    ∑ b : Fin g_dim, ∑ e : Fin g_dim, ∑ f : Fin g_dim, g b e f =
    ∑ b, ∑ e, ∑ f, g f b e := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e₀ _
  rw [Finset.sum_comm]

/-- Helper: forward cyclic permutation.
    ∑_b ∑_e ∑_f g(b,e,f) = ∑_b ∑_e ∑_f g(e,f,b). -/
private theorem sum3_fwd_cycle (g : Fin g_dim → Fin g_dim → Fin g_dim → ℝ) :
    ∑ b : Fin g_dim, ∑ e : Fin g_dim, ∑ f : Fin g_dim, g b e f =
    ∑ b, ∑ e, ∑ f, g e f b := by
  rw [sum3_rev_cycle (g := g)]
  rw [sum3_rev_cycle (g := fun b e f => g f b e)]

/-- **Key lemma: Jacobi contraction with triple product vanishes.**
    ∑_{b,d,e,f} c(a,b,d)·c(d,e,f) · [A_l(b)·A_μ(e)·A_ν(f) + cyclic] = 0
    by the Jacobi identity on the structure constants. -/
theorem jacobi_triple_vanishes
    (sc : StructureConstants g_dim)
    (a : Fin g_dim) (P Q R : Fin g_dim → ℝ) :
    ∑ b : Fin g_dim, ∑ d : Fin g_dim, ∑ e : Fin g_dim, ∑ f : Fin g_dim,
      sc.c a b d * sc.c d e f * (P b * Q e * R f + Q b * R e * P f + R b * P e * Q f) = 0 := by
  -- The Jacobi coefficient vanishes for all b,e,f:
  have jc : ∀ b' e' f' : Fin g_dim,
      ∑ d : Fin g_dim, (sc.c a b' d * sc.c d e' f' +
        sc.c a e' d * sc.c d f' b' + sc.c a f' d * sc.c d b' e') = 0 := by
    intro b' e' f'
    have hj := sc.jacobi a b' e' f'
    have step : ∀ d : Fin g_dim,
        sc.c a b' d * sc.c d e' f' + sc.c a e' d * sc.c d f' b' + sc.c a f' d * sc.c d b' e' =
        -(sc.c d b' e' * sc.c a d f' + sc.c d e' f' * sc.c a d b' + sc.c d f' b' * sc.c a d e') := by
      intro d; rw [sc.antisym a b' d, sc.antisym a e' d, sc.antisym a f' d]; ring
    have combine : (∑ d : Fin g_dim, (sc.c a b' d * sc.c d e' f' + sc.c a e' d * sc.c d f' b' +
        sc.c a f' d * sc.c d b' e')) =
      -(∑ d, (sc.c d b' e' * sc.c a d f' + sc.c d e' f' * sc.c a d b' +
        sc.c d f' b' * sc.c a d e')) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun d _ => step d)
    rw [combine, hj, neg_zero]
  -- Distribute into 3 terms
  simp_rw [mul_add, Finset.sum_add_distrib]
  -- Factor d-sum out of each term
  have factor : ∀ (X : Fin g_dim → Fin g_dim → Fin g_dim → ℝ),
      (∑ b : Fin g_dim, ∑ d, ∑ e, ∑ f, sc.c a b d * sc.c d e f * X b e f) =
      ∑ b, ∑ e, ∑ f, X b e f * (∑ d, sc.c a b d * sc.c d e f) := by
    intro X; apply Finset.sum_congr rfl; intro b _
    show (∑ d : Fin g_dim, ∑ e, ∑ f, sc.c a b d * sc.c d e f * X b e f) =
      ∑ e, ∑ f, X b e f * ∑ d, sc.c a b d * sc.c d e f
    simp_rw [fun d e f => show sc.c a b d * sc.c d e f * X b e f =
        X b e f * (sc.c a b d * sc.c d e f) from by ring]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro f _
    exact (Finset.mul_sum ..).symm
  rw [factor (fun b e f => P b * Q e * R f),
      factor (fun b e f => Q b * R e * P f),
      factor (fun b e f => R b * P e * Q f)]
  set C := fun b e f => ∑ d : Fin g_dim, sc.c a b d * sc.c d e f with hC
  -- Relabel T₂ using forward cycle
  have ht2 : (∑ b : Fin g_dim, ∑ e, ∑ f,
      Q b * R e * P f * C b e f) =
    ∑ b, ∑ e, ∑ f, P b * Q e * R f * C e f b := by
    rw [sum3_fwd_cycle (g := fun b e f => Q b * R e * P f * C b e f)]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro e _
    apply Finset.sum_congr rfl; intro f _; ring
  -- Relabel T₃ using reverse cycle
  have ht3 : (∑ b : Fin g_dim, ∑ e, ∑ f,
      R b * P e * Q f * C b e f) =
    ∑ b, ∑ e, ∑ f, P b * Q e * R f * C f b e := by
    rw [sum3_rev_cycle (g := fun b e f => R b * P e * Q f * C b e f)]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro e _
    apply Finset.sum_congr rfl; intro f _; ring
  rw [ht2, ht3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro b _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro e _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro f _
  have hcombine : P b * Q e * R f * C b e f +
    P b * Q e * R f * C e f b +
    P b * Q e * R f * C f b e =
    P b * Q e * R f * (C b e f + C e f b + C f b e) := by ring
  rw [hcombine]
  simp only [hC]
  rw [show (∑ d, sc.c a b d * sc.c d e f) + (∑ d, sc.c a e d * sc.c d f b) +
    (∑ d, sc.c a f d * sc.c d b e) =
    ∑ d, (sc.c a b d * sc.c d e f + sc.c a e d * sc.c d f b +
      sc.c a f d * sc.c d b e) from by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]]
  rw [jc, mul_zero]

/-- **Bracket cyclic sum vanishes.**
    The dA·A terms cancel by antisym_sym_product_vanishes.
    The A·A·A terms cancel by jacobi_triple_vanishes. -/
-- Helper definitions for splitting bracketPart
private def dAPart (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * (conn.dA l_ μ b * conn.A ν d + conn.A μ b * conn.dA l_ ν d) +
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * conn.A l_ b * (conn.dA μ ν d - conn.dA ν μ d)

private def AAAPart (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) : ℝ :=
  ∑ b : Fin g_dim, ∑ d : Fin g_dim,
    sc.c a b d * conn.A l_ b *
    (∑ e : Fin g_dim, ∑ f : Fin g_dim, sc.c d e f * conn.A μ e * conn.A ν f)

private theorem bracketPart_eq_dA_plus_AAA (sc : StructureConstants g_dim)
    (conn : ConnectionData n g_dim) (l_ μ ν : Fin n) (a : Fin g_dim) :
    bracketPart sc conn l_ μ ν a = dAPart sc conn l_ μ ν a + AAAPart sc conn l_ μ ν a := by
  simp only [bracketPart, dAPart, AAAPart]
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private theorem dA_cyclic_vanishes
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    dAPart sc conn l_ μ ν a + dAPart sc conn μ ν l_ a + dAPart sc conn ν l_ μ a = 0 := by
  simp only [dAPart]
  -- Use antisym_sym_product_vanishes for the three cyclic pairs
  have h1 := antisym_sym_product_vanishes (sc.c) sc.antisym a (conn.dA l_ μ) (conn.A ν)
  have h2 := antisym_sym_product_vanishes (sc.c) sc.antisym a (conn.dA μ ν) (conn.A l_)
  have h3 := antisym_sym_product_vanishes (sc.c) sc.antisym a (conn.dA ν l_) (conn.A μ)
  -- Show the goal equals h1 + h2 + h3 = 0 + 0 + 0 = 0
  -- by converting both sides to the same normal form.
  -- Goal after simp only [dAPart]:
  --   (∑∑ c*(dA(l_,μ)*A(ν) + A(μ)*dA(l_,ν)) + ∑∑ c*A(l_)*(dA(μ,ν) - dA(ν,μ)))
  -- + (∑∑ c*(dA(μ,ν)*A(l_) + A(ν)*dA(μ,l_)) + ∑∑ c*A(μ)*(dA(ν,l_) - dA(l_,ν)))
  -- + (∑∑ c*(dA(ν,l_)*A(μ) + A(l_)*dA(ν,μ)) + ∑∑ c*A(ν)*(dA(l_,μ) - dA(μ,l_)))
  -- = 0
  --
  -- h1: ∑∑ c*(dA(l_,μ)*A(ν) + dA(l_,μ,·swapped·)*A(ν,·swapped·)) = 0
  -- The key insight: the goal can be rewritten as h1+h2+h3 if we first
  -- show that ∑∑ c*A(σ₁,b)*(dA(σ₂,σ₃,d)) can be expressed via antisym_sym
  --
  -- Direct approach: show goal = h1 + h2 + h3 by converting to a single ∑∑
  -- and showing summands match by ring.
  suffices goal_eq :
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA l_ μ b * conn.A ν d + conn.A μ b * conn.dA l_ ν d)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * conn.A l_ b * (conn.dA μ ν d - conn.dA ν μ d)) +
    ((∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA μ ν b * conn.A l_ d + conn.A ν b * conn.dA μ l_ d)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * conn.A μ b * (conn.dA ν l_ d - conn.dA l_ ν d))) +
    ((∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA ν l_ b * conn.A μ d + conn.A l_ b * conn.dA ν μ d)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * conn.A ν b * (conn.dA l_ μ d - conn.dA μ l_ d))) =
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA l_ μ b * conn.A ν d + conn.dA l_ μ d * conn.A ν b)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA μ ν b * conn.A l_ d + conn.dA μ ν d * conn.A l_ b)) +
    (∑ b : Fin g_dim, ∑ d : Fin g_dim,
      sc.c a b d * (conn.dA ν l_ b * conn.A μ d + conn.dA ν l_ d * conn.A μ b)) by
    rw [goal_eq]; linarith
  -- Merge all double sums into one double sum, then show summands equal by ring
  simp only [sub_eq_add_neg, mul_neg, neg_mul, mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro d _
  ring

private theorem AAA_cyclic_vanishes
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    AAAPart sc conn l_ μ ν a + AAAPart sc conn μ ν l_ a + AAAPart sc conn ν l_ μ a = 0 := by
  simp only [AAAPart]
  simp_rw [Finset.mul_sum, mul_assoc]
  have hj := jacobi_triple_vanishes sc a (conn.A l_) (conn.A μ) (conn.A ν)
  simp_rw [mul_add, Finset.sum_add_distrib] at hj
  simp_rw [mul_assoc, mul_left_comm] at hj ⊢
  linarith

theorem bracket_cyclic_vanishes
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    bracketPart sc conn l_ μ ν a + bracketPart sc conn μ ν l_ a +
    bracketPart sc conn ν l_ μ a = 0 := by
  rw [bracketPart_eq_dA_plus_AAA, bracketPart_eq_dA_plus_AAA, bracketPart_eq_dA_plus_AAA]
  have hdA := dA_cyclic_vanishes sc conn l_ μ ν a
  have hAAA := AAA_cyclic_vanishes sc conn l_ μ ν a
  linarith

/-- **Nonabelian Bianchi identity**: D_λ F_μν + D_μ F_νλ + D_ν F_λμ = 0.

    Proof: split into abelian part (ddA terms) and bracket part.
    Abelian part vanishes by commutativity (proven).
    Bracket part vanishes by antisymmetry of c + Jacobi identity. -/
theorem nonabelian_bianchi
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    covariantDerivF sc conn l_ μ ν a +
    covariantDerivF sc conn μ ν l_ a +
    covariantDerivF sc conn ν l_ μ a = 0 := by
  rw [covariantDerivF_split, covariantDerivF_split, covariantDerivF_split]
  have hab := abelian_cyclic_vanishes conn l_ μ ν a
  have hbr := bracket_cyclic_vanishes sc conn l_ μ ν a
  linarith

/-! ## Summary -/

/-- **NONABELIAN YANG-MILLS SUMMARY.**

    The full nonabelian gauge sector is formalized:

    (1) Covariant derivative D_μ T^a = ∂_μ T^a + c^a_{bd} A_μ^b T^d
    (2) Covariant derivative of field strength D_λ F_μν
    (3) Nonabelian Yang-Mills equation D^μ F_μν = 0
    (4) Zero connection is a solution (trivially)
    (5) Abelian limit: nonabelian reduces to abelian when c = 0
    (6) Nonabelian Bianchi: D_λ F_μν + cyclic = 0 (fully proven via Jacobi identity)

    This upgrades the gauge sector from "abelian only" to "full nonabelian"
    with zero sorries. The Bianchi identity is fully proven using
    antisymmetry of structure constants and the Jacobi identity. -/
theorem nonabelian_ym_summary (sc : StructureConstants g_dim) :
    -- Zero connection satisfies nonabelian YM
    satisfiesNonabelianYM sc (GaugeDerived.zeroConnection (n := n) (g_dim := g_dim))
    -- Abelian limit works
    ∧ (∀ conn : ConnectionData n g_dim, ∀ ν a,
        yangMillsDivNonabelian abelianSC conn ν a =
        GaugeDerived.yangMillsDivergence conn ν a) := by
  exact ⟨zero_satisfies_nonabelian_ym sc, nonabelian_reduces_to_abelian⟩

end UnifiedTheory.LayerA.NonabelianYangMills
