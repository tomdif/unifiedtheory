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

/-- **Key lemma: Jacobi contraction with triple product vanishes.**
    ∑_{b,d,e,f} c(a,b,d)·c(d,e,f) · [A_l(b)·A_μ(e)·A_ν(f) + cyclic] = 0
    by the Jacobi identity on the structure constants. -/
theorem jacobi_triple_vanishes
    (sc : StructureConstants g_dim)
    (a : Fin g_dim) (P Q R : Fin g_dim → ℝ) :
    ∑ b : Fin g_dim, ∑ d : Fin g_dim, ∑ e : Fin g_dim, ∑ f : Fin g_dim,
      sc.c a b d * sc.c d e f * (P b * Q e * R f + Q b * R e * P f + R b * P e * Q f) = 0 := by
  -- Factor: each summand = P(b)*Q(e)*R(f) * [c(a,b,d)*c(d,e,f)] + (cyclic relabelings)
  -- After relabeling dummy indices in the 2nd and 3rd terms, all three have
  -- the same P(b)*Q(e)*R(f) factor with coefficient ∑_d Jacobi(...) = 0.
  --
  -- More precisely: the sum equals
  -- ∑_{b,e,f} P(b)*Q(e)*R(f) * [∑_d (c_abd*c_def + c_aed*c_dfb + c_afd*c_dbe)]
  -- and the inner sum vanishes by the Jacobi identity.
  --
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
    have combine : (∑ d : Fin g_dim, (sc.c a b' d * sc.c d e' f' + sc.c a e' d * sc.c d f' b' + sc.c a f' d * sc.c d b' e')) =
      -(∑ d, (sc.c d b' e' * sc.c a d f' + sc.c d e' f' * sc.c a d b' + sc.c d f' b' * sc.c a d e')) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun d _ => step d)
    rw [combine, hj, neg_zero]
  -- STRATEGY: Factor out ∑_d first, then relabel the 3-fold sums.
  -- Step 1: Distribute into 3 terms
  simp_rw [mul_add, Finset.sum_add_distrib]
  -- Step 2: In each term, factor the d-sum out:
  --   ∑_b ∑_d ∑_e ∑_f c_abd*c_def*X = ∑_b ∑_e ∑_f X * (∑_d c_abd*c_def)
  -- Step 3: Relabel b,e,f in terms 2 and 3 (3-fold sums, much simpler)
  -- Step 4: Combine coefficient = jc(b,e,f) = 0

  -- Define C(b,e,f) = ∑_d c_abd*c_def (one-third of the Jacobi coefficient)
  -- Term 1 = ∑_b ∑_e ∑_f P_b*Q_e*R_f * C(b,e,f)
  -- Term 2 = ∑_b ∑_e ∑_f Q_b*R_e*P_f * C(b,e,f)
  --        = ∑_b ∑_e ∑_f P_b*Q_e*R_f * C(e,f,b)  [relabel b→e,e→f,f→b]
  -- Term 3 = ∑_b ∑_e ∑_f R_b*P_e*Q_f * C(b,e,f)
  --        = ∑_b ∑_e ∑_f P_b*Q_e*R_f * C(f,b,e)  [relabel b→f,e→b,f→e]
  -- Total = ∑_b ∑_e ∑_f P*Q*R * (C(b,e,f) + C(e,f,b) + C(f,b,e)) = ∑ P*Q*R*jc = 0

  -- Factor d-sum out of each term
  have factor : ∀ (X : Fin g_dim → Fin g_dim → Fin g_dim → ℝ),
      (∑ b : Fin g_dim, ∑ d, ∑ e, ∑ f, sc.c a b d * sc.c d e f * X b e f) =
      ∑ b, ∑ e, ∑ f, X b e f * (∑ d, sc.c a b d * sc.c d e f) := by
    intro X; apply Finset.sum_congr rfl; intro b _
    -- For fixed b: ∑_d ∑_e ∑_f c*c*X = ∑_e ∑_f X*(∑_d c*c)
    -- Proof: swap d past e and f, then factor
    -- For fixed b: ∑_d ∑_e ∑_f c*c*X = ∑_e ∑_f X*(∑_d c*c)
    -- Proof: the d-sum factors out because X doesn't depend on d
    show (∑ d : Fin g_dim, ∑ e, ∑ f, sc.c a b d * sc.c d e f * X b e f) =
      ∑ e, ∑ f, X b e f * ∑ d, sc.c a b d * sc.c d e f
    -- Rewrite summand
    have hfact : ∀ d e f : Fin g_dim, sc.c a b d * sc.c d e f * X b e f =
        X b e f * (sc.c a b d * sc.c d e f) := fun d e f => by ring
    simp_rw [hfact]
    -- Goal: ∑_d ∑_e ∑_f X(b,e,f)*cc(b,d,e,f) = ∑_e ∑_f X(b,e,f)*(∑_d cc(b,d,e,f))
    -- Step 1: Move d inside by swapping summation order
    rw [Finset.sum_comm]
    -- Now: ∑_e ∑_d ∑_f X*cc
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_comm]
    -- Now: ∑_f ∑_d X*cc
    apply Finset.sum_congr rfl; intro f _
    -- Now: ∑_d X*cc = X*(∑_d cc) since X doesn't depend on d
    exact (Finset.mul_sum ..).symm
  rw [factor (fun b e f => P b * Q e * R f),
      factor (fun b e f => Q b * R e * P f),
      factor (fun b e f => R b * P e * Q f)]
  -- Relabel Term 2: (b,e,f) → (e,f,b)
  -- Q(b)*R(e)*P(f)*C(b,e,f) summed = P(b)*Q(e)*R(f)*C(e,f,b) summed
  rw [show (∑ b : Fin g_dim, ∑ e, ∑ f,
      Q b * R e * P f * (∑ d, sc.c a b d * sc.c d e f)) =
    ∑ b, ∑ e, ∑ f,
      P b * Q e * R f * (∑ d, sc.c a e d * sc.c d f b) from by
    rw [Finset.sum_comm]  -- swap outermost: b↔e
    apply Finset.sum_congr rfl; intro e₀ _
    rw [Finset.sum_comm]  -- swap next: e₀↔f
    apply Finset.sum_congr rfl; intro f₀ _
    -- After sum_comm: outermost is e₀ (was b), next level is f₀ (was e),
    -- innermost is b₀ (was f). Summand = Q(b₀_orig)*R(e₀_orig)*P(f₀_orig)*C(b,e,f)
    -- where b₀_orig = b₀ (inner), e₀_orig = e₀ (outer), f₀_orig = f₀ (middle).
    -- After renaming (outermost=e₀, middle=f₀, inner=b₀):
    -- summand = Q(b₀)*R(e₀)*P(f₀)*C(b₀,e₀,f₀)
    -- but we want P(b₀)*Q(e₀)*R(f₀)*C(e₀,f₀,b₀)
    -- Wait — after sum_comm, e₀ is the OUTERMOST. Inside it, sum_comm
    -- swaps original_d(=b) and original_e(=f). So the order is e₀,f₀,b₀
    -- meaning: sum over e₀ first, then f₀, then b₀.
    -- The summand value at (e₀,f₀,b₀) is:
    -- Q(e₀)*R(f₀)*P(b₀)*C(e₀,f₀,b₀)   [original summand with b=e₀,e=f₀,f=b₀]
    -- And we want: P(b₀)*Q(e₀)*R(f₀)*C(e₀,f₀,b₀) ✓ (same by mul_comm)
    -- After two sum_comms, the bound vars are (e₀=orig_b, f₀=orig_e, inner=orig_f)
    -- Need to enter the f₀ level and show summands match up to mul_comm
    apply Finset.sum_congr rfl; intro x _
    -- At the summand: Q(orig_b=e₀)*R(orig_e=f₀)*P(orig_f=x)*(∑d c(a,e₀,d)*c(d,f₀,x))
    -- = P(x)*Q(e₀)*R(f₀)*(∑d c(a,e₀,d)*c(d,f₀,x))
    -- The sums are identical; just commute Q*R*P → P*Q*R
    -- Use mul_left_cancel or direct multiplication lemma
    -- Use mul_left_cancel strategy: show LHS and RHS differ only by mul_comm on prefix
    simp only [mul_assoc]
    -- After mul_assoc: LHS = Q(e₀) * (R(x) * (P(f₀) * S))
    --                  RHS = P(f₀) * (Q(e₀) * (R(x) * S))
    -- Use mul_left_comm repeatedly
    simp only [mul_left_comm]]
  -- Relabel Term 3: same strategy
  rw [show (∑ b : Fin g_dim, ∑ e, ∑ f,
      R b * P e * Q f * (∑ d, sc.c a b d * sc.c d e f)) =
    ∑ b, ∑ e, ∑ f,
      P b * Q e * R f * (∑ d, sc.c a f d * sc.c d b e) from by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e₀ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro f₀ _
    apply Finset.sum_congr rfl; intro x _
    simp only [mul_assoc, mul_left_comm]]
  -- Combine the three terms
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro b _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro e _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro f _
  -- Goal: P*Q*R*C(b,e,f) + P*Q*R*C(e,f,b) + P*Q*R*C(f,b,e) = 0
  -- Factor: P*Q*R * (C(b,e,f) + C(e,f,b) + C(f,b,e)) = P*Q*R * jc(b,e,f) = 0
  have : P b * Q e * R f * (∑ d, sc.c a b d * sc.c d e f) +
    P b * Q e * R f * (∑ d, sc.c a e d * sc.c d f b) +
    P b * Q e * R f * (∑ d, sc.c a f d * sc.c d b e) =
    P b * Q e * R f * (∑ d, (sc.c a b d * sc.c d e f +
      sc.c a e d * sc.c d f b + sc.c a f d * sc.c d b e)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; ring
  rw [this, jc, mul_zero]

/-- **Bracket cyclic sum vanishes.**
    The dA·A terms cancel by antisym_sym_product_vanishes.
    The A·A·A terms cancel by jacobi_triple_vanishes. -/
theorem bracket_cyclic_vanishes
    (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim)
    (l_ μ ν : Fin n) (a : Fin g_dim) :
    bracketPart sc conn l_ μ ν a + bracketPart sc conn μ ν l_ a +
    bracketPart sc conn ν l_ μ a = 0 := by
  simp only [bracketPart]
  -- Distribute the sums and group by type
  -- The dA·A + A·dA terms form antisymmetric products → vanish
  -- The A·A·A terms form Jacobi contractions → vanish
  sorry

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
