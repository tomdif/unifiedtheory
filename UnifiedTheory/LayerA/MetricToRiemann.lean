/-
  LayerA/MetricToRiemann.lean — Construct RiemannData from metric derivatives

  Proves ALL axioms of RiemannData (symmetries + Bianchi) as theorems,
  by constructing the Riemann tensor from second derivatives of the metric
  in normal coordinates.

  Key identity: R_{abcd} = ½(h(c,b,a,d) - h(c,a,b,d) - h(d,b,a,c) + h(d,a,b,c))
  where h(e,f,a,b) = ∂_e ∂_f g_{ab}.

  The Bianchi identity follows from commutativity of third partial derivatives:
  all 12 terms in the cyclic sum cancel in pairs.

  NO AXIOMS. Everything is derived from metric symmetry + partial commutativity.
-/
import Mathlib.Analysis.Normed.Field.Basic
import UnifiedTheory.LayerA.BianchiIdentity

namespace UnifiedTheory.LayerA.MetricConstruction

variable {n : ℕ}

/-! ### Metric derivative data -/

/-- Second and third derivatives of a metric tensor in normal coordinates.
    h(e,f,a,b) = ∂_e ∂_f g_{ab}, k(e,f,g,a,b) = ∂_e ∂_f ∂_g g_{ab}. -/
structure MetricDerivs (n : ℕ) where
  /-- Second derivatives: h(e,f,a,b) = ∂_e ∂_f g_{ab} -/
  h : Fin n → Fin n → Fin n → Fin n → ℝ
  /-- Metric symmetry: g_{ab} = g_{ba} -/
  h_metric : ∀ e f a b, h e f a b = h e f b a
  /-- Commutativity of partials: ∂_e ∂_f = ∂_f ∂_e -/
  h_comm : ∀ e f a b, h e f a b = h f e a b
  /-- Third derivatives: k(e,f,g,a,b) = ∂_e ∂_f ∂_g g_{ab} -/
  k : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ
  /-- Metric symmetry for k -/
  k_metric : ∀ e f g a b, k e f g a b = k e f g b a
  /-- Commutativity: swap 1st and 2nd derivative indices -/
  k_sym12 : ∀ e f g a b, k e f g a b = k f e g a b
  /-- Commutativity: swap 2nd and 3rd derivative indices -/
  k_sym23 : ∀ e f g a b, k e f g a b = k e g f a b

variable (md : MetricDerivs n)

/-- Derived: swap 1st and 3rd derivative indices of k. -/
lemma k_sym13 (e f g a b : Fin n) : md.k e f g a b = md.k g f e a b := by
  rw [md.k_sym12, md.k_sym23, md.k_sym12]

/-! ### Riemann tensor from metric -/

/-- Riemann tensor in normal coordinates:
    R_{abcd} = ½(h(c,b,a,d) - h(c,a,b,d) - h(d,b,a,c) + h(d,a,b,c)) -/
noncomputable def R_metric (a b c d : Fin n) : ℝ :=
  (md.h c b a d - md.h c a b d - md.h d b a c + md.h d a b c) / 2

/-- Covariant derivative of Riemann (in normal coords, ∇ = ∂):
    (∂_e R)_{abcd} = ½(k(e,c,b,a,d) - k(e,c,a,b,d) - k(e,d,b,a,c) + k(e,d,a,b,c)) -/
noncomputable def dR_metric (e a b c d : Fin n) : ℝ :=
  (md.k e c b a d - md.k e c a b d - md.k e d b a c + md.k e d a b c) / 2

/-! ### Prove all Riemann symmetries -/

/-- **Antisymmetry in first pair**: R_{abcd} = -R_{bacd}.
    Proof: swapping a,b negates every term. -/
theorem R_antisym1 (a b c d : Fin n) :
    R_metric md a b c d = -(R_metric md b a c d) := by
  simp only [R_metric]; ring

/-- **Antisymmetry in second pair**: R_{abcd} = -R_{abdc}.
    Proof: swapping c,d negates every term. -/
theorem R_antisym2 (a b c d : Fin n) :
    R_metric md a b c d = -(R_metric md a b d c) := by
  simp only [R_metric]; ring

/-- **dR inherits first-pair antisymmetry**: ∂_e R_{abcd} = -∂_e R_{bacd}. -/
theorem dR_antisym1 (e a b c d : Fin n) :
    dR_metric md e a b c d = -(dR_metric md e b a c d) := by
  simp only [dR_metric]; ring

/-- **dR inherits second-pair antisymmetry**: ∂_e R_{abcd} = -∂_e R_{abdc}. -/
theorem dR_antisym2 (e a b c d : Fin n) :
    dR_metric md e a b c d = -(dR_metric md e a b d c) := by
  simp only [dR_metric]; ring

/-! ### Prove the second Bianchi identity -/

/-- **Second Bianchi Identity** (the main theorem):
    ∂_e R_{abcd} + ∂_a R_{becd} + ∂_b R_{eacd} = 0

    Proof: expand all three terms using the k-definition, use commutativity
    of third partial derivatives to show all 12 terms cancel in 6 pairs. -/
theorem bianchi2 (e a b c d : Fin n) :
    dR_metric md e a b c d +
    dR_metric md a b e c d +
    dR_metric md b e a c d = 0 := by
  simp only [dR_metric]
  -- After unfolding, we have a sum of k-terms divided by 2.
  -- We need to show the numerator is zero after using k-symmetries.
  -- The 12 k-terms (before dividing by 2) are:
  --   From ∂_e R_{abcd}: k(e,c,b,a,d) - k(e,c,a,b,d) - k(e,d,b,a,c) + k(e,d,a,b,c)
  --   From ∂_a R_{becd}: k(a,c,e,b,d) - k(a,c,b,e,d) - k(a,d,e,b,c) + k(a,d,b,e,c)
  --   From ∂_b R_{eacd}: k(b,c,a,e,d) - k(b,c,e,a,d) - k(b,d,a,e,c) + k(b,d,e,a,c)
  -- Using k-symmetries, these cancel in 6 pairs.
  -- Rewrite to make cancellations manifest:
  -- Each pair cancels after applying k-symmetries.
  -- Strategy: rewrite every k-term to a canonical form, then ring.
  -- Canonical: sort the first 3 indices lexicographically.
  -- We use targeted have-lemmas to avoid rw-loops.
  have p1 : md.k e c b a d = md.k b c e a d := k_sym13 md e c b a d
  have p2 : md.k e c a b d = md.k a c e b d := k_sym13 md e c a b d
  have p3 : md.k e d b a c = md.k b d e a c := k_sym13 md e d b a c
  have p4 : md.k e d a b c = md.k a d e b c := k_sym13 md e d a b c
  have p5 : md.k a c b e d = md.k a b c e d := md.k_sym23 a c b e d
  have p6 : md.k a d b e c = md.k a b d e c := md.k_sym23 a d b e c
  have p7 : md.k b c a e d = md.k a b c e d :=
    calc md.k b c a e d = md.k c b a e d := md.k_sym12 b c a e d
    _ = md.k c a b e d := md.k_sym23 c b a e d
    _ = md.k a c b e d := md.k_sym12 c a b e d
    _ = md.k a b c e d := md.k_sym23 a c b e d
  have p8 : md.k b d a e c = md.k a b d e c :=
    calc md.k b d a e c = md.k d b a e c := md.k_sym12 b d a e c
    _ = md.k d a b e c := md.k_sym23 d b a e c
    _ = md.k a d b e c := md.k_sym12 d a b e c
    _ = md.k a b d e c := md.k_sym23 a d b e c
  linarith

/-! ### Assemble into RiemannData -/

open UnifiedTheory.LayerA.Bianchi in
/-- **Construct RiemannData from metric derivatives.**
    All fields are PROVEN, not axiomatized. -/
noncomputable def riemannFromMetric : RiemannData n where
  R := R_metric md
  antisym1 := R_antisym1 md
  antisym2 := R_antisym2 md
  dR := dR_metric md
  d_antisym1 := dR_antisym1 md
  d_antisym2 := dR_antisym2 md
  bianchi2 := bianchi2 md

open UnifiedTheory.LayerA.Bianchi in
/-- **The contracted Bianchi identity holds for metric-derived curvature.**
    Fully proven chain: metric → Riemann → Bianchi → contracted Bianchi.
    No axioms anywhere. -/
noncomputable example (md : MetricDerivs n) (b : Fin n) :
    2 * divRic (riemannFromMetric md) b =
    dScalar (riemannFromMetric md) b :=
  contracted_bianchi (riemannFromMetric md) b

end UnifiedTheory.LayerA.MetricConstruction
