/-
  LayerA/LinearizedFieldEqs.lean — Linearity of curvature in metric derivatives

  Proves that R_metric, dR_metric, divRic, and dScalar are all LINEAR
  in the metric derivative data (h, k). This means:

  1. R_metric(md₁ + md₂) = R_metric(md₁) + R_metric(md₂)
  2. R_metric(-md) = -R_metric(md)
  3. All contracted quantities (divRic, dScalar) inherit linearity

  Combined with the Bianchi identity (which is an unconditional identity,
  not a field equation), this gives:

  - div(G)[md₁ + md₂] = 0 unconditionally (no hypotheses on md₁, md₂)
  - div(G)[-md] = 0 unconditionally

  Note: the Bianchi identity div(G) = 0 holds for ALL MetricDerivs.
  The hypotheses in einstein_preserved_add are unnecessary — see
  ExactRegime.lean for the stronger unconditional versions.

  The linearity results here remain useful for understanding WHY
  the chain is exact: curvature is linear in the derivative data,
  and the Bianchi identity is algebraic, so everything composes.
-/
import UnifiedTheory.LayerA.MetricToRiemann
import UnifiedTheory.LayerA.BianchiIdentity

namespace UnifiedTheory.LayerA.LinearizedFieldEqs

open MetricConstruction Bianchi

/-! ## Combining metric derivative data

    We define pointwise addition and negation of MetricDerivs.
    The symmetry conditions (h_metric, h_comm, k_metric, k_sym12, k_sym23)
    are preserved by addition and negation because they are equalities
    between values at the same arguments. -/

/-- Pointwise addition of metric derivative data. -/
def mdAdd {n : ℕ} (md₁ md₂ : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => md₁.h e f a b + md₂.h e f a b
  h_metric := fun e f a b => by simp [md₁.h_metric, md₂.h_metric]
  h_comm := fun e f a b => by simp [md₁.h_comm, md₂.h_comm]
  k := fun e f g a b => md₁.k e f g a b + md₂.k e f g a b
  k_metric := fun e f g a b => by simp [md₁.k_metric, md₂.k_metric]
  k_sym12 := fun e f g a b => by simp [md₁.k_sym12, md₂.k_sym12]
  k_sym23 := fun e f g a b => by simp [md₁.k_sym23, md₂.k_sym23]

/-- Pointwise negation of metric derivative data. -/
def mdNeg {n : ℕ} (md : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => -(md.h e f a b)
  h_metric := fun e f a b => by simp [md.h_metric]
  h_comm := fun e f a b => by simp [md.h_comm]
  k := fun e f g a b => -(md.k e f g a b)
  k_metric := fun e f g a b => by simp [md.k_metric]
  k_sym12 := fun e f g a b => by simp [md.k_sym12]
  k_sym23 := fun e f g a b => by simp [md.k_sym23]

variable {n : ℕ}

/-! ## Linearity of the Riemann tensor -/

/-- **R_metric is additive**: R(md₁ + md₂) = R(md₁) + R(md₂). -/
theorem R_metric_add (md₁ md₂ : MetricDerivs n) (a b c d : Fin n) :
    R_metric (mdAdd md₁ md₂) a b c d =
    R_metric md₁ a b c d + R_metric md₂ a b c d := by
  simp only [R_metric, mdAdd]
  ring

/-- **R_metric respects negation**: R(-md) = -R(md). -/
theorem R_metric_neg (md : MetricDerivs n) (a b c d : Fin n) :
    R_metric (mdNeg md) a b c d = -(R_metric md a b c d) := by
  simp only [R_metric, mdNeg]
  ring

/-- **dR_metric is additive**: dR(md₁ + md₂) = dR(md₁) + dR(md₂). -/
theorem dR_metric_add (md₁ md₂ : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (mdAdd md₁ md₂) e a b c d =
    dR_metric md₁ e a b c d + dR_metric md₂ e a b c d := by
  simp only [dR_metric, mdAdd]
  ring

/-- **dR_metric respects negation**: dR(-md) = -dR(md). -/
theorem dR_metric_neg (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (mdNeg md) e a b c d = -(dR_metric md e a b c d) := by
  simp only [dR_metric, mdNeg]
  ring

/-! ## Linearity of contracted quantities

    divRic and dScalar are sums of R/dR values, so they inherit linearity. -/

/-- **dRic is additive.** -/
theorem dRic_add (md₁ md₂ : MetricDerivs n) (e b d : Fin n) :
    dRic (riemannFromMetric (mdAdd md₁ md₂)) e b d =
    dRic (riemannFromMetric md₁) e b d + dRic (riemannFromMetric md₂) e b d := by
  simp only [dRic, riemannFromMetric]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact dR_metric_add md₁ md₂ e a b a d

/-- **divRic is additive.** -/
theorem divRic_add (md₁ md₂ : MetricDerivs n) (b : Fin n) :
    divRic (riemannFromMetric (mdAdd md₁ md₂)) b =
    divRic (riemannFromMetric md₁) b + divRic (riemannFromMetric md₂) b := by
  simp only [divRic]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact dRic_add md₁ md₂ e b e

/-- **dScalar is additive.** -/
theorem dScalar_add (md₁ md₂ : MetricDerivs n) (b : Fin n) :
    dScalar (riemannFromMetric (mdAdd md₁ md₂)) b =
    dScalar (riemannFromMetric md₁) b + dScalar (riemannFromMetric md₂) b := by
  simp only [dScalar]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact dRic_add md₁ md₂ b a a

/-- **dRic respects negation.** -/
theorem dRic_neg (md : MetricDerivs n) (e b d : Fin n) :
    dRic (riemannFromMetric (mdNeg md)) e b d =
    -(dRic (riemannFromMetric md) e b d) := by
  simp only [dRic, riemannFromMetric, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact dR_metric_neg md e a b a d

/-- **divRic respects negation.** -/
theorem divRic_neg (md : MetricDerivs n) (b : Fin n) :
    divRic (riemannFromMetric (mdNeg md)) b =
    -(divRic (riemannFromMetric md) b) := by
  simp only [divRic, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact dRic_neg md e b e

/-- **dScalar respects negation.** -/
theorem dScalar_neg (md : MetricDerivs n) (b : Fin n) :
    dScalar (riemannFromMetric (mdNeg md)) b =
    -(dScalar (riemannFromMetric md) b) := by
  simp only [dScalar, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact dRic_neg md b a a

/-! ## The Einstein condition is linear -/

/-- **The Einstein condition is preserved under addition.**

    If md₁ satisfies div(G) = 0 and md₂ satisfies div(G) = 0,
    then md₁ + md₂ satisfies div(G) = 0.

    This is NOT a modeling choice — it is a theorem about
    the linearized field equations being linear. -/
theorem einstein_preserved_add (md₁ md₂ : MetricDerivs n)
    (h₁ : ∀ b, divRic (riemannFromMetric md₁) b -
                dScalar (riemannFromMetric md₁) b / 2 = 0)
    (h₂ : ∀ b, divRic (riemannFromMetric md₂) b -
                dScalar (riemannFromMetric md₂) b / 2 = 0) :
    ∀ b, divRic (riemannFromMetric (mdAdd md₁ md₂)) b -
         dScalar (riemannFromMetric (mdAdd md₁ md₂)) b / 2 = 0 := by
  intro b
  rw [divRic_add, dScalar_add]
  linarith [h₁ b, h₂ b]

/-- **The Einstein condition is preserved under negation.**

    If md satisfies div(G) = 0, then -md satisfies div(G) = 0.

    This is NOT a modeling choice — it is a theorem about
    the linearized field equations being linear. -/
theorem einstein_preserved_neg (md : MetricDerivs n)
    (h : ∀ b, divRic (riemannFromMetric md) b -
              dScalar (riemannFromMetric md) b / 2 = 0) :
    ∀ b, divRic (riemannFromMetric (mdNeg md)) b -
         dScalar (riemannFromMetric (mdNeg md)) b / 2 = 0 := by
  intro b
  rw [divRic_neg, dScalar_neg]
  linarith [h b]

/-! ## The derivation theorem -/

/-- **COMPOSITION AND CONJUGATION ARE FORCED BY LINEARITY.**

    The linearized Einstein equations are linear in the metric
    derivative data. Therefore:

    (1) The solution space is closed under addition:
        if h₁ and h₂ satisfy div(G) = 0, so does h₁ + h₂.

    (2) The solution space is closed under negation:
        if h satisfies div(G) = 0, so does -h.

    This means: composition = addition and conjugation = negation
    are not modeling choices. They are theorems about the structure
    of the field equations. Any perturbation that satisfies the
    linearized equations can be composed by addition and conjugated
    by negation, and the result still satisfies the equations.

    The only genuine assumption is: we work in the linearized regime
    (perturbations small enough that the linear approximation applies).
    Within that regime, + and - are forced. -/
theorem composition_forced_by_linearity :
    -- (1) Addition preserves the Einstein condition
    (∀ md₁ md₂ : MetricDerivs n,
      (∀ b, divRic (riemannFromMetric md₁) b -
            dScalar (riemannFromMetric md₁) b / 2 = 0) →
      (∀ b, divRic (riemannFromMetric md₂) b -
            dScalar (riemannFromMetric md₂) b / 2 = 0) →
      (∀ b, divRic (riemannFromMetric (mdAdd md₁ md₂)) b -
            dScalar (riemannFromMetric (mdAdd md₁ md₂)) b / 2 = 0))
    -- (2) Negation preserves the Einstein condition
    ∧ (∀ md : MetricDerivs n,
      (∀ b, divRic (riemannFromMetric md) b -
            dScalar (riemannFromMetric md) b / 2 = 0) →
      (∀ b, divRic (riemannFromMetric (mdNeg md)) b -
            dScalar (riemannFromMetric (mdNeg md)) b / 2 = 0)) :=
  ⟨einstein_preserved_add, einstein_preserved_neg⟩

end UnifiedTheory.LayerA.LinearizedFieldEqs
