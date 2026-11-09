/- Diagonal inverse-metric weights are retained in both Bianchi contractions.
The metric-jet specialization derives the identity from commuting partials,
and its Lorentzian traces agree with the computed conformal connection.
These are pointwise jet identities, not an Einstein field equation or a
global manifold/variational theorem. Actual covariant curvature derivatives
of an arbitrary metric are not constructed by this module. -/
import UnifiedTheory.LayerA.VariationalEinstein
import UnifiedTheory.Audit.KFCausalConformal4DConnection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalLorentzianContractedBianchi
noncomputable section
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs riemannFromMetric R_metric)

variable {n : ℕ}

def dRic (rd : RiemannData n) (w : Fin n → ℝ) (e b d : Fin n) : ℝ :=
  ∑ a, w a * rd.dR e a b a d

def divRic (rd : RiemannData n) (w : Fin n → ℝ) (b : Fin n) : ℝ :=
  ∑ e, w e * dRic rd w e b e

def dScalar (rd : RiemannData n) (w : Fin n → ℝ) (e : Fin n) : ℝ :=
  ∑ b, w b * dRic rd w e b b

def dEinstein (rd : RiemannData n) (w : Fin n → ℝ) (e b d : Fin n) : ℝ :=
  dRic rd w e b d - dScalar rd w e / 2 * if b = d then w b else 0

theorem once_contracted (rd : RiemannData n) (w : Fin n → ℝ) (a b d : Fin n) :
    (∑ c, w c * rd.dR c a b c d) - dRic rd w a b d + dRic rd w b a d = 0 := by
  have hs : (∑ c, w c *
      (rd.dR c a b c d + rd.dR a b c c d + rd.dR b c a c d)) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [rd.bianchi2, mul_zero]
  simp only [mul_add, Finset.sum_add_distrib] at hs
  have h2 : (∑ c, w c * rd.dR a b c c d) = -dRic rd w a b d := by
    rw [dRic, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [rd.d_antisym1 a b c c d]
    ring
  rw [h2] at hs
  change (∑ c, w c * rd.dR c a b c d) + -dRic rd w a b d + dRic rd w b a d = 0 at hs
  linarith

private theorem first_contraction (rd : RiemannData n) (w : Fin n → ℝ) (b : Fin n) :
    (∑ a, w a * ∑ c, w c * rd.dR c a b c a) = -divRic rd w b := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [divRic, dRic, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [rd.d_antisym2 c a b c a]
  ring

theorem contracted_bianchi (rd : RiemannData n) (w : Fin n → ℝ) (b : Fin n) :
    2 * divRic rd w b = dScalar rd w b := by
  have hs : (∑ a, w a * ((∑ c, w c * rd.dR c a b c a) -
      dRic rd w a b a + dRic rd w b a a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [once_contracted, mul_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  rw [first_contraction] at hs
  change -divRic rd w b - divRic rd w b + dScalar rd w b = 0 at hs
  linarith

theorem signed_einstein_divergence (rd : RiemannData n) (w : Fin n → ℝ)
    (hw : ∀ i, w i * w i = 1) (b : Fin n) :
    (∑ e, w e * dEinstein rd w e b e) = 0 := by
  have ht : (∑ e, w e * (dScalar rd w e / 2 * if b = e then w b else 0)) =
      dScalar rd w b / 2 := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    calc w b * (dScalar rd w b / 2 * w b) = (w b * w b) * (dScalar rd w b / 2) := by ring
      _ = _ := by rw [hw, one_mul]
  simp only [dEinstein, mul_sub, Finset.sum_sub_distrib]
  rw [ht]
  change divRic rd w b - dScalar rd w b / 2 = 0
  have h := contracted_bianchi rd w b
  linarith

def ricci (md : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ∑ a, w a * R_metric md a b a d

def scalar (md : MetricDerivs n) (w : Fin n → ℝ) : ℝ :=
  ∑ b, w b * ricci md w b b

def einstein (md : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ricci md w b d - scalar md w / 2 * if b = d then w b else 0

theorem ricci_symmetric (md : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    ricci md w b d = ricci md w d b := by
  apply Finset.sum_congr rfl
  intro a _
  rw [UnifiedTheory.LayerA.VariationalEinstein.R_metric_pair_symm md a b a d]

private theorem metric_dR_pair (md : MetricDerivs n) (e a b c d : Fin n) :
    UnifiedTheory.LayerA.MetricConstruction.dR_metric md e a b c d =
      UnifiedTheory.LayerA.MetricConstruction.dR_metric md e c d a b := by
  simp only [UnifiedTheory.LayerA.MetricConstruction.dR_metric]
  have h1 : md.k e c b a d = md.k e b c d a := by rw [md.k_sym23, md.k_metric]
  have h2 : md.k e c a b d = md.k e a c d b := by rw [md.k_sym23, md.k_metric]
  have h3 : md.k e d b a c = md.k e b d c a := by rw [md.k_sym23, md.k_metric]
  have h4 : md.k e d a b c = md.k e a d c b := by rw [md.k_sym23, md.k_metric]
  linarith

theorem metric_dRic_symmetric (md : MetricDerivs n) (w : Fin n → ℝ)
    (e b d : Fin n) :
    dRic (riemannFromMetric md) w e b d = dRic (riemannFromMetric md) w e d b := by
  apply Finset.sum_congr rfl
  intro a _
  change w a * UnifiedTheory.LayerA.MetricConstruction.dR_metric md e a b a d =
    w a * UnifiedTheory.LayerA.MetricConstruction.dR_metric md e a d a b
  rw [metric_dR_pair md e a b a d]

private theorem metric_dEinstein_symmetric (md : MetricDerivs n) (w : Fin n → ℝ)
    (e b d : Fin n) :
    dEinstein (riemannFromMetric md) w e b d =
      dEinstein (riemannFromMetric md) w e d b := by
  simp only [dEinstein, metric_dRic_symmetric md w e b d]
  by_cases h : b = d
  · subst d; rfl
  · simp only [if_neg h, if_neg (Ne.symm h)]

theorem metric_signed_divergence (md : MetricDerivs n) (w : Fin n → ℝ)
    (hw : ∀ i, w i * w i = 1) (b : Fin n) :
    (∑ e, w e * dEinstein (riemannFromMetric md) w e b e) = 0 :=
  signed_einstein_divergence (riemannFromMetric md) w hw b

open KFCausalConformal4DDiamondBenchmark (sign derivativeData)

theorem lorentzian_metric_divergence (md : MetricDerivs 4) (b : Fin 4) :
    (∑ e, sign e * dEinstein (riemannFromMetric md) sign e b e) = 0 := by
  apply metric_signed_divergence
  intro i
  simp only [sign]
  split_ifs <;> norm_num

theorem lorentzian_metric_first_divergence (md : MetricDerivs 4) (b : Fin 4) :
    (∑ e, sign e * dEinstein (riemannFromMetric md) sign e e b) = 0 := by
  have he : (∑ e, sign e * dEinstein (riemannFromMetric md) sign e e b) =
      ∑ e, sign e * dEinstein (riemannFromMetric md) sign e b e := by
    apply Finset.sum_congr rfl
    intro e _
    rw [metric_dEinstein_symmetric md sign e e b]
  rw [he]
  exact lorentzian_metric_divergence md b

theorem conformal_ricci (att spatial : ℝ) (b d : Fin 4) :
    ricci (derivativeData att spatial) sign b d =
      KFCausalConformal4DDiamondBenchmark.ricci att spatial b d := rfl

theorem conformal_scalar (att spatial : ℝ) :
    scalar (derivativeData att spatial) sign =
      KFCausalConformal4DDiamondBenchmark.scalar att spatial := rfl

theorem conformal_einstein_time (att spatial : ℝ) :
    einstein (derivativeData att spatial) sign 0 0 = -6 * spatial := by
  rw [einstein, conformal_ricci, conformal_scalar,
    KFCausalConformal4DDiamondBenchmark.ricci_time,
    KFCausalConformal4DDiamondBenchmark.scalar_curvature]
  norm_num [sign]
  ring

theorem conformal_einstein_spatial (att spatial : ℝ) (i : Fin 4) (hi : i ≠ 0) :
    einstein (derivativeData att spatial) sign i i = -2 * att + 4 * spatial := by
  rw [einstein, conformal_ricci, conformal_scalar,
    KFCausalConformal4DDiamondBenchmark.ricci_spatial att spatial i hi,
    KFCausalConformal4DDiamondBenchmark.scalar_curvature]
  simp only [ite_true, sign, if_neg hi]
  ring

#print axioms once_contracted
#print axioms contracted_bianchi
#print axioms signed_einstein_divergence
#print axioms ricci_symmetric
#print axioms metric_dRic_symmetric
#print axioms metric_signed_divergence
#print axioms lorentzian_metric_divergence
#print axioms lorentzian_metric_first_divergence
#print axioms conformal_ricci
#print axioms conformal_scalar
#print axioms conformal_einstein_time
#print axioms conformal_einstein_spatial
end
end UnifiedTheory.Audit.KFCausalLorentzianContractedBianchi
