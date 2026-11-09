/- Two actual resolvents of one positive Hamiltonian commute. The
residual of a separately smoothed state factors through the finer
resolvent defect. This supplies a bound without extra state regularity. -/
import UnifiedTheory.Audit.KFCausalYosidaParameterDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTwoScaleResolventResidual
noncomputable section
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation
open UnifiedTheory.Audit.KFCausalYosidaParameterDifference
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvents_commute (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (hr : Resolves T R a) (hs : Resolves T S b)
    (hlr : ∀ x : T.domain, R (T x+a • (x:H)) = x)
    (hls : ∀ x : T.domain, S (T x+b • (x:H)) = x) (f : H) :
    R (S f) = S (R f) := by
  have he := resolvent_difference_apply T R S a b hs hlr
  by_cases hab : a = b
  · have heq (x : H) : R x = S x := by
      have hx := he x
      rw [hab,sub_self,zero_smul] at hx
      exact sub_eq_zero.mp hx
    rw [heq (S f),heq f]
  · have hs' := resolvent_difference_apply T S R b a hr hls f
    have hc : (b-a) • R (S f) = (b-a) • S (R f) := by
      calc
        _ = R f-S f := (he f).symm
        _ = -(S f-R f) := by abel
        _ = -((a-b) • S (R f)) := congrArg Neg.neg hs'
        _ = _ := by rw [← neg_smul,neg_sub]
    have hz : (b-a) • (R (S f)-S (R f)) = 0 := by rw [smul_sub,hc,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hab)))

theorem yosida_intertwines (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (hs : Resolves T S b) (hlr : ∀ x : T.domain, R (T x+a • (x:H)) = x) (f : H) :
    yosida R a (b • S f) = a • R (yosida S b f) := by
  have he := yosida_on_domain T R a hlr (point T S b hs f)
  rw [point_value] at he
  change yosida R a (S f) = a • R (f-b • S f) at he
  rw [ContinuousLinearMap.map_smul_of_tower,he,yosida_apply,← smul_sub,
    ContinuousLinearMap.map_smul_of_tower,smul_comm b a]

theorem residual_factorization (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (hr : Resolves T R a) (hs : Resolves T S b)
    (hlr : ∀ x : T.domain, R (T x+a • (x:H)) = x)
    (hls : ∀ x : T.domain, S (T x+b • (x:H)) = x) (f : H) :
    yosida R a (b • S f)-yosida S b f = -yosida S b (f-a • R f) := by
  rw [yosida_intertwines T R S a b hs hlr f]
  have hc : a • R (yosida S b f) = yosida S b (a • R f) := by
    simp only [yosida_apply,map_sub,ContinuousLinearMap.map_smul_of_tower,
      resolvents_commute T R S a b hr hs hlr hls f]
  rw [hc,map_sub]
  abel

theorem residual_bound (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ) (hb : 0 < b)
    (hr : Resolves T R a) (hs : Resolves T S b)
    (hlr : ∀ x : T.domain, R (T x+a • (x:H)) = x)
    (hls : ∀ x : T.domain, S (T x+b • (x:H)) = x)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    ‖yosida R a (b • S f)-yosida S b f‖ ≤ 2*b*‖f-a • R f‖ := by
  rw [residual_factorization T R S a b hr hs hlr hls f,norm_neg]
  exact ((yosida S b).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (yosida_norm_bound T S b hb hs hp) (norm_nonneg _))

#print axioms resolvents_commute
#print axioms yosida_intertwines
#print axioms residual_factorization
#print axioms residual_bound
end
end UnifiedTheory.Audit.KFCausalTwoScaleResolventResidual
