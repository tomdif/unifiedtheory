/- The Laplace resolvent is integrated from the constructed OS evolution.
Its domain, boundedness, positivity, symmetry and injectivity are proved from
that evolution; no Hamiltonian or resolvent identity is assumed. -/
import UnifiedTheory.Clay.YangMills.OSInjectiveEvolution
import UnifiedTheory.Audit.KFCausalInverseResolventGraph
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSLaplaceResolvent
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics
open scoped NNReal Topology

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

abbrev State := Hilbert (positiveKernel W plane hp)

def integrand (x : State (hp := hp)) (t : ℝ) : State (hp := hp) :=
  Real.exp (-t) • D.operator t.toNNReal x

theorem integrand_continuous (x : State (hp := hp)) : Continuous (integrand D x) :=
  (Real.continuous_exp.comp continuous_neg).smul
    ((D.strongly_continuous x).comp continuous_real_toNNReal)

theorem integrand_norm (x : State (hp := hp)) (t : ℝ) :
    ‖integrand D x t‖ ≤ Real.exp (-t) * ‖x‖ := by
  rw [integrand, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (D.contraction _ x) (Real.exp_pos _).le

theorem integrand_integrable (x : State (hp := hp)) :
    Integrable (integrand D x) (volume.restrict (Set.Ioi 0)) :=
  ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖).mono'
    (integrand_continuous D x).aestronglyMeasurable
    (Eventually.of_forall (integrand_norm D x))

def laplaceLinear : State (hp := hp) →ₗ[ℂ] State (hp := hp) where
  toFun x := ∫ t : ℝ in Set.Ioi 0, integrand D x t
  map_add' x y := by
    simp only [integrand, map_add, smul_add]
    exact integral_add (integrand_integrable D x) (integrand_integrable D y)
  map_smul' c x := by
    simp only [integrand, map_smul, smul_comm (Real.exp _) c]
    exact integral_smul c _

theorem laplaceLinear_norm (x : State (hp := hp)) : ‖laplaceLinear D x‖ ≤ ‖x‖ := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖)
    (Eventually.of_forall (integrand_norm D x))
  simpa only [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] using h

def resolvent : State (hp := hp) →L[ℂ] State (hp := hp) :=
  (laplaceLinear D).mkContinuous 1 (fun x => by
    simpa only [one_mul] using laplaceLinear_norm D x)

@[simp] theorem resolvent_apply (x : State (hp := hp)) :
    resolvent D x = ∫ t : ℝ in Set.Ioi 0, integrand D x t := rfl

theorem resolvent_contraction (x : State (hp := hp)) : ‖resolvent D x‖ ≤ ‖x‖ :=
  laplaceLinear_norm D x

theorem resolvent_norm : ‖resolvent D‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa only [one_mul] using resolvent_contraction D x)

theorem pairing (x y : State (hp := hp)) :
    inner ℂ x (resolvent D y) = ∫ t : ℝ in Set.Ioi 0, inner ℂ x (integrand D y t) :=
  (integral_inner (integrand_integrable D y) x).symm

theorem resolvent_symmetric (x y : State (hp := hp)) :
    inner ℂ (resolvent D x) y = inner ℂ x (resolvent D y) := by
  calc
    _ = star (inner ℂ y (resolvent D x)) := (inner_conj_symm _ _).symm
    _ = ∫ t : ℝ in Set.Ioi 0, star (inner ℂ y (integrand D x t)) := by
      rw [pairing]
      exact (integral_conj).symm
    _ = ∫ t : ℝ in Set.Ioi 0, inner ℂ x (integrand D y t) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [show star (inner ℂ y (integrand D x t)) = inner ℂ (integrand D x t) y
          from inner_conj_symm _ _]
        simp only [integrand, inner_smul_left_eq_smul, inner_smul_right_eq_smul, D.symmetric])
    _ = _ := (pairing D x y).symm

theorem quadratic_integrand_nonneg (x : State (hp := hp)) (t : ℝ) :
    0 ≤ (inner ℂ x (integrand D x t)).re := by
  simp only [integrand, inner_smul_right_eq_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Real.exp_pos _).le (D.positive _ x)

theorem quadratic_pairing (x : State (hp := hp)) :
    (inner ℂ x (resolvent D x)).re =
      ∫ t : ℝ in Set.Ioi 0, (inner ℂ x (integrand D x t)).re := by
  rw [pairing]
  exact (integral_re ((integrand_integrable D x).const_inner (𝕜 := ℂ) x)).symm

theorem resolvent_positive (x : State (hp := hp)) :
    0 ≤ (inner ℂ x (resolvent D x)).re := by
  rw [quadratic_pairing]
  exact integral_nonneg (quadratic_integrand_nonneg D x)

theorem resolvent_selfAdjoint : IsSelfAdjoint (resolvent D) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (resolvent_symmetric D)

/-- Vanishing of the positive Laplace quadratic form forces a half-time
vector to vanish, and the previously constructed evolution is injective. -/
theorem resolvent_null (x : State (hp := hp)) (hx : resolvent D x = 0) : x = 0 := by
  have hi := ((integrand_integrable D x).const_inner (𝕜 := ℂ) x).re
  have hz : (∫ t : ℝ in Set.Ioi 0, (inner ℂ x (integrand D x t)).re) = 0 := by
    rw [← quadratic_pairing, hx, inner_zero_right]
    rfl
  have hae := (integral_eq_zero_iff_of_nonneg (quadratic_integrand_nonneg D x) hi).mp hz
  have hc : Continuous (fun t : ℝ => (inner ℂ x (integrand D x t)).re) :=
    Complex.continuous_re.comp (continuous_const.inner (integrand_continuous D x))
  have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
    hc.continuousOn continuous_zero.continuousOn
  have h₁ := he (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  simp only [integrand, inner_smul_right_eq_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Pi.zero_apply,
    Real.toNNReal_one] at h₁
  have hq : (inner ℂ x (D.operator 1 x)).re = 0 :=
    (mul_eq_zero.mp h₁).resolve_left (ne_of_gt (Real.exp_pos _))
  have hh : ‖D.operator (1/2) x‖ ^ 2 = 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (D.operator (1/2) x) (D.operator (1/2) x)).re = 0
    rw [D.symmetric, D.add, show (1/2 : ℝ≥0)+1/2=1 by norm_num]
    exact hq
  have hv : D.operator (1/2) x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  apply OSInjectiveEvolution.injective D (1/2)
  simpa only [map_zero] using hv

theorem resolvent_injective : Function.Injective (resolvent D) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply resolvent_null D
  rw [map_sub, hxy, sub_self]

theorem resolvent_dense : DenseRange (resolvent D) :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.symmetric_injective_dense
    (resolvent D) (resolvent_injective D) (resolvent_symmetric D)

end
end UnifiedTheory.Clay.YangMills.OSLaplaceResolvent
