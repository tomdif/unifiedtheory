/- Strong Schwartz continuity for the linear parts of genuine spacetime
transformations, proved using weighted derivative bounds near the identity. -/
import UnifiedTheory.Clay.YangMills.SchwartzTranslationContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzLinearContinuity
noncomputable section
open LocalFields PoincareKinematics PoincareTestAction PoincareTopology
open SchwartzTranslationContinuity
open scoped Topology

abbrev DerivativeSpace (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => Spacetime) ℂ

def derivativePrecomp (n : ℕ) (A : Spacetime →L[ℝ] Spacetime) :
    DerivativeSpace n →L[ℝ] DerivativeSpace n :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => A)

theorem continuous_derivativePrecomp (n : ℕ) : Continuous (derivativePrecomp n) :=
  (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => Spacetime) (fun _ : Fin n => Spacetime) ℂ).cont.comp
      (continuous_pi (fun _ => continuous_id))

@[simp] theorem derivativePrecomp_id (n : ℕ) :
    derivativePrecomp n (ContinuousLinearMap.id ℝ Spacetime) =
      ContinuousLinearMap.id ℝ (DerivativeSpace n) := by
  ext m v
  rfl

def linearOperator (g : Poincare) : Spacetime →L[ℝ] Spacetime := (linearUnit g).val

theorem continuous_linearOperator : Continuous linearOperator :=
  Units.continuous_val.comp continuous_linearUnit

@[simp] theorem linearOperator_one : linearOperator 1 = ContinuousLinearMap.id ℝ Spacetime := by
  ext x
  rfl

def linearPullback (g : Poincare) : TestFunction →L[ℂ] TestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (transform g).linear.toContinuousLinearEquiv

@[simp] theorem linearPullback_apply (g : Poincare) (f : TestFunction) (x : Spacetime) :
    linearPullback g f x = f (linearOperator g x) := rfl

@[simp] theorem linearPullback_one (f : TestFunction) : linearPullback 1 f = f := by
  ext x
  rfl

theorem iteratedFDeriv_linearPullback (g : Poincare) (f : TestFunction) (n : ℕ) (x : Spacetime) :
    iteratedFDeriv ℝ n (linearPullback g f) x =
      derivativePrecomp n (linearOperator g) (iteratedFDeriv ℝ n f (linearOperator g x)) := by
  exact (linearOperator g).iteratedFDeriv_comp_right (f.smooth n) x le_rfl

theorem norm_linear_difference (A : Spacetime →L[ℝ] Spacetime) (x : Spacetime) :
    ‖A x - x‖ ≤ ‖A - ContinuousLinearMap.id ℝ Spacetime‖ * ‖x‖ := by
  exact (A - ContinuousLinearMap.id ℝ Spacetime).le_opNorm x

def linearDerivativeBound (f : TestFunction) (k n : ℕ) : ℝ :=
  2 ^ (k + 1) * SchwartzMap.seminorm ℂ (k + 1) (n + 1) f

theorem linearDerivativeBound_nonneg (f : TestFunction) (k n : ℕ) :
    0 ≤ linearDerivativeBound f k n := by
  unfold linearDerivativeBound
  positivity

/-- The extra derivative and polynomial weight absorb the displacement A*x-x
uniformly in x. This is the crucial estimate for nontranslation transformations. -/
theorem weighted_derivative_linear_difference (f : TestFunction) (k n : ℕ)
    (A : Spacetime →L[ℝ] Spacetime)
    (hA : ‖A - ContinuousLinearMap.id ℝ Spacetime‖ ≤ 1 / 2) (x : Spacetime) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (A x) - iteratedFDeriv ℝ n f x‖ ≤
      linearDerivativeBound f k n * ‖A - ContinuousLinearMap.id ℝ Spacetime‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, sub_self, norm_zero, mul_zero]
    exact mul_nonneg (linearDerivativeBound_nonneg f k n) (norm_nonneg _)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let F := fun y : Spacetime => ‖x‖ ^ (k + 1) • iteratedFDeriv ℝ n f y
  have hf : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    (f.smooth (n + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have hF : Differentiable ℝ F := hf.const_smul (‖x‖ ^ (k + 1))
  have hbound : ∀ y ∈ Metric.closedBall x (‖x‖ / 2),
      ‖fderiv ℝ F y‖ ≤ linearDerivativeBound f k n := by
    intro y hy
    have hxy : ‖x‖ ≤ 2 * ‖y‖ := by
      have hd : ‖x - y‖ ≤ ‖x‖ / 2 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
      have hn := norm_le_norm_sub_add x y
      linarith
    change ‖fderiv ℝ ((‖x‖ ^ (k + 1)) • iteratedFDeriv ℝ n f) y‖ ≤ _
    rw [fderiv_const_smul (hf y) (‖x‖ ^ (k + 1)), norm_smul,
      Real.norm_of_nonneg (by positivity), norm_fderiv_iteratedFDeriv]
    calc
      ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤
          (2 * ‖y‖) ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) f y‖ := by gcongr
      _ = 2 ^ (k + 1) * (‖y‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by
        rw [mul_pow]
        ring
      _ ≤ linearDerivativeBound f k n :=
        mul_le_mul_of_nonneg_left (f.le_seminorm ℂ (k + 1) (n + 1) y) (by positivity)
  have hxmem : x ∈ Metric.closedBall x (‖x‖ / 2) :=
    Metric.mem_closedBall_self (by positivity)
  have hAx : A x ∈ Metric.closedBall x (‖x‖ / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖A x - x‖ ≤ ‖A - ContinuousLinearMap.id ℝ Spacetime‖ * ‖x‖ :=
        norm_linear_difference A x
      _ ≤ ‖x‖ / 2 := by nlinarith
  have hm := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hF y) hbound hxmem hAx
  have hm' : ‖x‖ ^ (k + 1) *
      ‖iteratedFDeriv ℝ n f (A x) - iteratedFDeriv ℝ n f x‖ ≤
      linearDerivativeBound f k n * ‖A x - x‖ := by
    simpa only [F, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ (k + 1))] using hm
  apply le_of_mul_le_mul_right (a := ‖x‖) _ hxp
  calc
    (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (A x) - iteratedFDeriv ℝ n f x‖) * ‖x‖ =
        ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f (A x) - iteratedFDeriv ℝ n f x‖ := by
      rw [pow_succ]
      ring
    _ ≤ linearDerivativeBound f k n * ‖A x - x‖ := hm'
    _ ≤ linearDerivativeBound f k n *
        (‖A - ContinuousLinearMap.id ℝ Spacetime‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_linear_difference A x)
        (linearDerivativeBound_nonneg f k n)
    _ = (linearDerivativeBound f k n * ‖A - ContinuousLinearMap.id ℝ Spacetime‖) * ‖x‖ := by
      ring

theorem norm_precomp_difference (n : ℕ) (A : Spacetime →L[ℝ] Spacetime)
    (m v : DerivativeSpace n) :
    ‖derivativePrecomp n A m - v‖ ≤ ‖derivativePrecomp n A‖ * ‖m - v‖ +
      ‖derivativePrecomp n A - ContinuousLinearMap.id ℝ (DerivativeSpace n)‖ * ‖v‖ := by
  have heq : derivativePrecomp n A m - v = derivativePrecomp n A (m - v) +
      (derivativePrecomp n A - ContinuousLinearMap.id ℝ (DerivativeSpace n)) v := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((derivativePrecomp n A).le_opNorm (m - v))
    ((derivativePrecomp n A - ContinuousLinearMap.id ℝ (DerivativeSpace n)).le_opNorm v))

def linearDifferenceBound (f : TestFunction) (k n : ℕ) (A : Spacetime →L[ℝ] Spacetime) : ℝ :=
  ‖derivativePrecomp n A‖ * (linearDerivativeBound f k n *
    ‖A - ContinuousLinearMap.id ℝ Spacetime‖) +
  ‖derivativePrecomp n A - ContinuousLinearMap.id ℝ (DerivativeSpace n)‖ *
    SchwartzMap.seminorm ℂ k n f

theorem linearDifferenceBound_nonneg (f : TestFunction) (k n : ℕ)
    (A : Spacetime →L[ℝ] Spacetime) : 0 ≤ linearDifferenceBound f k n A := by
  have h := linearDerivativeBound_nonneg f k n
  unfold linearDifferenceBound
  positivity

theorem seminorm_linear_difference (g : Poincare) (f : TestFunction) (k n : ℕ)
    (hg : ‖linearOperator g - ContinuousLinearMap.id ℝ Spacetime‖ ≤ 1 / 2) :
    SchwartzMap.seminorm ℂ k n (linearPullback g f - f) ≤
      linearDifferenceBound f k n (linearOperator g) := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (linearDifferenceBound_nonneg f k n _)
  intro x
  rw [iteratedFDeriv_schwartz_sub, iteratedFDeriv_linearPullback]
  calc
    _ ≤ ‖x‖ ^ k * (‖derivativePrecomp n (linearOperator g)‖ *
        ‖iteratedFDeriv ℝ n f (linearOperator g x) - iteratedFDeriv ℝ n f x‖ +
        ‖derivativePrecomp n (linearOperator g) - ContinuousLinearMap.id ℝ (DerivativeSpace n)‖ *
        ‖iteratedFDeriv ℝ n f x‖) :=
      mul_le_mul_of_nonneg_left (norm_precomp_difference n (linearOperator g) _ _) (by positivity)
    _ = ‖derivativePrecomp n (linearOperator g)‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (linearOperator g x) - iteratedFDeriv ℝ n f x‖) +
        ‖derivativePrecomp n (linearOperator g) - ContinuousLinearMap.id ℝ (DerivativeSpace n)‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
    _ ≤ linearDifferenceBound f k n (linearOperator g) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (weighted_derivative_linear_difference f k n _ hg x)
          (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (f.le_seminorm ℂ k n x) (norm_nonneg _))

theorem continuous_linearDifferenceBound (f : TestFunction) (k n : ℕ) :
    Continuous (linearDifferenceBound f k n) := by
  exact ((continuous_derivativePrecomp n).norm.mul
    (continuous_const.mul (continuous_id.sub continuous_const).norm)).add
    (((continuous_derivativePrecomp n).sub continuous_const).norm.mul continuous_const)

@[simp] theorem linearDifferenceBound_id (f : TestFunction) (k n : ℕ) :
    linearDifferenceBound f k n (ContinuousLinearMap.id ℝ Spacetime) = 0 := by
  simp [linearDifferenceBound]

theorem tendsto_linearPullback_one (f : TestFunction) :
    Filter.Tendsto (fun g : Poincare => linearPullback g f) (𝓝 1) (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ Spacetime ℂ).tendsto_nhds _ f).mpr
  rintro ⟨k, n⟩ ε hε
  have hd : Continuous (fun g : Poincare =>
      ‖linearOperator g - ContinuousLinearMap.id ℝ Spacetime‖) :=
    (continuous_linearOperator.sub continuous_const).norm
  have hdlim : Filter.Tendsto (fun g : Poincare =>
      ‖linearOperator g - ContinuousLinearMap.id ℝ Spacetime‖) (𝓝 1) (𝓝 0) := by
    simpa using hd.tendsto 1
  have hsmall : ∀ᶠ g : Poincare in 𝓝 1,
      ‖linearOperator g - ContinuousLinearMap.id ℝ Spacetime‖ ≤ 1 / 2 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hc := (continuous_linearDifferenceBound f k n).comp continuous_linearOperator
  have hlim : Filter.Tendsto (fun g : Poincare => linearDifferenceBound f k n (linearOperator g))
      (𝓝 1) (𝓝 0) := by simpa using hc.tendsto 1
  filter_upwards [hsmall, hlim.eventually (gt_mem_nhds hε)] with g hg hεg
  exact (seminorm_linear_difference g f k n hg).trans_lt hεg

end
end UnifiedTheory.Clay.YangMills.SchwartzLinearContinuity
