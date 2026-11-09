import UnifiedTheory.Audit.KFCausalConformal4DDiamondMeasure

/-! A genuine C¹ curve with future timelike velocity has future timelike
endpoint displacement. The proof uses a separating spatial functional,
three-dimensional Cauchy--Schwarz and the mean-value theorem. Straight
segments supply the converse and remain in the endpoint time slab. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMinkowski4DTimelikeCurves
noncomputable section
open Set
open scoped BigOperators ContDiff
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DDiamondAffine (future)
open KFCausalConformal4DDiamondMeasure (spatialRadius future_iff_radius)

def straight (p q : Point) (s : ℝ) : Point := p + s • (q - p)

private def spatialDot (u v : Point) : ℝ := u 1 * v 1 + u 2 * v 2 + u 3 * v 3

private def separator (d v : Point) : ℝ := spatialRadius d * v 0 - spatialDot d v

private theorem spatial_dot_le (u v : Point) :
    spatialDot u v ≤ spatialRadius u * spatialRadius v := by
  simpa [spatialDot, spatialRadius, Fin.sum_univ_three] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin 3 => u i.succ) (fun i : Fin 3 => v i.succ)

private theorem separator_positive (d v : Point) (hd : 0 < spatialRadius d)
    (hv : future v) : 0 < separator d v := by
  have h := mul_lt_mul_of_pos_left ((future_iff_radius v).mp hv) hd
  have hcs := spatial_dot_le d v
  dsimp [separator]
  linarith

private theorem coordinate_derivative (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (s : ℝ) (i : Fin 4) :
    HasDerivAt (fun t => γ t i) (deriv γ s i) s :=
  hasDerivAt_pi.mp ((hγ.differentiable (by norm_num)).differentiableAt.hasDerivAt) i

private theorem separator_derivative (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (d : Point) (s : ℝ) :
    HasDerivAt (fun t => separator d (γ t)) (separator d (deriv γ s)) s := by
  exact ((coordinate_derivative γ hγ s 0).const_mul (spatialRadius d)).sub
    ((((coordinate_derivative γ hγ s 1).const_mul (d 1)).add
      ((coordinate_derivative γ hγ s 2).const_mul (d 2))).add
        ((coordinate_derivative γ hγ s 3).const_mul (d 3)))

private theorem time_strictMono (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, future (deriv γ s)) :
    StrictMonoOn (fun s => γ s 0) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (((continuous_apply 0).comp hγ.continuous).continuousOn)
  intro s hs
  change 0 < deriv (fun t => γ t 0) s
  rw [(coordinate_derivative γ hγ s 0).deriv]
  exact (hv s (interior_subset hs)).1

theorem future_displacement (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, future (deriv γ s)) :
    future (γ 1 - γ 0) := by
  let d : Point := γ 1 - γ 0
  have ht : 0 < d 0 := by
    have h := time_strictMono γ hγ hv (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
    change 0 < γ 1 0 - γ 0 0
    linarith
  apply (future_iff_radius d).mpr
  have hR : 0 ≤ spatialRadius d := Real.sqrt_nonneg _
  by_cases hzero : spatialRadius d = 0
  · simpa only [hzero] using ht
  have hpos : 0 < spatialRadius d := lt_of_le_of_ne hR (Ne.symm hzero)
  have hm : StrictMonoOn (fun s => separator d (γ s)) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · have hc : Continuous (fun s => separator d (γ s)) := by
        have hcγ := hγ.continuous
        unfold separator spatialDot
        fun_prop
      exact hc.continuousOn
    · intro s hs
      rw [(separator_derivative γ hγ d s).deriv]
      exact separator_positive d _ hpos (hv s (interior_subset hs))
  have hstrict := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  have hdiff : separator d (γ 1) - separator d (γ 0) =
      spatialRadius d * d 0 - spatialDot d d := by
    dsimp [separator, spatialDot, d]
    ring
  have hsq : spatialRadius d ^ 2 = spatialDot d d := by
    rw [spatialRadius, Real.sq_sqrt (by positivity)]
    unfold spatialDot
    ring
  nlinarith

theorem curve_time_bounds (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, future (deriv γ s))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    γ 0 0 ≤ γ s 0 ∧ γ s 0 ≤ γ 1 0 := by
  have hm := (time_strictMono γ hγ hv).monotoneOn
  exact ⟨hm (by norm_num) hs hs.1, hm hs (by norm_num) hs.2⟩

theorem straight_smooth (p q : Point) : ContDiff ℝ 1 (straight p q) := by
  unfold straight
  fun_prop

theorem straight_derivative (p q : Point) (s : ℝ) :
    HasDerivAt (straight p q) (q - p) s := by
  change HasDerivAt (fun t => p + t • (q - p)) (q - p) s
  convert (hasDerivAt_const s p).add ((hasDerivAt_id s).smul_const (q - p)) using 1
  simp only [zero_add, one_smul]

theorem straight_endpoints (p q : Point) : straight p q 0 = p ∧ straight p q 1 = q := by
  simp [straight]

theorem straight_time_bounds (p q : Point) (hpq : p 0 ≤ q 0) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    p 0 ≤ straight p q s 0 ∧ straight p q s 0 ≤ q 0 := by
  change p 0 ≤ p 0 + s * (q 0 - p 0) ∧ p 0 + s * (q 0 - p 0) ≤ q 0
  constructor <;> nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hpq),
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hpq)]

#print axioms future_displacement
#print axioms curve_time_bounds
#print axioms straight_smooth
#print axioms straight_derivative
#print axioms straight_endpoints
#print axioms straight_time_bounds
end
end UnifiedTheory.Audit.KFCausalMinkowski4DTimelikeCurves
