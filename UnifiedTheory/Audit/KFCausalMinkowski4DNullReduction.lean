/-
  Audit/KFCausalMinkowski4DNullReduction.lean — the null change of variables
  (t,r) → (u,v), by triangular 1D substitutions

  The reduction of the 4D cone integral to the (u,v)-profile plane needs the
  measure identity

    ∫_{t<0} ∫_{0<r<−t} G(t,r) dr dt  =  ½ ∬_{0<u<v} G(−(u+v)/2, (v−u)/2) du dv

  (null coordinates `u = −t−r`, `v = −t+r`, Jacobian ½).  No two-dimensional
  change-of-variables machinery is required: the map factors into a reflection,
  a per-slice shift, and a per-slice scale — this file provides the two 1D
  substitution steps on `Ioi`, via indicator extension and the global
  translation/dilation invariance of Lebesgue measure.
-/
import Mathlib

open MeasureTheory Set

namespace UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction

/-- **The shift step**: `∫_{w>r} f(w) dw = ∫_{u>0} f(u+r) du`. -/
theorem shift_Ioi (f : ℝ → ℝ) (r : ℝ) (hf : IntegrableOn f (Ioi r)) :
    ∫ w in Ioi r, f w = ∫ u in Ioi (0:ℝ), f (u + r) := by
  have hind : Integrable ((Ioi r).indicator f) := by
    rwa [integrable_indicator_iff measurableSet_Ioi]
  have h := integral_add_right_eq_self (μ := volume) ((Ioi r).indicator f) r
  calc ∫ w in Ioi r, f w
      = ∫ x : ℝ, (Ioi r).indicator f x := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ x : ℝ, (Ioi r).indicator f (x + r) := h.symm
    _ = ∫ x : ℝ, (Ioi (0:ℝ)).indicator (fun u => f (u + r)) x := by
        congr 1
        funext x
        by_cases hx : 0 < x
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith : r < x + r)),
            Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
        · rw [Set.indicator_of_notMem
            (fun hmem => hx (by linarith [Set.mem_Ioi.mp hmem])),
            Set.indicator_of_notMem (fun hmem => hx (Set.mem_Ioi.mp hmem))]
    _ = ∫ u in Ioi (0:ℝ), f (u + r) := integral_indicator measurableSet_Ioi

/-- **The scale-shift step**: `∫_{r>0} f(r) dr = ½ ∫_{v>u} f((v−u)/2) dv`. -/
theorem scale_shift_Ioi (f : ℝ → ℝ) (u : ℝ) (hf : IntegrableOn f (Ioi (0:ℝ))) :
    ∫ r in Ioi (0:ℝ), f r = (1/2) * ∫ v in Ioi u, f ((v - u)/2) := by
  have hind : Integrable ((Ioi (0:ℝ)).indicator f) := by
    rwa [integrable_indicator_iff measurableSet_Ioi]
  have h2 := Measure.integral_comp_div ((Ioi (0:ℝ)).indicator f) 2
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun v => (Ioi (0:ℝ)).indicator f ((v - u)/2)) u
  calc ∫ r in Ioi (0:ℝ), f r
      = ∫ y : ℝ, (Ioi (0:ℝ)).indicator f y :=
        (integral_indicator measurableSet_Ioi).symm
    _ = (1/2) * ∫ x : ℝ, (Ioi (0:ℝ)).indicator f (x/2) := by
        rw [h2, smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        ring
    _ = (1/2) * ∫ v : ℝ, (Ioi (0:ℝ)).indicator f ((v - u)/2) := by
        congr 1
        rw [← hshift]
        congr 1
        funext x
        rw [show (x + u - u)/2 = x/2 from by ring]
    _ = (1/2) * ∫ v : ℝ, (Ioi u).indicator (fun v' => f ((v' - u)/2)) v := by
        congr 1
        congr 1
        funext v
        by_cases hv : u < v
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < (v - u)/2)),
            Set.indicator_of_mem (Set.mem_Ioi.mpr hv)]
        · rw [Set.indicator_of_notMem
            (fun hmem => hv (by linarith [Set.mem_Ioi.mp hmem])),
            Set.indicator_of_notMem (fun hmem => hv (by
              have := Set.mem_Ioi.mp hmem
              linarith))]
    _ = (1/2) * ∫ v in Ioi u, f ((v - u)/2) :=
        congrArg _ (integral_indicator measurableSet_Ioi)

/-- **The reflection step**: `∫_{t<0} h(t) dt = ∫_{w>0} h(−w) dw`. -/
theorem reflect_Iio (h : ℝ → ℝ) :
    ∫ t in Iio (0:ℝ), h t = ∫ w in Ioi (0:ℝ), h (-w) := by
  rw [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio]

/-- Product-box integrability: bounded, measurable, supported in a box implies
integrable on the product of the two `(0,∞)`-restrictions — the input of both
Fubini swaps. -/
theorem prod_box_integrable (F : ℝ → ℝ → ℝ) (M T R : ℝ) (hM : 0 ≤ M)
    (hT : 0 < T) (hR : 0 < R)
    (hFm : Measurable (Function.uncurry F))
    (hFb : ∀ w r, |F w r| ≤ M)
    (hsT : ∀ w r, T ≤ w → F w r = 0) (hsR : ∀ w r, R ≤ r → F w r = 0) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  rw [Measure.prod_restrict]
  have hdom : IntegrableOn ((Ioc (0:ℝ) T ×ˢ Ioc (0:ℝ) R).indicator (fun _ => M))
      (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) (volume.prod volume) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff (measurableSet_Ioc.prod measurableSet_Ioc)]
    exact integrableOn_const (hs := by
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  apply Integrable.mono' hdom hFm.aestronglyMeasurable.restrict
  apply MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  intro p hp
  by_cases hbox : p ∈ Ioc (0:ℝ) T ×ˢ Ioc (0:ℝ) R
  · rw [Set.indicator_of_mem hbox, Real.norm_eq_abs]
    exact hFb p.1 p.2
  · rw [Set.indicator_of_notMem hbox, Real.norm_eq_abs]
    have hz : F p.1 p.2 = 0 := by
      rw [Set.mem_prod] at hbox hp
      rcases not_and_or.mp hbox with h1 | h2
      · have : T < p.1 := by
          rcases not_and_or.mp (fun hmem => h1 (Set.mem_Ioc.mpr hmem)) with ha | hb
          · exact absurd hp.1 ha
          · exact lt_of_not_ge hb
        exact hsT p.1 p.2 (le_of_lt this)
      · have : R < p.2 := by
          rcases not_and_or.mp (fun hmem => h2 (Set.mem_Ioc.mpr hmem)) with ha | hb
          · exact absurd hp.2 ha
          · exact lt_of_not_ge hb
        exact hsR p.1 p.2 (le_of_lt this)
    rw [show Function.uncurry F p = F p.1 p.2 from rfl, hz, abs_zero]

#print axioms shift_Ioi
#print axioms scale_shift_Ioi
#print axioms reflect_Iio

end UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction
