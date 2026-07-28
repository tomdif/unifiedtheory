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
import UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

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
    (hFb : ∀ w r, 0 < w → 0 < r → |F w r| ≤ M)
    (hsT : ∀ w r, 0 < r → T ≤ w → F w r = 0)
    (hsR : ∀ w r, 0 < w → R ≤ r → F w r = 0) :
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
  have hp1 : (0:ℝ) < p.1 := hp.1
  have hp2 : (0:ℝ) < p.2 := hp.2
  by_cases hbox : p ∈ Ioc (0:ℝ) T ×ˢ Ioc (0:ℝ) R
  · rw [Set.indicator_of_mem hbox, Real.norm_eq_abs]
    exact hFb p.1 p.2 hp1 hp2
  · rw [Set.indicator_of_notMem hbox, Real.norm_eq_abs]
    have hz : F p.1 p.2 = 0 := by
      rw [Set.mem_prod] at hbox
      rcases not_and_or.mp hbox with h1 | h2
      · have : T < p.1 := by
          rcases not_and_or.mp (fun hmem => h1 (Set.mem_Ioc.mpr hmem)) with ha | hb
          · exact absurd hp1 ha
          · exact lt_of_not_ge hb
        exact hsT p.1 p.2 hp2 (le_of_lt this)
      · have : R < p.2 := by
          rcases not_and_or.mp (fun hmem => h2 (Set.mem_Ioc.mpr hmem)) with ha | hb
          · exact absurd hp2 ha
          · exact lt_of_not_ge hb
        exact hsR p.1 p.2 hp1 (le_of_lt this)
    rw [show Function.uncurry F p = F p.1 p.2 from rfl, hz, abs_zero]

/-- **The null change of variables**: for `G` bounded, measurable, supported in
`{−T ≤ t, r ≤ R}`,

    ∫_{t<0} ∫_{0<r<−t} G(t,r) dr dt = ½ ∫_{u>0} ∫_{v>u} G(−(u+v)/2, (v−u)/2) dv du

— the cone integral in `(t,r)` equals the null-coordinate integral over the
wedge `0 < u < v`, Jacobian `½`.  Triangular route: reflection, triangle
Fubini, per-slice shift, rectangular Fubini, per-slice scale. -/
theorem null_reduction (G : ℝ → ℝ → ℝ) (M T R : ℝ) (hM : 0 ≤ M)
    (hT : 0 < T) (hR : 0 < R)
    (hGm : Measurable (Function.uncurry G))
    (hGb : ∀ t r, |G t r| ≤ M)
    (hsT : ∀ t r, t ≤ -T → G t r = 0) (hsR : ∀ t r, R ≤ r → G t r = 0) :
    ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), G t r
      = (1/2) * ∫ u in Ioi (0:ℝ), ∫ v in Ioi u, G (-(u+v)/2) ((v-u)/2) := by
  -- the reflected integrand
  set F : ℝ → ℝ → ℝ := fun w r => G (-w) r with hFdef
  have hFm : Measurable (Function.uncurry F) :=
    hGm.comp ((measurable_fst.neg).prodMk measurable_snd)
  have hFb : ∀ w r, |F w r| ≤ M := fun w r => hGb (-w) r
  have hFsT : ∀ w r, T ≤ w → F w r = 0 := fun w r hw => hsT (-w) r (by linarith)
  have hFsR : ∀ w r, R ≤ r → F w r = 0 := fun w r hr => hsR (-w) r hr
  -- slice measurability/integrability helpers
  have hslicew : ∀ r : ℝ, IntegrableOn (fun w => F w r) (Ioi (0:ℝ)) :=
    fun r => integrableOn_Ioi_of_bounded_support (fun w => F w r) M T hT
      ((hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (fun w _ => hFb w r) (fun w hw => hFsT w r hw)
  have hslicer : ∀ u : ℝ, IntegrableOn (fun r => F (u+r) r) (Ioi (0:ℝ)) :=
    fun u => integrableOn_Ioi_of_bounded_support (fun r => F (u+r) r) M R hR
      ((hFm.comp ((measurable_const.add measurable_id).prodMk
        measurable_id)).aestronglyMeasurable)
      (fun r _ => hFb (u+r) r) (fun r hr => hFsR (u+r) r hr)
  -- the region indicator H w r = 1_{r<w}·F w r
  set H : ℝ → ℝ → ℝ := fun w r => ({p : ℝ × ℝ | p.2 < p.1}.indicator
    (Function.uncurry F)) (w, r) with hHdef
  have hHm : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = ({p : ℝ × ℝ | p.2 < p.1}.indicator
        (Function.uncurry F)) := by
      funext p
      rfl
    rw [this]
    exact hFm.indicator (measurableSet_lt measurable_snd measurable_fst)
  have hHb : ∀ w r, 0 < w → 0 < r → |H w r| ≤ M := by
    intro w r _ _
    simp only [hHdef]
    by_cases hmem : ((w, r) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 < p.1}
    · rw [Set.indicator_of_mem hmem]
      exact hFb w r
    · rw [Set.indicator_of_notMem hmem, abs_zero]
      exact hM
  have hHsT : ∀ w r, 0 < r → T ≤ w → H w r = 0 := by
    intro w r _ hw
    simp only [hHdef]
    by_cases hmem : ((w, r) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 < p.1}
    · rw [Set.indicator_of_mem hmem]
      exact hFsT w r hw
    · exact Set.indicator_of_notMem hmem _
  have hHsR : ∀ w r, 0 < w → R ≤ r → H w r = 0 := by
    intro w r _ hr
    simp only [hHdef]
    by_cases hmem : ((w, r) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 < p.1}
    · rw [Set.indicator_of_mem hmem]
      exact hFsR w r hr
    · exact Set.indicator_of_notMem hmem _
  -- E1: reflection
  have E1 : (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), G t r)
      = ∫ w in Ioi (0:ℝ), ∫ r in Ioo (0:ℝ) w, F w r := by
    rw [reflect_Iio (fun t => ∫ r in Ioo (0:ℝ) (-t), G t r)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w _
    dsimp only
    rw [neg_neg]
  -- E2: triangle Fubini
  have E2 : (∫ w in Ioi (0:ℝ), ∫ r in Ioo (0:ℝ) w, F w r)
      = ∫ r in Ioi (0:ℝ), ∫ w in Ioi r, F w r := by
    have h2a : ∀ w : ℝ, (∫ r in Ioo (0:ℝ) w, F w r)
        = ∫ r in Ioi (0:ℝ), H w r := by
      intro w
      rw [show (fun r => H w r) = (Iio w).indicator (fun r => F w r) from by
        funext r
        simp only [hHdef, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio,
          Function.uncurry]]
      rw [integral_indicator measurableSet_Iio,
        Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
    have h2b : ∀ r : ℝ, 0 < r → (∫ w in Ioi r, F w r)
        = ∫ w in Ioi (0:ℝ), H w r := by
      intro r hr
      rw [show (fun w => H w r) = (Ioi r).indicator (fun w => F w r) from by
        funext w
        simp only [hHdef, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioi,
          Function.uncurry]]
      rw [integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi,
        Set.inter_eq_self_of_subset_left
          (fun x hx => Set.mem_Ioi.mpr (lt_trans hr (Set.mem_Ioi.mp hx)))]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => h2a w),
      integral_integral_swap (prod_box_integrable H M T R hM hT hR hHm hHb hHsT hHsR),
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => (h2b r hr).symm)]
  -- E3: per-r shift
  have E3 : (∫ r in Ioi (0:ℝ), ∫ w in Ioi r, F w r)
      = ∫ r in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), F (u+r) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    exact shift_Ioi (fun w => F w r) r
      ((hslicew r).mono_set
        (fun x hx => Set.mem_Ioi.mpr (lt_trans (Set.mem_Ioi.mp hr) hx)))
  -- E4: rectangular Fubini
  have E4 : (∫ r in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), F (u+r) r)
      = ∫ u in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), F (u+r) r := by
    have hK : Measurable (Function.uncurry (fun r u => F (u+r) r)) :=
      hFm.comp ((measurable_snd.add measurable_fst).prodMk measurable_fst)
    exact integral_integral_swap (prod_box_integrable (fun r u => F (u+r) r)
      M R T hM hR hT hK
      (fun r u _ _ => hFb (u+r) r)
      (fun r u _ hrR => hFsR (u+r) r hrR)
      (fun r u hr huT => hFsT (u+r) r (by linarith)))
  -- E5: per-u scale
  have E5 : (∫ u in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), F (u+r) r)
      = ∫ u in Ioi (0:ℝ), (1/2) * ∫ v in Ioi u, G (-(u+v)/2) ((v-u)/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [scale_shift_Ioi (fun r => F (u+r) r) u (hslicer u)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    dsimp only
    rw [hFdef]
    dsimp only
    rw [show -(u + (v-u)/2) = -(u+v)/2 from by ring]
  rw [E1, E2, E3, E4, E5, integral_const_mul]

#print axioms null_reduction

#print axioms shift_Ioi
#print axioms scale_shift_Ioi
#print axioms reflect_Iio

end UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction
