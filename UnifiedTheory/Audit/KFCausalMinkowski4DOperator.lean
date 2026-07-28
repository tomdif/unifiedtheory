/-
  Audit/KFCausalMinkowski4DOperator.lean — THE REDUCED 4D OPERATOR THEOREM

  The monolith on the (t,r)-cone: for the spherically-reduced field `M̄` (even
  in `r`) with the profile hypothesis stack,

    √a·( 16a·∫_{t<0}∫_{0<r<−t} r²·f4D(a(t²−r²)²)·M̄(t,r) dr dt − (1/6)·M̄(0,0) )
        ⟶  (√π/24)(F_uu+F_vv)(0,0) − (√π/6)·F_uv(0,0)      (a → ∞),

  where `F(u,v) = M̄(−(u+v)/2, (v−u)/2)` is the null-coordinate profile.  The
  factor 16a = 4 (wedge→quadrant and weight (v−u)² = 4r²) × 4a; through the jet
  dictionary and `bdg_4d_normalization` the limit is `□φ` with coefficient 1.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DProfileTheorem

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction
open UnifiedTheory.Audit.KFCausalMinkowski4DProfileTheorem

namespace UnifiedTheory.Audit.KFCausalMinkowski4DOperator

/-- `cone_to_quadrant` without the causal-vanishing hypothesis: truncate. -/
theorem cone_to_quadrant' (H : ℝ → ℝ → ℝ) (M T : ℝ) (hM : 0 ≤ M) (hT : 0 < T)
    (hHm : Measurable (Function.uncurry H)) (hsym : ∀ u v, H u v = H v u)
    (hHb : ∀ u v, |H u v| ≤ M)
    (hsuppU : ∀ u v, T ≤ u → H u v = 0) :
    (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), H (-t-r) (-t+r))
      = (1/4) * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ), H u v := by
  set H' : ℝ → ℝ → ℝ := fun u v =>
    ({p : ℝ × ℝ | 0 < p.1 + p.2}.indicator (Function.uncurry H)) (u, v) with hH'def
  have hH'H : ∀ u v, 0 < u + v → H' u v = H u v := by
    intro u v huv
    simp only [hH'def]
    rw [Set.indicator_of_mem (show ((u, v) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | 0 < p.1 + p.2} from huv)]
    rfl
  have hH'z : ∀ u v, u + v ≤ 0 → H' u v = 0 := by
    intro u v huv
    simp only [hH'def]
    exact Set.indicator_of_notMem (show ((u, v) : ℝ × ℝ) ∉
      {p : ℝ × ℝ | 0 < p.1 + p.2} from fun hmem =>
        absurd hmem (not_lt.mpr huv)) _
  have hH'm : Measurable (Function.uncurry H') := by
    have : Function.uncurry H' = ({p : ℝ × ℝ | 0 < p.1 + p.2}.indicator
        (Function.uncurry H)) := by
      funext p
      rfl
    rw [this]
    exact hHm.indicator (measurableSet_lt measurable_const
      (measurable_fst.add measurable_snd))
  have hH'sym : ∀ u v, H' u v = H' v u := by
    intro u v
    rcases le_or_gt (u + v) 0 with h | h
    · rw [hH'z u v h, hH'z v u (by linarith)]
    · rw [hH'H u v h, hH'H v u (by linarith), hsym]
  have hH'b : ∀ u v, |H' u v| ≤ M := by
    intro u v
    rcases le_or_gt (u + v) 0 with h | h
    · rw [hH'z u v h, abs_zero]
      exact hM
    · rw [hH'H u v h]
      exact hHb u v
  have hH'sU : ∀ u v, T ≤ u → H' u v = 0 := by
    intro u v hu
    rcases le_or_gt (u + v) 0 with h | h
    · exact hH'z u v h
    · rw [hH'H u v h]
      exact hsuppU u v hu
  have hcq := cone_to_quadrant H' M T hM hT hH'm hH'sym hH'b hH'sU hH'z
  have hL : (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), H' (-t-r) (-t+r))
      = ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), H (-t-r) (-t+r) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro t ht
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    exact hH'H _ _ (by
      have h1 := Set.mem_Iio.mp ht
      linarith)
  have hR : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ), H' u v)
      = ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ), H u v := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact hH'H _ _ (by
      have h1 := Set.mem_Ioi.mp hu
      have h2 := Set.mem_Ioi.mp hv
      linarith)
  rw [← hL, hcq, hR]

/-- **THE REDUCED 4D OPERATOR THEOREM** — the monolith on the (t,r)-cone. -/
theorem bdg_4d_operator_reduced (A B CF CFu Mv Mu3 Mv3 Ccone : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (Mbar : ℝ → ℝ → ℝ) (F Fu Fuv Fuvu Fuvv : ℝ → ℝ → ℝ) (Fuu Fvv : ℝ → ℝ)
    (hFdef : ∀ u v, F u v = Mbar (-(u+v)/2) ((v-u)/2))
    (heven : ∀ t r, Mbar t (-r) = Mbar t r)
    (hFC : Continuous (Function.uncurry F))
    (hFuc : Continuous (Function.uncurry Fu))
    (hFuvc : Continuous (Function.uncurry Fuv))
    (hFd : ∀ v u, HasDerivAt (fun u' => F u' v) (Fu u v) u)
    (hFud : ∀ u v, HasDerivAt (fun v' => Fu u v') (Fuv u v) v)
    (hFuvdu : ∀ v u, HasDerivAt (fun u' => Fuv u' v) (Fuvu u v) u)
    (hFuvdv : ∀ u v, HasDerivAt (fun v' => Fuv u v') (Fuvv u v) v)
    (hCF : ∀ u v, |F u v| ≤ CF) (hCFu : ∀ u v, |Fu u v| ≤ CFu)
    (hMv : ∀ u v, |Fuv u v| ≤ Mv)
    (hMu3 : ∀ u v, |Fuvu u v| ≤ Mu3) (hMv3 : ∀ u v, |Fuvv u v| ≤ Mv3)
    (hCcone : ∀ (a : ℝ), 0 < a → ∀ u v,
      |a*(v-u)^2 * f4D (a*u^2*v^2) * F u v| ≤ Ccone * a)
    (hsUF : ∀ u v, A ≤ u → F u v = 0) (hsVF : ∀ u v, B ≤ v → F u v = 0)
    (hsUFu : ∀ u v, A ≤ u → Fu u v = 0) (hsVFu : ∀ u v, B ≤ v → Fu u v = 0)
    (hsUFuv : ∀ u v, A ≤ u → Fuv u v = 0) (hsVFuv : ∀ u v, B ≤ v → Fuv u v = 0)
    (hFvvd : ∀ u, HasDerivAt Fvv (Fuvv u 0) u)
    (hFuud : ∀ v, HasDerivAt Fuu (Fuvu 0 v) v)
    (hpdvc : Continuous (fun u => Fuvv u 0))
    (hpduc : Continuous (fun v => Fuvu 0 v))
    (hFvvs : ∀ u, A ≤ u → Fvv u = 0) (hFuus : ∀ v, B ≤ v → Fuu v = 0) :
    Tendsto (fun a : ℝ => Real.sqrt a *
        ((16 * a * ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
            r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r) - (1/6) * F 0 0))
      atTop (𝓝 (Real.sqrt π/24 * (Fuu 0 + Fvv 0) - Real.sqrt π/6 * Fuv 0 0)) := by
  apply Filter.Tendsto.congr' _
    (bdg_4d_profile A B CF CFu Mv Mu3 Mv3 Ccone hA hB F Fu Fuv Fuvu Fuvv Fuu Fvv
      hFC hFuc hFuvc hFd hFud hFuvdu hFuvdv hCF hCFu hMv hMu3 hMv3 hCcone
      hsUF hsVF hsUFu hsVFu hsUFuv hsVFuv hFvvd hFuud hpdvc hpduc hFvvs hFuus)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  -- the quadrant integrand, symmetrized
  have hHm : Measurable (Function.uncurry (fun u v =>
      a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        a*(p.2-p.1)^2 * f4D (a*p.1^2*p.2^2)) := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
      fun_prop
    exact (hc.mul hFC).measurable
  have hFsym : ∀ u v, F u v = F v u := by
    intro u v
    rw [hFdef, hFdef, show -(v+u)/2 = -(u+v)/2 from by ring,
      show (u-v)/2 = -((v-u)/2) from by ring, heven]
  have hHsym : ∀ u v, a*(v-u)^2 * f4D (a*u^2*v^2) * F u v
      = a*(u-v)^2 * f4D (a*v^2*u^2) * F v u := by
    intro u v
    rw [← hFsym, show a*(u-v)^2 = a*(v-u)^2 from by ring,
      show a*v^2*u^2 = a*u^2*v^2 from by ring]
  have hCa0 : (0:ℝ) ≤ Ccone * a := le_trans (abs_nonneg _) (hCcone a ha 0 0)
  have hcq := cone_to_quadrant' (fun u v => a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
    (Ccone * a) A hCa0 hA hHm hHsym (hCcone a ha)
    (fun u v hu => by dsimp only; rw [hsUF u v hu, mul_zero])
  -- the cone integrand matches through the null substitution
  have hcone : (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
      (fun u v => a*(v-u)^2 * f4D (a*u^2*v^2) * F u v) (-t-r) (-t+r))
      = ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
          4 * (a * (r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r)) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro t _
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    dsimp only
    rw [hFdef, show -(-t-r+(-t+r))/2 = t from by ring,
      show ((-t+r)-(-t-r))/2 = r from by ring,
      show (-t+r-(-t-r))^2 = 4*r^2 from by ring,
      show a*(-t-r)^2*(-t+r)^2 = a*(t^2-r^2)^2 from by ring]
    ring
  -- pull the constants out of the cone integral
  have hpull : (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
      4 * (a * (r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r)))
      = 4*a*∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
          r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r := by
    rw [show (4:ℝ)*a*∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
        r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r
        = ∫ t in Iio (0:ℝ), (4*a) * ∫ r in Ioo (0:ℝ) (-t),
          r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r from
      (integral_const_mul _ _).symm]
    apply setIntegral_congr_fun measurableSet_Iio
    intro t _
    dsimp only
    rw [show ((4:ℝ)*a) * ∫ r in Ioo (0:ℝ) (-t),
        r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r
        = ∫ r in Ioo (0:ℝ) (-t), (4*a) * (r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r)
        from (integral_const_mul _ _).symm]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    dsimp only
    ring
  -- orientation: the profile theorem's quadrant is (v-outer, u-inner)
  have horient : (∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
      a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
      = ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        a*(v-u)^2 * f4D (a*u^2*v^2) * F u v := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    exact hHsym y x
  -- the quadrant equals 16a times the physical cone integral
  have hQ : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
      = 16 * a * ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
          r^2 * f4D (a*(t^2-r^2)^2) * Mbar t r := by
    have h4 : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
        = 4 * ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
          (fun u v => a*(v-u)^2 * f4D (a*u^2*v^2) * F u v) (-t-r) (-t+r) := by
      linarith [hcq]
    rw [h4, hcone, hpull]
    ring
  rw [horient, hQ]

#print axioms cone_to_quadrant'
#print axioms bdg_4d_operator_reduced

end UnifiedTheory.Audit.KFCausalMinkowski4DOperator
