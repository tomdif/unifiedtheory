/- Exact null-coordinate normalization for continuous compact symmetric
profiles, including the actual curvature derivative kernel. This supplies
the original radial-cone integral, not a curved causal-diamond identification. -/
import UnifiedTheory.Audit.KFCausalMinkowski4DEulerQuadrant
import UnifiedTheory.Audit.KFCausalMinkowski4DOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalMinkowski4DVariationCone
noncomputable section
open MeasureTheory Set
open KFCausalMinkowski4DEulerIBP (variation fd)
open KFCausalMinkowski4DEulerQuadrant
open KFCausalMinkowski4DMoments (f4D)

def coneIntegral (κ : ℝ → ℝ) (a : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
    r^2*κ (a*(t^2-r^2)^2)*F (-t-r,-t+r)

theorem kernel_cone_normalization (κ : ℝ → ℝ) (hκ : Continuous κ)
    (a T : ℝ) (hT : 0 < T) (F : ℝ × ℝ → ℝ) (hF : Continuous F)
    (hcompact : HasCompactSupport F) (hs : UpperSupport T T F)
    (hsym : ∀ u v, F (u,v)=F (v,u)) :
    quadrantIntegral (fun p => a*(p.2-p.1)^2*κ (a*p.1^2*p.2^2)*F p) =
      16*a*coneIntegral κ a F := by
  let H : ℝ × ℝ → ℝ := fun p => a*(p.2-p.1)^2*κ (a*p.1^2*p.2^2)*F p
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hHc : HasCompactSupport H := hcompact.mul_left
  obtain ⟨M,hM⟩ := hHc.exists_bound_of_continuous hH
  have hM0 : 0 ≤ M := (norm_nonneg (H (0,0))).trans (hM (0,0))
  have hHsym (u v : ℝ) : H (u,v)=H (v,u) := by
    dsimp [H]
    rw [hsym u v,show (u-v)^2=(v-u)^2 from by ring,
      show a*v^2*u^2=a*u^2*v^2 from by ring]
  have hsH : UpperSupport T T H := by
    intro p hp; dsimp [H]; rw [hs p hp,mul_zero]
  have hquad : quadrantIntegral H =
      ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ), H (u,v) := by
    rw [quadrant_eq_iterated T T H hH hsH]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    exact hHsym v u
  have hcq := KFCausalMinkowski4DOperator.cone_to_quadrant'
    (fun u v => H (u,v)) M T hM0 hT hH.measurable hHsym
      (fun u v => by simpa only [Real.norm_eq_abs] using hM (u,v))
      (fun u v hu => hsH (u,v) (Or.inl hu))
  have hcone : (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), H (-t-r,-t+r)) =
      4*a*coneIntegral κ a F := by
    unfold coneIntegral
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iio
    intro t _
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    dsimp [H]
    rw [show (-t+r-(-t-r))^2=4*r^2 from by ring,
      show a*(-t-r)^2*(-t+r)^2=a*(t^2-r^2)^2 from by ring]
    ring
  rw [hcone,← hquad] at hcq
  change quadrantIntegral H=16*a*coneIntegral κ a F
  linarith

theorem variation_cone_normalization (a T : ℝ) (hT : 0 < T)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) (hcompact : HasCompactSupport F)
    (hs : UpperSupport T T F) (hsym : ∀ u v, F (u,v)=F (v,u)) :
    quadrantIntegral (fun p => variation a p.1 p.2*F p) =
      16*a*coneIntegral (fun x => x*deriv f4D x) a F := by
  have hf (x : ℝ) : deriv f4D x=fd x :=
    (KFCausalMinkowski4DSecondOrder.f4D_hasDerivAt x).deriv
  simp_rw [hf]
  have hκ : Continuous (fun x : ℝ => x*fd x) := by dsimp [fd]; fun_prop
  have hn := kernel_cone_normalization (fun x => x*fd x) hκ a T hT F hF hcompact hs hsym
  convert hn using 1
  apply congrArg quadrantIntegral
  funext p
  dsimp [variation]
  ring

#print axioms kernel_cone_normalization
#print axioms variation_cone_normalization
end
end UnifiedTheory.Audit.KFCausalMinkowski4DVariationCone
