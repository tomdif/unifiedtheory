/- The actual compact quadratic curvature-kernel limit, proved by exact
Euler integration by parts and an ordinary flat-profile limit. No limit is
differentiated. The original radial-cone normalization is retained. -/
import UnifiedTheory.Audit.KFCausalBDG4DQuadraticEulerProfiles
import UnifiedTheory.Audit.KFCausalMinkowski4DVariationCone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DQuadraticVariationLimit
noncomputable section
open MeasureTheory Set Filter Topology Real
open KFCausalMinkowski4DEulerIBP (kernel variation)
open KFCausalMinkowski4DEulerQuadrant
open KFCausalMinkowski4DVariationCone (coneIntegral)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalBDG4DQuadraticEulerProfiles

private theorem profile_support (A B : ℝ) :
    UpperSupport 3 3 (Function.uncurry (profile A B)) ∧
    UpperSupport 3 3 (Function.uncurry (profileU A B)) ∧
    UpperSupport 3 3 (Function.uncurry (profileV A B)) := by
  have h (p : ℝ × ℝ) (hp : (3:ℝ) ≤ p.1 ∨ 3 ≤ p.2) :=
    profile_outside A B p.1 p.2 (hp.imp (fun q => q.trans (le_abs_self _))
      (fun q => q.trans (le_abs_self _)))
  exact ⟨fun p hp => (h p hp).1,fun p hp => (h p hp).2.1,fun p hp => (h p hp).2.2⟩

private theorem euler_support (A B : ℝ) : UpperSupport 3 3 (Function.uncurry (eulerProfile A B)) := by
  intro p hp
  exact euler_outside A B p.1 p.2 (hp.imp (fun q => q.trans (le_abs_self _))
    (fun q => q.trans (le_abs_self _)))

theorem variation_identity (a A B : ℝ) :
    quadrantIntegral (fun p => variation a p.1 p.2*profile A B p.1 p.2) =
      -(1/4)*(∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
        a*(v-u)^2*f4D (a*u^2*v^2)*eulerProfile A B u v) := by
  obtain ⟨hsF,hsU,hsV⟩ := profile_support A B
  have he := quadrant_euler_identity a 3 3 (by norm_num) (by norm_num)
    (Function.uncurry (profile A B)) (Function.uncurry (profileU A B))
    (Function.uncurry (profileV A B)) (profile_continuous A B)
    (profileU_continuous A B) (profileV_continuous A B)
    (fun v u => profile_derivative_u A B u v)
    (fun u v => profile_derivative_v A B u v) hsF hsU hsV
  have hc : Continuous (fun p : ℝ × ℝ => kernel a p.1 p.2*eulerProfile A B p.1 p.2) := by
    have h := euler_continuous A B
    dsimp [kernel,f4D]; fun_prop
  have hs : UpperSupport 3 3 (fun p => kernel a p.1 p.2*eulerProfile A B p.1 p.2) := by
    intro p hp
    have hz : eulerProfile A B p.1 p.2 = 0 := euler_support A B p hp
    dsimp only; rw [hz,mul_zero]
  dsimp only [Function.uncurry] at he
  simp only [← euler_identity] at he
  rw [quadrant_eq_iterated 3 3 _ hc hs] at he
  exact he

theorem variation_quadrant_tendsto (A B : ℝ) :
    Tendsto (fun a : ℝ => sqrt a*quadrantIntegral
      (fun p => variation a p.1 p.2*profile A B p.1 p.2)) atTop
      (𝓝 (-(sqrt π*(A-B))/4)) := by
  have h := (euler_tendsto A B).const_mul (-(1/4):ℝ)
  have hv : (-(1/4):ℝ)*(sqrt π*(A-B)) = -(sqrt π*(A-B))/4 := by ring
  rw [hv] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun a => by dsimp only; rw [variation_identity]; ring)

theorem ordinary_cone_tendsto (A B : ℝ) :
    Tendsto (fun a : ℝ => sqrt a*(16*a*coneIntegral f4D a (Function.uncurry (profile A B))))
      atTop (𝓝 (sqrt π*(A-B)/6)) := by
  apply (profile_tendsto A B).congr'
  apply Filter.Eventually.of_forall
  intro a
  have hc : Continuous (fun p : ℝ × ℝ => kernel a p.1 p.2*profile A B p.1 p.2) := by
    have h := profile_continuous A B
    dsimp [kernel,f4D]; fun_prop
  have hs : UpperSupport 3 3 (fun p => kernel a p.1 p.2*profile A B p.1 p.2) := by
    intro p hp
    have hz : profile A B p.1 p.2 = 0 := (profile_support A B).1 p hp
    dsimp only; rw [hz,mul_zero]
  have hq := quadrant_eq_iterated 3 3 _ hc hs
  have hn := KFCausalMinkowski4DVariationCone.kernel_cone_normalization f4D
    (by unfold f4D; fun_prop) a 3 (by norm_num) (Function.uncurry (profile A B))
    (profile_continuous A B) (profile_compact A B) (profile_support A B).1 (profile_symmetric A B)
  change quadrantIntegral (fun p => kernel a p.1 p.2*profile A B p.1 p.2)=_ at hn
  rw [hq] at hn
  exact congrArg (fun x : ℝ => sqrt a*x) hn

theorem variation_cone_tendsto (A B : ℝ) :
    Tendsto (fun a : ℝ => sqrt a*(16*a*coneIntegral (fun x => x*deriv f4D x) a
      (Function.uncurry (profile A B)))) atTop (𝓝 (-(sqrt π*(A-B))/4)) := by
  apply (variation_quadrant_tendsto A B).congr'
  apply Filter.Eventually.of_forall
  intro a
  exact congrArg (fun x : ℝ => sqrt a*x)
    (KFCausalMinkowski4DVariationCone.variation_cone_normalization a 3 (by norm_num)
      (Function.uncurry (profile A B)) (profile_continuous A B) (profile_compact A B)
      (profile_support A B).1 (profile_symmetric A B))

#print axioms variation_identity
#print axioms variation_quadrant_tendsto
#print axioms ordinary_cone_tendsto
#print axioms variation_cone_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DQuadraticVariationLimit
