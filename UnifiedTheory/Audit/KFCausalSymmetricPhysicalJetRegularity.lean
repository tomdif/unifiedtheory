/- Continuity of the actual complete symmetric derivative multipliers
on the real clock line and in the charge angle. -/
import UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetMultiplier
import UnifiedTheory.Audit.KFCausalSymmetricDirectionRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetRegularity
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalSymmetricPhysicalJets (multiplier actualCore core)
open KFCausalSymmetricDirectionRegularity
open KFCausalSymmetricNumeratorJets (slope curvature)
open KFCausalComplexQuadraticPerturbation (bilinear quadratic)
open KFCausalWidthGaussianNeutralMultiplier (neutral)

private theorem core_continuous {T : Type*} [TopologicalSpace T]
    (Q P : Polynomial ℂ) (A z a d g c : T → ℂ) (order : Fin 3)
    (hA : Continuous A) (hz : Continuous z) (ha : Continuous a) (hd : Continuous d)
    (hg : Continuous g) (hc : Continuous c) :
    Continuous (fun t => core Q P (A t) (z t) (a t) (d t) (g t) (c t) order) := by
  have hQ := Q.continuous.comp hA
  have hQ' := Q.derivative.continuous.comp hA
  have hQ'' := Q.derivative.derivative.continuous.comp hA
  have hP := P.continuous.comp hz
  have hP' := P.derivative.continuous.comp hz
  have hP'' := P.derivative.derivative.continuous.comp hz
  fin_cases order <;> dsimp [core,KFCausalSymmetricJetBounds.firstCore,KFCausalSymmetricJetBounds.secondCore]
  all_goals fun_prop

private theorem slope_continuous {T : Type*} [TopologicalSpace T] (b : ℂ)
    (d : T → ℂ) (Z U : T → Fin 5 → ℂ) (hd : Continuous d)
    (hZ : ∀ j, Continuous (fun t => Z t j)) (hU : ∀ j, Continuous (fun t => U t j)) :
    Continuous (fun t => slope b (d t) (Z t) (U t)) := by
  apply (continuous_const.mul hd).sub
  apply continuous_const.mul
  exact continuous_finset_sum _ (fun j _ => (hZ j).mul (hU j))

private theorem curvature_continuous {T : Type*} [TopologicalSpace T]
    (U : T → Fin 5 → ℂ) (hU : ∀ j, Continuous (fun t => U t j)) :
    Continuous (fun t => curvature (U t)) := by
  apply continuous_const.mul
  exact continuous_finset_sum _ (fun j _ => (hU j).pow 2)

theorem multiplier_factor (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b Q P i order q x=
      actualCore ε h α w c θ b Q P i order q x*
        KFCausalWidthGaussianNeutralMultiplier.multiplier ε h a α W w c θ C p b 1 q x := by
  simp only [multiplier,KFCausalWidthGaussianNeutralMultiplier.multiplier,Polynomial.eval_one,one_mul]
  ring

theorem multiplier_real_continuous (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (hε : 0 < ε) (hb : |h| ≤ ε/10) :
    Continuous (fun v : ℝ × Joint 2 4 => multiplier ε h a α W w c θ C p b Q P i order (v.1:ℂ) v.2) := by
  have hA := matter_horizontal_continuous ε h α w c θ hε hb 0 (by simp)
  have hz := KFCausalWidthGaussianNeutralMultiplier.neutral_horizontal_continuous ε h α w c θ hε hb 0 (by simp)
  have ha := (matterSlope_horizontal_continuous ε h α w θ i hε hb 0 (by simp)).comp
    (continuous_fst : Continuous (Prod.fst : ℝ × Joint 2 4 → ℝ))
  have hd := (neutralSlope_horizontal_continuous ε h α w θ i hε hb 0 (by simp)).comp
    (continuous_fst : Continuous (Prod.fst : ℝ × Joint 2 4 → ℝ))
  have hZ := targetVector_horizontal_continuous ε h α w c θ hε hb 0 (by simp)
  have hU (j : Fin 5) := (targetDirection_horizontal_continuous ε h α w θ i hε hb 0 (by simp) j).comp
    (continuous_fst : Continuous (Prod.fst : ℝ × Joint 2 4 → ℝ))
  have hcore := core_continuous Q P _ _ _ _ _ _ order hA hz ha hd
    (slope_continuous b _ _ _ hd hZ hU) (curvature_continuous _ hU)
  have hm := KFCausalWidthGaussianNeutralMultiplier.multiplier_horizontal_continuous
    ε h a α W w c θ C p b 1 hε hb 0 (by simp)
  simp_rw [multiplier_factor]
  simpa only [actualCore,Complex.ofReal_zero,zero_mul,add_zero,Function.comp_apply] using hcore.mul hm

theorem multiplier_angle_continuous (ε h a α W w c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun θ => multiplier ε h a α W w c θ C p b Q P i order q x) := by
  have hA := matter_angle_continuous ε h α w c q x
  have hz := KFCausalWidthGaussianNeutralMultiplier.neutral_angle_continuous ε h α w c q x
  have ha := matterSlope_angle_continuous ε h α w i q
  have hd := neutralSlope_angle_continuous ε h α w i q
  have hZ := targetVector_angle_continuous ε h α w c q x
  have hU := targetDirection_angle_continuous ε h α w i q
  have hcore := core_continuous Q P _ _ _ _ _ _ order hA hz ha hd
    (slope_continuous b _ _ _ hd hZ hU) (curvature_continuous _ hU)
  have hm := KFCausalWidthGaussianNeutralMultiplier.multiplier_angle_continuous
    ε h a α W w c C p b 1 q x
  simp_rw [multiplier_factor]
  exact hcore.mul hm

#print axioms multiplier_factor
#print axioms multiplier_real_continuous
#print axioms multiplier_angle_continuous
end
end UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetRegularity
