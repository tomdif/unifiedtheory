/- Gaussian/Laplace domination with positive width floors and bounded
linear sources. No inverse width-spacing constant enters these bounds. -/
import UnifiedTheory.Audit.KFCausalJointCompactPolynomialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointUniformWeightEnvelope
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalJointPolynomialIntegrability (weight)
open KFCausalJointCompactPolynomialBounds

theorem gaussian_linear_bound (c q l L x : ℝ) (hc : q ≤ c) (hl : |l| ≤ L) :
    Real.exp (-c*x^2+l*x) ≤ Real.exp (-q*x^2+L*x)+Real.exp (-q*x^2-L*x) := by
  rcases le_total 0 x with hx | hx
  · apply (Real.exp_le_exp.mpr (show -c*x^2+l*x ≤ -q*x^2+L*x by
      nlinarith [(abs_le.mp hl).2,mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg x),mul_nonneg (sub_nonneg.mpr (abs_le.mp hl).2) hx])).trans
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · apply (Real.exp_le_exp.mpr (show -c*x^2+l*x ≤ -q*x^2-L*x by
      nlinarith [(abs_le.mp hl).1,mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg x),mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ l+L by linarith [(abs_le.mp hl).1]) hx])).trans
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem weight_le (a c d l m q L : ℝ) (ha : q ≤ a) (hc : q ≤ c) (hl : |l| ≤ L)
    (p : Joint) (hp : 0 ≤ p.2) :
    weight a c d l m p ≤ weight q q d L m p+weight q q d (-L) m p := by
  have hu : Real.exp (-a*p.1.1^2) ≤ Real.exp (-q*p.1.1^2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg p.1.1)])
  have hy : Real.exp (-a*p.2) ≤ Real.exp (-q*p.2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ha) hp])
  have hv := gaussian_linear_bound c q l L (p.1.2 0) hc hl
  calc
    _ ≤ Real.exp (-q*p.1.1^2)*(Real.exp (-q*(p.1.2 0)^2+L*p.1.2 0)+
        Real.exp (-q*(p.1.2 0)^2-L*p.1.2 0))*
        Real.exp (-d*(p.1.2 1)^2+m*p.1.2 1)*Real.exp (-q*p.2) := by
      unfold weight
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul hu hv (Real.exp_pos _).le (Real.exp_pos _).le)
          (Real.exp_pos _).le) hy (Real.exp_pos _).le (by positivity)
    _ = _ := by simp only [weight,neg_mul,sub_eq_add_neg]; ring

theorem weight_nonnegative (a c d l m : ℝ) (p : Joint) : 0 ≤ weight a c d l m p := by
  unfold weight
  positivity

theorem controlled_square_envelope {X : Type*} [TopologicalSpace X] (K : Set X)
    (hK : IsCompact K) (f : X → Joint → ℂ) (hf : Controlled K f)
    (a c l : X → ℝ) (hl : Continuous l) (d m q : ℝ) (hd : 0 < d) (hq : 0 < q)
    (ha : ∀ s ∈ K, q ≤ a s) (hc : ∀ s ∈ K, q ≤ c s) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 → ‖f s p‖^2*weight (a s) (c s) d (l s) m p ≤ D p := by
  obtain ⟨Q,hQ,hf⟩ := hf
  obtain ⟨L,hL⟩ := hK.exists_bound_of_continuousOn hl.continuousOn
  refine ⟨fun p => val Q p^2*(weight q q d L m p+weight q q d (-L) m p), ?_, ?_, ?_⟩
  · convert (val_squared_integrable Q q q d L m hq hq hd).add
      (val_squared_integrable Q q q d (-L) m hq hq hd) using 1
    funext p
    simp only [Pi.add_apply]
    ring
  · intro p
    exact mul_nonneg (sq_nonneg _) (add_nonneg (weight_nonnegative _ _ _ _ _ _) (weight_nonnegative _ _ _ _ _ _))
  · intro s hs p hp
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hf s hs p) 2)
      (weight_le _ _ _ _ _ q L (ha s hs) (hc s hs) (by simpa only [Real.norm_eq_abs] using hL s hs) p hp)
      (weight_nonnegative _ _ _ _ _ _) (sq_nonneg _)

#print axioms gaussian_linear_bound
#print axioms weight_le
#print axioms weight_nonnegative
#print axioms controlled_square_envelope
end
end UnifiedTheory.Audit.KFCausalJointUniformWeightEnvelope
