/- Quasi-dissipativity in a positive symmetric form gives a uniform
energy bound for full-generator resolvent regularizations. -/
import UnifiedTheory.Audit.KFCausalWeightedMassEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuasiDissipativeResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem energy_sub_real (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (f u : V) (r : ℝ) :
    energy F (f-r • u) = energy F f-2*r*(inner ℂ u (F f)).re+r^2*energy F u := by
  have he : (inner ℂ f (F u)).re = (inner ℂ u (F f)).re :=
    (inner_re_symm (𝕜 := ℂ) f (F u)).trans (congrArg Complex.re (hF u f))
  simp only [energy,map_sub,ContinuousLinearMap.map_smul_of_tower,
    inner_sub_left,inner_sub_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,he]
  ring

theorem lower_pairing_energy (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy F x) (f u : V) (r : ℝ) (hr : 0 ≤ r)
    (hpair : r*energy F u ≤ (inner ℂ u (F f)).re) : r^2*energy F u ≤ energy F f := by
  have he := hp (f-r • u)
  rw [energy_sub_real F hF] at he
  have hm := mul_le_mul_of_nonneg_left hpair hr
  nlinarith only [he,hm]

theorem resolvent_energy (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy F x) (f u y : V) (b ω : ℝ) (hb : ω ≤ b)
    (he : b • u-y = f) (hq : (inner ℂ u (F y)).re ≤ ω*energy F u) :
    (b-ω)^2*energy F u ≤ energy F f := by
  apply lower_pairing_energy F hF hp f u (b-ω) (sub_nonneg.mpr hb)
  have hh : (inner ℂ u (F f)).re = b*energy F u-(inner ℂ u (F y)).re := by
    rw [← he,map_sub,ContinuousLinearMap.map_smul_of_tower,inner_sub_right,inner_smul_right_eq_smul]
    simp only [energy,Complex.sub_re,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hh]
  nlinarith only [hq]

theorem dissipation_identity (F : V →L[ℂ] V) (u y : V) (b : ℝ) :
    (inner ℂ (b • u-y) (F (b • y))).re = b^2*(inner ℂ u (F y)).re-b*energy F y := by
  simp only [energy,ContinuousLinearMap.map_smul_of_tower,inner_sub_left,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,Complex.sub_re,Complex.real_smul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem uniform_dissipation (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy F x) (f u y : V) (b ω : ℝ)
    (hb : 0 < b) (hω : 0 ≤ ω) (hhalf : 2*ω ≤ b)
    (he : b • u-y = f) (hq : (inner ℂ u (F y)).re ≤ ω*energy F u) :
    (inner ℂ f (F (b • y))).re ≤ (4*ω)*energy F f := by
  have hgap : ω ≤ b := by linarith
  have hres := resolvent_energy F hF hp f u y b ω hgap he hq
  have hs : b^2 ≤ 4*(b-ω)^2 := by nlinarith only [hhalf,hω,hb]
  have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg hω (hp u))
  have hr := mul_le_mul_of_nonneg_left hres (show 0 ≤ 4*ω by positivity)
  have hq' := mul_le_mul_of_nonneg_left hq (sq_nonneg b)
  have hy := mul_nonneg hb.le (hp y)
  have hid := dissipation_identity F u y b
  rw [he] at hid
  nlinarith only [hm,hr,hq',hy,hid]

theorem approximation_bound (T : V →ₗ.[ℂ] V) (F R A : V →L[ℂ] V) (b ω : ℝ)
    (hF : F.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy F x)
    (hb : 0 < b) (hω : 0 ≤ ω) (hhalf : 2*ω ≤ b)
    (hA : A = b • (b • R-1))
    (hR : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hq : ∀ x y, (x,y) ∈ T.graph → (inner ℂ x (F y)).re ≤ ω*energy F x) (f : V) :
    (inner ℂ f (F (A f))).re ≤ (4*ω)*energy F f := by
  have he : b • R f-(b • R f-f) = f := by abel
  have hh := uniform_dissipation F hF hp f (R f) (b • R f-f) b ω hb hω hhalf he
    (hq _ _ (hR f))
  simpa only [hA,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using hh

#print axioms energy_sub_real
#print axioms lower_pairing_energy
#print axioms resolvent_energy
#print axioms dissipation_identity
#print axioms uniform_dissipation
#print axioms approximation_bound
end
end UnifiedTheory.Audit.KFCausalQuasiDissipativeResolvent
