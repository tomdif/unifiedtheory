/- Complex unitary rotations of the normalized transverse coordinates.
The intertwining identity uses the existing physical charge action and
the reciprocal target metric, rather than the narrow Fourier chart. -/
import UnifiedTheory.Audit.KFCausalPhysicalReciprocalNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNormalizedComplexRotation
noncomputable section
open KFCausalComplexShearPerturbation (Space)
open KFCausalPhysicalReciprocalNormalization (normalize)
open KFCausalEuclideanProductCoordinates (Joint)

def rotate (θ : ℝ) (x : Space) : Space := WithLp.toLp 2
  ![(Real.cos θ:ℂ)*x 0-(Real.sin θ:ℂ)*x 2,
    (Real.cos θ:ℂ)*x 1-(Real.sin θ:ℂ)*x 3,
    (Real.sin θ:ℂ)*x 0+(Real.cos θ:ℂ)*x 2,
    (Real.sin θ:ℂ)*x 1+(Real.cos θ:ℂ)*x 3,x 4]

theorem rotate_zero (x : Space) : rotate 0 x=x := by
  ext i
  fin_cases i <;> simp [rotate]

theorem rotate_compose (θ φ : ℝ) (x : Space) :
    rotate θ (rotate φ x)=rotate (θ+φ) x := by
  ext i
  fin_cases i <;> simp [rotate,Real.sin_add,Real.cos_add] <;> ring

theorem rotate_reverse (θ : ℝ) (x : Space) : rotate (-θ) (rotate θ x)=x := by
  rw [rotate_compose,neg_add_cancel,rotate_zero]

def rotationEquiv (θ : ℝ) : Space ≃ₗ[ℂ] Space where
  toFun := rotate θ
  invFun := rotate (-θ)
  left_inv := rotate_reverse θ
  right_inv x := by simpa only [neg_neg] using rotate_reverse (-θ) x
  map_add' x y := by ext i; fin_cases i <;> simp [rotate] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [rotate] <;> ring

private theorem pair_inner (θ : ℝ) (a b c d : ℂ) :
    star ((Real.cos θ:ℂ)*a-(Real.sin θ:ℂ)*b)*((Real.cos θ:ℂ)*c-(Real.sin θ:ℂ)*d)+
    star ((Real.sin θ:ℂ)*a+(Real.cos θ:ℂ)*b)*((Real.sin θ:ℂ)*c+(Real.cos θ:ℂ)*d)=
      star a*c+star b*d := by
  have h : (Real.sin θ:ℂ)^2+(Real.cos θ:ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  simp only [star_sub,star_add,star_mul,Complex.star_def,Complex.conj_ofReal]
  calc
    _ = ((Real.sin θ:ℂ)^2+(Real.cos θ:ℂ)^2)*(star a*c+star b*d) := by
      simp only [Complex.star_def]
      ring
    _ = _ := by simp only [h,one_mul,Complex.star_def]

theorem rotation_inner (θ : ℝ) (x y : Space) :
    inner ℂ (rotationEquiv θ x) (rotationEquiv θ y)=inner ℂ x y := by
  have h₁ := pair_inner θ (x 0) (x 2) (y 0) (y 2)
  have h₂ := pair_inner θ (x 1) (x 3) (y 1) (y 3)
  simp only [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [rotationEquiv,rotate,RCLike.inner_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]
  simp only [Complex.star_def,map_add,map_sub,map_mul,Complex.conj_ofReal] at h₁ h₂
  linear_combination h₁+h₂

def rotationIsometry (θ : ℝ) : Space ≃ₗᵢ[ℂ] Space where
  toLinearEquiv := rotationEquiv θ
  norm_map' := ((rotationEquiv θ).toLinearMap.isometryOfInner (rotation_inner θ)).norm_map

theorem rotationIsometry_apply (θ : ℝ) (x : Space) : rotationIsometry θ x=rotate θ x := rfl

theorem physical_rotation (α w c θ : ℝ) (hc : c ≠ 0) (x : Joint 2 4) :
    normalize α w c (KFCausalNormalizedChargeFlow.flowEquiv c hc θ x)=
      rotationIsometry θ (normalize α w c x) := by
  have h₁ := KFCausalNormalizedChargeFlow.flow_first_plane c hc θ x
  have h₂ := KFCausalNormalizedChargeFlow.flow_second_plane c hc θ x
  have h₁a := congrArg Prod.fst h₁
  have h₁b := congrArg Prod.snd h₁
  have h₂a := congrArg Prod.fst h₂
  have h₂b := congrArg Prod.snd h₂
  dsimp only at h₁a h₁b h₂a h₂b
  have hcc : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  ext i
  fin_cases i <;> simp [KFCausalPhysicalReciprocalNormalization.normalize,rotationIsometry,rotationEquiv,rotate,h₁a,h₁b,h₂a,h₂b,
    KFCausalNormalizedChargeFlow.flow_neutral]
  all_goals try field_simp [hcc]

#print axioms rotate_zero
#print axioms rotate_compose
#print axioms rotate_reverse
#print axioms rotation_inner
#print axioms rotationIsometry_apply
#print axioms physical_rotation
end
end UnifiedTheory.Audit.KFCausalNormalizedComplexRotation
