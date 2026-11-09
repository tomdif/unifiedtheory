/- A symmetric bounded defect with the signed Hamiltonian pairing has
nonincreasing norm along a strongly differentiable Schrodinger trajectory.
This lemma will be applied to the constructed bounded Yosida dynamics. -/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalBoundedDefectMonotonicity
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (D : H →L[ℂ] H) (hD : ∀ x y, inner ℂ (D x) y = inner ℂ x (D y))
  (hbar : ℝ) (hh : hbar ≠ 0)

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

include hD in
theorem derivative_pairing (x y : H) :
    2*inner ℝ (D x) (D ((-Complex.I*((1/hbar:ℝ):ℂ)) • y)) =
      (-2/hbar)*(inner ℂ y (D (D x))).im := by
  rw [map_smul,real_inner_eq_re_inner ℂ,inner_smul_right,← hD]
  change 2*((-Complex.I*((1/hbar:ℝ):ℂ))*inner ℂ (D (D x)) y).re =
    (-2/hbar)*(inner ℂ y (D (D x))).im
  have hi : (inner ℂ (D (D x)) y).im = -(inner ℂ y (D (D x))).im :=
    inner_im_symm (𝕜 := ℂ) _ _
  simp [Complex.mul_re,Complex.mul_im,hi]
  ring

include hh in
theorem derivative_nonpositive (x y : H) (hs : 0 ≤ hbar*(inner ℂ y (D (D x))).im) :
    (-2/hbar)*(inner ℂ y (D (D x))).im ≤ 0 := by
  have he : (-2/hbar)*(inner ℂ y (D (D x))).im =
      (-2/hbar^2)*(hbar*(inner ℂ y (D (D x))).im) := by
    field_simp
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg hbar)) hs

include hD in
theorem norm_square_derivative (v : ℝ → H) (w : H) (t : ℝ)
    (hv : HasDerivAt v ((-Complex.I*((1/hbar:ℝ):ℂ)) • w) t) :
    HasDerivAt (fun r => ‖D (v r)‖^2) ((-2/hbar)*(inner ℂ w (D (D (v t)))).im) t := by
  have hd := (D.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hv
  change HasDerivAt (fun r => D (v r)) (D ((-Complex.I*((1/hbar:ℝ):ℂ)) • w)) t at hd
  convert hd.norm_sq using 1
  exact (derivative_pairing D hD hbar (v t) w).symm

include hD hh in
theorem norm_antitone (v : ℝ → H) (A : ℝ → H →L[ℂ] H)
    (hv : ∀ t, HasDerivAt v ((-Complex.I*((1/hbar:ℝ):ℂ)) • A t (v t)) t)
    (hs : ∀ t, 0 ≤ hbar*(inner ℂ (A t (v t)) (D (D (v t)))).im) :
    Antitone (fun t => ‖D (v t)‖) := by
  have ha : Antitone (fun t => ‖D (v t)‖^2) :=
    antitone_of_hasDerivAt_nonpos
      (fun t => norm_square_derivative D hD hbar v (A t (v t)) t (hv t))
      (fun t => derivative_nonpositive D hbar hh (v t) (A t (v t)) (hs t))
  intro s t hst
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (ha hst)

#print axioms derivative_pairing
#print axioms derivative_nonpositive
#print axioms norm_square_derivative
#print axioms norm_antitone

end
end UnifiedTheory.Audit.KFCausalBoundedDefectMonotonicity
