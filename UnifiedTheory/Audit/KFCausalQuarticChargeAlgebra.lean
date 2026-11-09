/- Finite tensor coefficients of the quartic paired polynomial and its
radial correction. The Fourier polynomial includes the lower-degree
terms produced by the Gaussian transform. -/
import UnifiedTheory.Audit.KFCausalGaussianQuarticFourier
import UnifiedTheory.Audit.KFCausalPairedQuadraticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalQuarticChargeAlgebra
noncomputable section
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianQuadraticFourier (moment second_moment_fourier)
open KFCausalGaussianQuarticFourier (fourth_moment_fourier)
open KFCausalPairedQuadraticFourier (product product_gaussian two_fourier)
open KFCausalChargeGaussianProducts (gaussian)

def powers : Fin 15 → Fin 4 → ℕ :=
  ![![0,0,4,0],![0,0,0,4],![0,0,2,2],![2,0,2,0],![2,0,0,2],
    ![0,2,2,0],![0,2,0,2],![4,0,0,0],![0,4,0,0],![2,2,0,0],
    ![2,0,0,0],![0,2,0,0],![0,0,2,0],![0,0,0,2],![0,0,0,0]]
def coefficients (A B D : ℂ) : Fin 15 → ℂ :=
  ![A,A,-2*A,-2*A,2*A,2*A,-2*A,A,A,-2*A,B,B,B,B,D]
def monomial (i : Fin 15) (u v x y : ℂ) : ℂ :=
  u^(powers i 0)*v^(powers i 1)*x^(powers i 2)*y^(powers i 3)
def fourierFactor (α : ℝ) (n : ℕ) (w : ℝ) : ℂ :=
  if n=0 then 1 else if n=2 then
    1/(2*(α:ℂ))-(Real.pi:ℂ)^2*(w:ℂ)^2/(α:ℂ)^2
  else if n=4 then
    3/(4*(α:ℂ)^2)-3*(Real.pi:ℂ)^2*(w:ℂ)^2/(α:ℂ)^3+
      (Real.pi:ℂ)^4*(w:ℂ)^4/(α:ℂ)^4
  else 0
def ratio (α : ℝ) : ℂ := (Real.pi:ℂ)^2/(α:ℂ)^2
def transformedMonomial (α : ℝ) (i : Fin 15) (u v : ℝ) (x y : ℂ) : ℂ :=
  fourierFactor α (powers i 0) u*fourierFactor α (powers i 1) v*
    x^(powers i 2)*y^(powers i 3)
def correctedCoefficients (α : ℝ) : Fin 15 → ℂ :=
  coefficients (1/4) (-1/(4*(α:ℂ))) (1/(8*(α:ℂ)^2))
def squareCoefficients : Fin 15 → ℂ := coefficients (1/4) 0 0

theorem powers_even (i : Fin 15) :
    (powers i 0=0 ∨ powers i 0=2 ∨ powers i 0=4) ∧
      (powers i 1=0 ∨ powers i 1=2 ∨ powers i 1=4) := by
  revert i
  decide

theorem polynomial_identity (A B D u v x y : ℂ) :
    (∑ i, coefficients A B D i*monomial i u v x y) =
      A*(x^2-y^2-u^2+v^2)^2+B*(u^2+v^2+x^2+y^2)+D := by
  simp [coefficients,monomial,powers,Fin.sum_univ_succ]
  ring

theorem even_moment_fourier (α : ℝ) (hα : 0 < α) (n : ℕ)
    (hn : n=0 ∨ n=2 ∨ n=4) (w : ℝ) :
    (𝓕 (moment α n)) w = fourierFactor α n w*(𝓕 (moment α 0)) w := by
  rcases hn with rfl | rfl | rfl
  · simp only [fourierFactor,ite_true,one_mul]
  · simpa only [fourierFactor,show ¬(2:ℕ)=0 by decide,ite_false,ite_true] using
      second_moment_fourier α hα w
  · simpa only [fourierFactor,show ¬(4:ℕ)=0 by decide,show ¬(4:ℕ)=2 by decide,
      ite_false,ite_true] using fourth_moment_fourier α hα w

theorem product_fourier (α : ℝ) (hα : 0 < α) (i : Fin 15) (w : Block 2) :
    (𝓕 (product α (powers i 0) (powers i 1))) w =
      fourierFactor α (powers i 0) (w 0)*fourierFactor α (powers i 1) (w 1)*
        (𝓕 (gaussian 2 α)) w := by
  have hg : gaussian 2 α = product α 0 0 := funext (fun u => (product_gaussian α u).symm)
  rw [hg]
  unfold product
  rw [two_fourier,two_fourier,even_moment_fourier α hα _ (powers_even i).1,
    even_moment_fourier α hα _ (powers_even i).2]
  ring

theorem transformed_identity (α : ℝ) (hα : 0 < α) (A B D : ℂ) (u v : ℝ) (x y : ℂ) :
    (∑ i, coefficients A B D i*transformedMonomial α i u v x y) =
      A*((x^2-y^2+ratio α*((u:ℂ)^2-(v:ℂ)^2))^2-
        2*ratio α/(α:ℂ)*((u:ℂ)^2+(v:ℂ)^2)+1/(α:ℂ)^2)+
      B*(x^2+y^2-ratio α*((u:ℂ)^2+(v:ℂ)^2)+1/(α:ℂ))+D := by
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  simp [coefficients,transformedMonomial,powers,fourierFactor,ratio,Fin.sum_univ_succ]
  field_simp
  ring

theorem corrected_identity (α : ℝ) (hα : 0 < α) (u v : ℝ) (x y : ℂ) :
    (∑ i, correctedCoefficients α i*transformedMonomial α i u v x y) =
      (x^2-y^2+ratio α*((u:ℂ)^2-(v:ℂ)^2))^2/4-
        (x^2+y^2+ratio α*((u:ℂ)^2+(v:ℂ)^2))/(4*(α:ℂ))+1/(8*(α:ℂ)^2) := by
  rw [correctedCoefficients,transformed_identity α hα]
  ring

theorem square_identity (α : ℝ) (hα : 0 < α) (u v : ℝ) (x y : ℂ) :
    (∑ i, squareCoefficients i*transformedMonomial α i u v x y) =
      (x^2-y^2+ratio α*((u:ℂ)^2-(v:ℂ)^2))^2/4-
        ratio α*((u:ℂ)^2+(v:ℂ)^2)/(2*(α:ℂ))+1/(4*(α:ℂ)^2) := by
  rw [squareCoefficients,transformed_identity α hα]
  ring

#print axioms powers_even
#print axioms polynomial_identity
#print axioms even_moment_fourier
#print axioms product_fourier
#print axioms transformed_identity
#print axioms corrected_identity
#print axioms square_identity
end
end UnifiedTheory.Audit.KFCausalQuarticChargeAlgebra
