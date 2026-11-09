/-
Fourier diagonalization of the existing Poisson-series heat operator.
The expansion applies to every real function on a finite additive group.
It is not a continuum-limit theorem.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat
open UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
open scoped ComplexConjugate

section Eigenfunction
variable {V : Type*} [AddCommGroup V]

theorem walk_eigenfunction (ex ey : V) (f : V → ℝ) (r : ℝ)
    (hf : ∀ p, step ex ey f p = r * f p) (k : ℕ) (p : V) :
    walk ex ey f k p = r ^ k * f p := by
  induction k generalizing p with
  | zero => simp [walk]
  | succ k ih =>
    calc
      walk ex ey f (k + 1) p = r ^ k * step ex ey f p := by
        simp only [walk, step, ih]
        ring
      _ = r ^ (k + 1) * f p := by rw [hf, pow_succ]; ring

theorem heat_eigenfunction (ex ey : V) (f : V → ℝ) (r s : ℝ)
    (hf : ∀ p, step ex ey f p = r * f p) (p : V) :
    heat ex ey s f p = Real.exp (s * (r - 1)) * f p := by
  have h := ((NormedSpace.expSeries_div_hasSum_exp (s * r)).mul_left
    (Real.exp (-s))).mul_right (f p)
  have he : NormedSpace.exp (s * r) = Real.exp (s * r) :=
    congr_fun Real.exp_eq_exp_ℝ.symm (s * r)
  have hterm : (fun k : ℕ => (Real.exp (-s) * ((s * r) ^ k / (k.factorial : ℝ))) * f p) =
      (fun k => poissonWeight s k * walk ex ey f k p) := by
    funext k
    rw [walk_eigenfunction ex ey f r hf]
    simp only [poissonWeight, mul_pow]
    ring
  rw [hterm, he] at h
  rw [← Real.exp_add] at h
  have hex : -s + s * r = s * (r - 1) := by ring
  rw [hex] at h
  exact h.tsum_eq
end Eigenfunction

section Characters
variable {V : Type*} [AddCommGroup V] [Fintype V]

def characterEigenvalue (ex ey : V) (χ : AddChar V ℂ) : ℝ :=
  ((χ ex).re + (χ ey).re) / 2

theorem character_mode_step (ex ey : V) (χ : AddChar V ℂ) (c : ℂ) (p : V) :
    step ex ey (fun q => (c * χ q).re) p =
      characterEigenvalue ex ey χ * (c * χ p).re := by
  simp only [step, characterEigenvalue, sub_eq_add_neg, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_conj, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem character_mode_heat (ex ey : V) (χ : AddChar V ℂ) (c : ℂ) (s : ℝ) (p : V) :
    heat ex ey s (fun q => (c * χ q).re) p =
      Real.exp (s * (characterEigenvalue ex ey χ - 1)) * (c * χ p).re :=
  heat_eigenfunction ex ey _ _ s (character_mode_step ex ey χ c) p

def coefficient (f : V → ℝ) (χ : AddChar V ℂ) : ℂ :=
  (AddChar.complexBasis V).repr (fun p => (f p : ℂ)) χ

theorem real_fourier_inversion (f : V → ℝ) (p : V) :
    f p = ∑ χ : AddChar V ℂ, (coefficient f χ * χ p).re := by
  have h := congrArg (fun g : V → ℂ => (g p).re)
    ((AddChar.complexBasis V).sum_repr (fun q => (f q : ℂ)))
  simpa only [AddChar.complexBasis_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Complex.re_sum, Complex.ofReal_re, coefficient] using h.symm

/-- Every finite-grid datum, not only a selected Fourier mode, is diagonalized. -/
theorem heat_fourier (ex ey : V) (s : ℝ) (f : V → ℝ) (p : V) :
    heat ex ey s f p = ∑ χ : AddChar V ℂ,
      Real.exp (s * (characterEigenvalue ex ey χ - 1)) * (coefficient f χ * χ p).re := by
  classical
  have hf : f = ∑ χ : AddChar V ℂ, (fun q => (coefficient f χ * χ q).re) := by
    funext q
    simpa only [Finset.sum_apply] using real_fourier_inversion f q
  calc
    heat ex ey s f p = evolution ex ey s f p := (evolution_eq_heat ex ey s f p).symm
    _ = ∑ χ : AddChar V ℂ, evolution ex ey s (fun q => (coefficient f χ * χ q).re) p := by
      conv_lhs => rw [hf]
      rw [map_sum, Finset.sum_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [evolution_eq_heat, character_mode_heat]

theorem gridHeat_fourier (n : ℕ) [NeZero n] (t : ℝ) (f : Grid n → ℝ) (p : Grid n) :
    gridHeat n t f p = ∑ χ : AddChar (Grid n) ℂ,
      Real.exp (4 * (n : ℝ)^2 * t * (characterEigenvalue (1, 0) (0, 1) χ - 1)) *
        (coefficient f χ * χ p).re :=
  heat_fourier (1, 0) (0, 1) _ f p

end Characters

section GridCharacters
variable (n : ℕ) [NeZero n]

/-- The actual two-dimensional lattice character with integer frequency. -/
def gridCharacter (k : ℤ × ℤ) : AddChar (Grid n) ℂ where
  toFun p := ZMod.stdAddChar ((k.1 : ZMod n) * p.1 + (k.2 : ZMod n) * p.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' p q := by
    simp only [Prod.fst_add, Prod.snd_add, mul_add]
    rw [show (k.1 : ZMod n) * p.1 + k.1 * q.1 + (k.2 * p.2 + k.2 * q.2) =
      (k.1 * p.1 + k.2 * p.2) + (k.1 * q.1 + k.2 * q.2) by ring,
      AddChar.map_add_eq_mul]

theorem gridCharacter_axes (k : ℤ × ℤ) :
    ((gridCharacter n k (1, 0)).re = Real.cos (2 * Real.pi * k.1 / n)) ∧
    ((gridCharacter n k (0, 1)).re = Real.cos (2 * Real.pi * k.2 / n)) := by
  constructor <;>
    simp [gridCharacter, ZMod.stdAddChar_coe, Complex.exp_re, Complex.mul_re,
      Complex.mul_im, Complex.div_natCast_re, Complex.div_natCast_im]

theorem gridCharacter_eigenvalue (k : ℤ × ℤ) :
    4 * (n : ℝ)^2 * (1 - characterEigenvalue (1, 0) (0, 1) (gridCharacter n k)) =
      spectralSymbol (1 / n) k.1 + spectralSymbol (1 / n) k.2 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold characterEigenvalue
  rw [(gridCharacter_axes n k).1, (gridCharacter_axes n k).2]
  rw [show 2 * Real.pi * (k.1 : ℝ) / n = 2 * (Real.pi * (1 / n) * k.1) by ring,
    show 2 * Real.pi * (k.2 : ℝ) / n = 2 * (Real.pi * (1 / n) * k.2) by ring]
  rw [Real.cos_two_mul, Real.cos_two_mul]
  have hx := Real.sin_sq_add_cos_sq (Real.pi * k.1 / n)
  have hy := Real.sin_sq_add_cos_sq (Real.pi * k.2 / n)
  unfold spectralSymbol
  field_simp
  nlinarith [hx, hy]

theorem gridHeat_mode (k : ℤ × ℤ) (c : ℂ) (t : ℝ) (p : Grid n) :
    gridHeat n t (fun q => (c * gridCharacter n k q).re) p =
      Real.exp (-(spectralSymbol (1 / n) k.1 + spectralSymbol (1 / n) k.2) * t) *
        (c * gridCharacter n k p).re := by
  unfold gridHeat
  rw [character_mode_heat]
  congr 2
  rw [← gridCharacter_eigenvalue n k]
  ring

end GridCharacters
end
end UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
