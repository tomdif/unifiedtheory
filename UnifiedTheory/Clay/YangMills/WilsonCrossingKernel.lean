/- Positive definiteness of the unitary-character Wilson crossing weight.
The result concerns arbitrary finite samples and arbitrary complex coefficients,
not merely pointwise positivity of the Boltzmann weight. Attaching the crossing
kernel to an actual reflected lattice measure is a separate geometric step. -/
import UnifiedTheory.Clay.YangMills.RegulatedGauge
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.StarOrdered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
noncomputable section
open Filter Matrix
open scoped Topology

variable {ι D X : Type*} [Fintype ι] [Fintype D]

def realQuadratic (K : ι → ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * K i j * c j

def featureKernel (φ : X → D → ℝ) (x y : X) : ℝ := ∑ k, φ x k * φ y k

theorem featureKernel_symm (φ : X → D → ℝ) (x y : X) :
    featureKernel φ x y = featureKernel φ y x := by
  simp only [featureKernel, mul_comm]

theorem feature_quadratic_nonneg (φ : ι → D → ℝ) (c : ι → ℝ) :
    0 ≤ realQuadratic (featureKernel φ) c := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (fun k i => φ i k)).dotProduct_mulVec_nonneg c
  simpa [realQuadratic, featureKernel, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc] using h

theorem feature_power (φ : X → D → ℝ) (x y : X) (m : ℕ) :
    featureKernel φ x y ^ m =
      featureKernel (fun z (p : Fin m → D) => ∏ t, φ z (p t)) x y := by
  simp only [featureKernel, Fintype.sum_pow, Finset.prod_mul_distrib]

theorem feature_power_quadratic_nonneg (φ : ι → D → ℝ) (c : ι → ℝ) (m : ℕ) :
    0 ≤ realQuadratic (fun i j => featureKernel φ i j ^ m) c := by
  simp only [feature_power]
  exact feature_quadratic_nonneg _ c

theorem realQuadratic_scale (K : ι → ι → ℝ) (c : ι → ℝ) (a : ℝ) :
    realQuadratic (fun i j => a * K i j) c = a * realQuadratic K c := by
  simp only [realQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exponentiating a finite real feature inner product preserves positive definiteness. -/
theorem exp_feature_quadratic_nonneg (φ : ι → D → ℝ) (c : ι → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ realQuadratic (fun i j => Real.exp (β * featureKernel φ i j)) c := by
  let T : ℕ → ℝ := fun m => realQuadratic
    (fun i j => (β * featureKernel φ i j) ^ m / (m.factorial : ℝ)) c
  have hT (m : ℕ) : 0 ≤ T m := by
    have heq : T m = (β ^ m / (m.factorial : ℝ)) *
        realQuadratic (fun i j => featureKernel φ i j ^ m) c := by
      dsimp [T]
      rw [← realQuadratic_scale]
      congr 1
      funext i j
      rw [mul_pow]
      ring
    rw [heq]
    exact mul_nonneg (div_nonneg (pow_nonneg hβ _) (Nat.cast_nonneg _))
      (feature_power_quadratic_nonneg φ c m)
  have hsum : HasSum T (realQuadratic (fun i j => Real.exp (β * featureKernel φ i j)) c) := by
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro j _
    have he := NormedSpace.expSeries_div_hasSum_exp (β * featureKernel φ i j)
    rw [← Real.exp_eq_exp_ℝ] at he
    exact (he.mul_left (c i)).mul_right (c j)
  exact ge_of_tendsto hsum.tendsto_sum_nat
    (Filter.Eventually.of_forall (fun N => Finset.sum_nonneg (fun m _ => hT m)))

def complexQuadratic (K : ι → ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (c i) * (K i j : ℂ) * c j

theorem complexQuadratic_re (K : ι → ι → ℝ) (c : ι → ℂ) :
    (complexQuadratic K c).re = realQuadratic K (fun i => (c i).re) +
      realQuadratic K (fun i => (c i).im) := by
  simp only [complexQuadratic, realQuadratic, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]

theorem complexQuadratic_im (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i) (c : ι → ℂ) :
    (complexQuadratic K c).im = 0 := by
  have hs : (∑ i, ∑ j, (c i).re * K i j * (c j).im) =
      ∑ i, ∑ j, (c i).im * K i j * (c j).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK j i]
    ring
  simp only [complexQuadratic, Complex.im_sum, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_zero, sub_zero, zero_add, neg_mul]
  simp only [← sub_eq_add_neg, Finset.sum_sub_distrib, hs, sub_self]

theorem exp_feature_complex_nonneg (φ : ι → D → ℝ) (c : ι → ℂ)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (complexQuadratic (fun i j => Real.exp (β * featureKernel φ i j)) c).re ∧
      (complexQuadratic (fun i j => Real.exp (β * featureKernel φ i j)) c).im = 0 := by
  constructor
  · rw [complexQuadratic_re]
    exact add_nonneg (exp_feature_quadratic_nonneg φ _ β hβ)
      (exp_feature_quadratic_nonneg φ _ β hβ)
  · apply complexQuadratic_im
    intro i j
    rw [featureKernel_symm φ i j]

variable {d : Type*} [Fintype d] [DecidableEq d]

def matrixFeatures (A : Matrix d d ℂ) : (d × d) ⊕ (d × d) → ℝ
  | Sum.inl p => (A p.1 p.2).re
  | Sum.inr p => (A p.1 p.2).im

omit [DecidableEq d] in
theorem real_trace_eq_featureKernel (A B : Matrix d d ℂ) :
    (Matrix.trace (Aᴴ * B)).re = featureKernel matrixFeatures A B := by
  simp only [featureKernel, Fintype.sum_sum_type, matrixFeatures, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (A j i).re * (B j i).re),
    Finset.sum_comm (f := fun i j => (A j i).im * (B j i).im)]

variable {G : Type*} [Group G]

def unitaryCharacter (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) : ℂ :=
  Matrix.trace (ρ g : Matrix d d ℂ)

def crossingKernel (ρ : G →* Matrix.unitaryGroup d ℂ) (β : ℝ) (x y : G) : ℝ :=
  Real.exp (β * (unitaryCharacter ρ (x⁻¹ * y)).re)

theorem crossingKernel_eq_exp_feature (ρ : G →* Matrix.unitaryGroup d ℂ)
    (β : ℝ) (x y : G) :
    crossingKernel ρ β x y = Real.exp (β * featureKernel
      (fun g => matrixFeatures (ρ g : Matrix d d ℂ)) x y) := by
  simp only [crossingKernel, unitaryCharacter, map_mul, map_inv, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose, real_trace_eq_featureKernel]
  rfl

/-- Genuine positive definiteness of the Wilson crossing kernel for arbitrary complex tests. -/
theorem crossingKernel_positive (ρ : G →* Matrix.unitaryGroup d ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (x : ι → G) (c : ι → ℂ) :
    0 ≤ (complexQuadratic (fun i j => crossingKernel ρ β (x i) (x j)) c).re ∧
      (complexQuadratic (fun i j => crossingKernel ρ β (x i) (x j)) c).im = 0 := by
  simp only [crossingKernel_eq_exp_feature]
  exact exp_feature_complex_nonneg (fun i => matrixFeatures (ρ (x i) : Matrix d d ℂ)) c β hβ

end
end UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
