/- Positive finite kernels are closed under entrywise products,
exponentials and pointwise limits. Finite positive measures give actual
Fourier-Gram and compound-Poisson kernels, without a positivity premise
on their characteristic functions. -/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPositiveKernelExponential
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology BigOperators ComplexOrder Kronecker

variable {n : Type*} [Fintype n]

theorem schur_positive {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.PosSemidef (fun i j => A i j * B i j) := by
  simpa only [Matrix.submatrix_apply, Matrix.kronecker_apply] using
    (hA.kronecker hB).submatrix (fun i => (i,i))

theorem constant_one_positive : Matrix.PosSemidef (fun _ _ : n => (1 : ℂ)) := by
  simpa only [Matrix.vecMulVec, Pi.star_apply, star_one, one_mul] using
    Matrix.posSemidef_vecMulVec_star_self (fun _ : n => (1 : ℂ))

theorem schur_power_positive {A : Matrix n n ℂ} (hA : A.PosSemidef) (m : ℕ) :
    Matrix.PosSemidef (fun i j => A i j ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using (constant_one_positive (n := n))
  | succ m hm => simpa only [pow_succ] using schur_positive hm hA

theorem pointwise_limit_positive {ι : Type*} {l : Filter ι} [NeBot l]
    {A : ι → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hA : ∀ k, (A k).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun k => A k i j) l (𝓝 (B i j))) :
    B.PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    have ht := (Complex.continuous_conj.tendsto _).comp (hlim j i)
    simp only [Function.comp_def] at ht
    have he : (fun k => starRingEnd ℂ (A k j i)) = (fun k => A k i j) := by
      funext k
      exact (hA k).isHermitian.apply i j
    rw [he] at ht
    exact tendsto_nhds_unique ht (hlim i j)
  · intro c
    have ht : Tendsto (fun k => star c ⬝ᵥ ((A k) *ᵥ c)) l
        (𝓝 (star c ⬝ᵥ (B *ᵥ c))) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      exact tendsto_finset_sum _ (fun i _ =>
        (tendsto_finset_sum _ (fun j _ => (hlim i j).mul_const (c j))).const_mul _)
    exact ge_of_tendsto' ht (fun k => (hA k).dotProduct_mulVec_nonneg c)

theorem entrywise_exp_positive {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => Complex.exp (A i j)) := by
  classical
  let P (N : ℕ) : Matrix n n ℂ :=
    ∑ m ∈ Finset.range N, ((Nat.factorial m : ℝ)⁻¹) • (fun i j => A i j ^ m)
  apply pointwise_limit_positive (A := P) (l := atTop)
  · intro N
    exact Matrix.posSemidef_sum _ (fun m _ =>
      (schur_power_positive hA m).smul (by positivity : 0 ≤ (Nat.factorial m : ℝ)⁻¹))
  · intro i j
    have ht := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
    simpa only [P, Matrix.sum_apply, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm,
      Complex.exp_eq_exp_ℂ] using ht

theorem integral_positive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : X → Matrix n n ℂ) (hA : ∀ x, (A x).PosSemidef)
    (hi : ∀ i j, Integrable (fun x => A x i j) μ) :
    Matrix.PosSemidef (fun i j => ∫ x, A x i j ∂μ) := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    change starRingEnd ℂ (∫ x, A x j i ∂μ) = _
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hA x).isHermitian.apply i j)
  · intro c
    have he : star c ⬝ᵥ ((fun i j => ∫ x, A x i j ∂μ) *ᵥ c) =
        ∫ x, star c ⬝ᵥ ((A x) *ᵥ c) ∂μ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => (hi i j).mul_const (c j))).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, integral_finset_sum _ (fun j _ => (hi i j).mul_const (c j))]
      simp only [integral_mul_const]
    rw [he]
    exact integral_nonneg (fun x => (hA x).dotProduct_mulVec_nonneg c)

def phase (x t : ℝ) : ℂ := Complex.exp ((x*t : ℝ) * Complex.I)

theorem phase_difference (x y t : ℝ) :
    phase (y-x) t = starRingEnd ℂ (phase x t) * phase y t := by
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_mul]
  congr 1
  ring

theorem phase_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (phase x) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold phase; fun_prop)
  filter_upwards [] with t
  exact (Complex.norm_exp_ofReal_mul_I (x*t)).le

theorem fourier_gram_positive (μ : Measure ℝ) [IsFiniteMeasure μ] (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => ∫ t, phase (x j-x i) t ∂μ) := by
  apply integral_positive μ
  · intro t
    simpa only [phase_difference, Matrix.vecMulVec, Pi.star_apply] using
      Matrix.posSemidef_vecMulVec_star_self (fun i => phase (x i) t)
  · intro i j
    exact phase_integrable μ (x j-x i)

theorem compound_poisson_positive (μ : Measure ℝ) [IsFiniteMeasure μ] (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (∫ t, phase (x j-x i) t - 1 ∂μ)) := by
  have hp := (entrywise_exp_positive (fourier_gram_positive μ x)).smul
    (Real.exp_pos (-μ.real Set.univ)).le
  convert hp using 1
  funext i j
  rw [integral_sub (phase_integrable μ _) (integrable_const _), integral_const]
  simp only [Measure.real, Matrix.smul_apply, Complex.real_smul, mul_one,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_neg]
  congr 1
  ring

theorem compound_poisson_limit_positive (μ : ℕ → Measure ℝ)
    [∀ N, IsFiniteMeasure (μ N)] (L : ℝ → ℂ)
    (hlim : ∀ z, Tendsto (fun N => ∫ t, phase z t - 1 ∂μ N) atTop (𝓝 (L z)))
    (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (L (x j-x i))) := by
  apply pointwise_limit_positive
    (A := fun N i j => Complex.exp (∫ t, phase (x j-x i) t - 1 ∂μ N)) (l := atTop)
  · intro N
    exact compound_poisson_positive (μ N) x
  · intro i j
    exact (Complex.continuous_exp.tendsto _).comp (hlim (x j-x i))

#print axioms schur_positive
#print axioms constant_one_positive
#print axioms schur_power_positive
#print axioms pointwise_limit_positive
#print axioms entrywise_exp_positive
#print axioms integral_positive
#print axioms phase_difference
#print axioms phase_integrable
#print axioms fourier_gram_positive
#print axioms compound_poisson_positive
#print axioms compound_poisson_limit_positive
end
end UnifiedTheory.Audit.KFCausalPositiveKernelExponential
