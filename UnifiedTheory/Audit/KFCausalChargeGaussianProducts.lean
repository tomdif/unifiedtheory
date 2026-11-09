/- Actual L2 Gaussian factors for the standing-charge ground-state test.
The two-dimensional Fourier formula retains mathlib's 2*pi convention. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import UnifiedTheory.Audit.KFCausalGaussianSliceDomain
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeGaussianProducts
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates

theorem pi_product_memLp (n : ℕ) (f : Fin n → ℝ → ℂ)
    (hc : ∀ i, Continuous (f i)) (hf : ∀ i, MemLp (f i) 2 volume) :
    MemLp (fun x : Fin n → ℝ => ∏ i, f i (x i)) 2 volume := by
  have hm : Continuous (fun x : Fin n → ℝ => ∏ i, f i (x i)) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := Integrable.fintype_prod (fun i =>
    (memLp_two_iff_integrable_sq_norm (hf i).1).mp (hf i))
  simpa only [norm_prod,Finset.prod_pow] using hi

theorem block_product_memLp (n : ℕ) (f : Fin n → ℝ → ℂ)
    (hc : ∀ i, Continuous (f i)) (hf : ∀ i, MemLp (f i) 2 volume) :
    MemLp (fun x : Block n => ∏ i, f i (x i)) 2 volume :=
  (pi_product_memLp n f hc hf).comp_measurePreserving
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))

def gaussian (n : ℕ) (α : ℝ) (x : Block n) : ℂ :=
  Complex.exp (-(α:ℂ)*(‖x‖:ℂ)^2)

theorem gaussian_continuous (n : ℕ) (α : ℝ) : Continuous (gaussian n α) := by
  unfold gaussian
  fun_prop

theorem gaussian_norm (n : ℕ) (α : ℝ) (x : Block n) :
    ‖gaussian n α x‖ = Real.exp (-α*‖x‖^2) := by
  rw [gaussian,norm_cexp_neg_mul_sq]
  rfl

theorem gaussian_norm_square (n : ℕ) (α : ℝ) (x : Block n) :
    ‖gaussian n α x‖^2 = Real.exp (-(2*α)*‖x‖^2) := by
  rw [gaussian_norm,← Real.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem gaussian_integrable (n : ℕ) (α : ℝ) (hα : 0 < α) : Integrable (gaussian n α) := by
  unfold gaussian
  simpa using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := Block n) (b := (α:ℂ)) hα 0 (0 : Block n)

theorem gaussian_memLp (n : ℕ) (α : ℝ) (hα : 0 < α) : MemLp (gaussian n α) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (gaussian_continuous n α).aestronglyMeasurable).mpr
  simp_rw [gaussian_norm_square]
  simpa only [gaussian_norm] using
    (gaussian_integrable n (2*α) (by positivity)).norm

theorem gaussian_two_fourier (α : ℝ) (hα : 0 < α) (x : Block 2) :
    (𝓕 (gaussian 2 α)) x = ((Real.pi/α:ℝ):ℂ)*gaussian 2 (Real.pi^2/α) x := by
  change (𝓕 (fun v : Block 2 => Complex.exp (-(α:ℂ)*(‖v‖:ℂ)^2))) x = _
  rw [fourier_gaussian_innerProductSpace (b := (α:ℂ)) hα]
  simp only [finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat]
  norm_num only [div_self (by norm_num : (2:ℂ) ≠ 0),Complex.cpow_one]
  push_cast
  congr 1
  unfold gaussian
  congr 1
  push_cast
  ring

def spectator (α β : ℝ) (g : ℝ → ℂ) (x : Block 4) : ℂ :=
  g (x 0) * Complex.exp (-((α*((x 1)^2+(x 2)^2)+β*(x 3)^2:ℝ):ℂ))

theorem spectator_continuous (α β : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    Continuous (spectator α β g) := by
  unfold spectator
  fun_prop

theorem spectator_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (spectator α β g) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,
    KFCausalGaussianSliceDomain.gaussian (α:ℂ),
    KFCausalGaussianSliceDomain.gaussian (α:ℂ),
    KFCausalGaussianSliceDomain.gaussian (β:ℂ)]
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact hc
    all_goals exact KFCausalGaussianSliceDomain.gaussian_continuous _
  have hfm : ∀ i, MemLp (f i) 2 volume := by
    intro i
    fin_cases i
    · exact hg
    · exact (KFCausalGaussianSliceDomain.gaussian_memLp_iff _).mpr hα
    · exact (KFCausalGaussianSliceDomain.gaussian_memLp_iff _).mpr hα
    · exact (KFCausalGaussianSliceDomain.gaussian_memLp_iff _).mpr hβ
  have he : spectator α β g = (fun x : Block 4 => ∏ i, f i (x i)) := by
    funext x
    simp only [spectator,f,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.prod_univ_zero,mul_one,KFCausalGaussianSliceDomain.gaussian]
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  rw [he]
  exact block_product_memLp 4 f hfc hfm

#print axioms pi_product_memLp
#print axioms block_product_memLp
#print axioms gaussian_continuous
#print axioms gaussian_norm
#print axioms gaussian_norm_square
#print axioms gaussian_integrable
#print axioms gaussian_memLp
#print axioms gaussian_two_fourier
#print axioms spectator_continuous
#print axioms spectator_memLp

end
end UnifiedTheory.Audit.KFCausalChargeGaussianProducts
