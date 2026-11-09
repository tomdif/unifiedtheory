/- Finite averages retain the exact L2 multiplier representatives.
These elementary identities allow cancellation before taking norms. -/
import UnifiedTheory.Audit.KFCausalUnitaryMultiplierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
noncomputable section
open MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mean (N : ℕ) (f : ℕ → E) : E := (N:ℂ)⁻¹ • ∑ j ∈ Finset.range N, f j

theorem mean_const (N : ℕ) (hN : 0 < N) (x : E) : mean N (fun _ => x) = x := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mean,Finset.sum_const,Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem mean_sub (N : ℕ) (f g : ℕ → E) : mean N (fun j => f j-g j) = mean N f-mean N g := by
  simp only [mean,Finset.sum_sub_distrib,smul_sub]

theorem mean_add (N : ℕ) (f g : ℕ → E) : mean N (fun j => f j+g j) = mean N f+mean N g := by
  simp only [mean,Finset.sum_add_distrib,smul_add]

theorem mean_mul_left (N : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    mean N (fun j => c*f j) = c*mean N f := by
  simp only [mean,smul_eq_mul,← Finset.mul_sum]
  ring

theorem mean_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →ₗ[ℂ] F) (N : ℕ) (f : ℕ → E) : L (mean N f) = mean N (fun j => L (f j)) := by
  simp only [mean,map_smul,map_sum]

theorem mean_inner_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (x : H) (f : ℕ → H) :
    mean N (fun j => inner ℂ x (f j)) = inner ℂ x (mean N f) := by
  simp only [mean,inner_smul_right,inner_sum,smul_eq_mul]

theorem mean_inner_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (f : ℕ → H) (x : H) :
    mean N (fun j => inner ℂ (f j) x) = inner ℂ (mean N f) x := by
  simp only [mean,inner_smul_left,sum_inner,smul_eq_mul,map_inv₀,map_natCast]

theorem mean_norm_le (N : ℕ) (hN : 0 < N) (f : ℕ → E) (B : ℝ)
    (hf : ∀ j ∈ Finset.range N, ‖f j‖ ≤ B) : ‖mean N f‖ ≤ B := by
  have hs : ‖∑ j ∈ Finset.range N, f j‖ ≤ (N:ℝ)*B := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hf).trans_eq (by simp))
  rw [mean,norm_smul,norm_inv,Complex.norm_natCast]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by field_simp)

theorem operator_mean_apply (N : ℕ) (M : ℕ → E →L[ℂ] E) (f : E) :
    mean N M f = mean N (fun j => M j f) := by
  simp only [mean,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [NormedSpace ℂ E] in
theorem sum_representation (f : ℕ → Lp E 2 μ) (g : ℕ → X → E)
    (hg : ∀ j, f j =ᵐ[μ] g j) (S : Finset ℕ) :
    (∑ j ∈ S, f j : Lp E 2 μ) =ᵐ[μ] fun x => ∑ j ∈ S, g j x := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero E 2 μ
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ S, f j),hg i,ih] with x ha hf hs
    rw [ha]
    simp only [Pi.add_apply,hf,hs,Finset.sum_insert hi]

theorem mean_representation (N : ℕ) (f : ℕ → Lp E 2 μ) (g : ℕ → X → E)
    (hg : ∀ j, f j =ᵐ[μ] g j) :
    (mean N f : Lp E 2 μ) =ᵐ[μ] fun x => (N:ℂ)⁻¹ • ∑ j ∈ Finset.range N, g j x := by
  unfold mean
  filter_upwards [Lp.coeFn_smul (N:ℂ)⁻¹ (∑ j ∈ Finset.range N, f j),
    sum_representation f g hg (Finset.range N)] with x hc hs
  rw [hc]
  simp only [Pi.smul_apply,hs]

theorem isometry_mean_representation (U : E ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (N : ℕ) (f : ℕ → E) (g : ℕ → X → ℂ) (hg : ∀ j, U (f j) =ᵐ[μ] g j) :
    U (mean N f) =ᵐ[μ] fun x => (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N, g j x := by
  rw [mean,map_smul,map_sum]
  exact mean_representation N (fun j => U (f j)) g hg

#print axioms mean_const
#print axioms mean_sub
#print axioms mean_add
#print axioms mean_mul_left
#print axioms mean_map
#print axioms mean_inner_right
#print axioms mean_inner_left
#print axioms mean_norm_le
#print axioms operator_mean_apply
#print axioms sum_representation
#print axioms mean_representation
#print axioms isometry_mean_representation

end
end UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
