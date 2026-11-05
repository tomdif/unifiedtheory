/- The positive semidefinite sesquilinear form of an arbitrary positive Gram
kernel. This is ordinary kernel positivity, not Osterwalder--Schrader
reflection positivity. -/
import UnifiedTheory.Clay.YangMills.ProbabilityGramCompactness
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveKernelForm
noncomputable section
open CountableCorrelationCompactness
open scoped BigOperators

structure PositiveKernel (ι : Type*) where
  value : ι × ι → ℂ
  positive : GramPositive (fun i j => (i, j)) value

variable {ι : Type*} (K : PositiveKernel ι)

theorem diagonal_im_zero (i : ι) : (K.value (i, i)).im = 0 := by
  simpa [gramValue, Fin.sum_univ_succ] using (K.positive 1 (fun _ => i) (fun _ => 1)).1

theorem kernel_hermitian (i j : ι) : star (K.value (j, i)) = K.value (i, j) := by
  have hd₁ := diagonal_im_zero K i
  have hd₂ := diagonal_im_zero K j
  have hs := (K.positive 2 ![i, j] ![1, 1]).1
  have hi := (K.positive 2 ![i, j] ![1, Complex.I]).1
  simp [gramValue, Fin.sum_univ_succ, Complex.mul_im] at hs hi
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

theorem positive_fintype {J : Type*} [Fintype J] (index : J → ι) (a : J → ℂ) :
    (∑ i, ∑ j, star (a i) * a j * K.value (index i, index j)).im = 0 ∧
    0 ≤ (∑ i, ∑ j, star (a i) * a j * K.value (index i, index j)).re := by
  let e := (Fintype.equivFin J).symm
  have h := K.positive (Fintype.card J) (fun i => index (e i)) (fun i => a (e i))
  have heq : gramValue (fun i j => (i, j)) K.value (Fintype.card J)
      (fun i => index (e i)) (fun i => a (e i)) =
      ∑ i, ∑ j, star (a i) * a j * K.value (index i, index j) := by
    unfold gramValue
    calc
      _ = ∑ i : Fin (Fintype.card J), ∑ j : J,
          star (a (e i)) * a j * K.value (index (e i), index j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact e.sum_comp (fun j => star (a (e i)) * a j * K.value (index (e i), index j))
      _ = _ := e.sum_comp (fun i : J => ∑ j : J,
        star (a i) * a j * K.value (index i, index j))
  rw [heq] at h
  exact h

def rawForm (x y : ι →₀ ℂ) : ℂ :=
  x.sum (fun i a => y.sum (fun j b => star a * b * K.value (i, j)))

theorem rawForm_nonneg (x : ι →₀ ℂ) : 0 ≤ (rawForm K x x).re := by
  classical
  have h := positive_fintype K (J := x.support) (fun i => i.val) (fun i => x i)
  have heq : (∑ i : x.support, ∑ j : x.support,
      star (x i) * x j * K.value (i, j)) = rawForm K x x := by
    unfold rawForm Finsupp.sum
    calc
      _ = ∑ i ∈ x.support, ∑ j : x.support, star (x i) * x j * K.value (i, j) :=
        x.support.sum_coe_sort (fun i => ∑ j : x.support, star (x i) * x j * K.value (i, j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact x.support.sum_coe_sort (fun j => star (x i) * x j * K.value (i, j))
  rw [heq] at h
  exact h.2

theorem rawForm_hermitian (x y : ι →₀ ℂ) : star (rawForm K y x) = rawForm K x y := by
  classical
  simp only [rawForm, Finsupp.sum, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [kernel_hermitian]
  ring

theorem rawForm_add_left (x y z : ι →₀ ℂ) :
    rawForm K (x + y) z = rawForm K x z + rawForm K y z := by
  classical
  unfold rawForm
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

theorem rawForm_smul_left (x y : ι →₀ ℂ) (c : ℂ) :
    rawForm K (c • x) y = star c * rawForm K x y := by
  classical
  unfold rawForm
  rw [Finsupp.sum_smul_index']
  · simp only [Finsupp.sum, smul_eq_mul, star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro i
    simp

@[simp] theorem rawForm_single_single (i j : ι) (a b : ℂ) :
    rawForm K (Finsupp.single i a) (Finsupp.single j b) = star a * b * K.value (i, j) := by
  simp [rawForm]

def preInnerCore : PreInnerProductSpace.Core ℂ (ι →₀ ℂ) where
  inner := rawForm K
  conj_inner_symm x y := rawForm_hermitian K x y
  re_inner_nonneg := rawForm_nonneg K
  add_left := rawForm_add_left K
  smul_left := rawForm_smul_left K

end
end UnifiedTheory.Clay.YangMills.PositiveKernelForm
