/- Concrete finite occupation ladders, including the capacity boundary.
The ambient box includes inert states above total occupation R; the
active simplex N<=R is exactly the numerical model's occupation basis. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
noncomputable section
open Matrix
open scoped BigOperators

def Occupation (m R : ℕ) := Fin m → Fin (R+1)
instance (m R : ℕ) : Fintype (Occupation m R) := inferInstanceAs (Fintype (Fin m → Fin (R+1)))
instance (m R : ℕ) : DecidableEq (Occupation m R) := inferInstanceAs (DecidableEq (Fin m → Fin (R+1)))

def total {m R : ℕ} (v : Occupation m R) : ℕ := ∑ a, (v a : ℕ)
def weight (R : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ := if n ≤ R then r n else 0

def lower {m R : ℕ} (a : Fin m) (v : Occupation m R) : Occupation m R :=
  Function.update v a ⟨(v a : ℕ)-1, lt_of_le_of_lt (Nat.sub_le _ _) (v a).isLt⟩

def raise {m R : ℕ} (a : Fin m) (v : Occupation m R) (h : (v a : ℕ)<R) : Occupation m R :=
  Function.update v a ⟨(v a : ℕ)+1, by omega⟩

theorem coordinate_le_total {m R : ℕ} (v : Occupation m R) (a : Fin m) :
    (v a : ℕ) ≤ total v := by
  exact Finset.single_le_sum (f := fun b => (v b : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem lower_injective_active {m R : ℕ} (a : Fin m) (u v : Occupation m R)
    (hu : 0 < (u a : ℕ)) (hv : 0 < (v a : ℕ)) (he : lower a u=lower a v) : u=v := by
  funext b
  have hh := congrFun he b
  by_cases hb : b=a
  · subst b
    simp only [lower, Function.update_self] at hh
    have hn := congrArg Fin.val hh
    apply Fin.ext
    dsimp at hn
    omega
  · simpa [lower, Function.update_of_ne hb] using hh

theorem lower_raise {m R : ℕ} (a : Fin m) (v : Occupation m R) (h : (v a : ℕ)<R) :
    lower a (raise a v h)=v := by
  funext b
  by_cases hb : b=a
  · subst b; apply Fin.ext; simp [lower, raise]
  · simp [lower, raise, Function.update_of_ne hb]

theorem total_raise {m R : ℕ} (a : Fin m) (v : Occupation m R) (h : (v a : ℕ)<R) :
    total (raise a v h)=total v+1 := by
  unfold total raise
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ a)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ a) (f := fun b => (v b : ℕ))]
  simp only [Function.update_self]
  have he : (∑ b ∈ Finset.univ \ {a}, ((Function.update v a ⟨(v a : ℕ)+1, by omega⟩) b : ℕ)) =
      ∑ b ∈ Finset.univ \ {a}, (v b : ℕ) := by
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := by simpa using (Finset.mem_sdiff.mp hb).2
    simp [Function.update_of_ne hba]
  rw [he]
  omega

def amplitude {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) (v : Occupation m R) : ℝ :=
  Real.sqrt (v a : ℝ)*weight R r (total v)

def annihilator {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    Matrix (Occupation m R) (Occupation m R) ℂ :=
  fun i j => if 0 < (j a : ℕ) ∧ i=lower a j then (amplitude r a j : ℂ) else 0

theorem amplitude_square {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) (v : Occupation m R) :
    amplitude r a v ^ 2 = (v a : ℝ) * weight R r (total v)^2 := by
  rw [amplitude, mul_pow, Real.sq_sqrt (by positivity)]

theorem annihilator_adjoint_square {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    (annihilator (R := R) r a)ᴴ*annihilator r a =
      Matrix.diagonal (fun v => (((v a : ℝ)*weight R r (total v)^2 : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i=j
  · subst j
    by_cases hi : 0 < (i a : ℕ)
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_eq_single (lower a i)]
      · simp [annihilator, hi, amplitude]
        norm_cast
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (i a : ℝ) by positivity)]
      · intro b _ hb
        simp only [annihilator, if_neg (show ¬(0 < (i a : ℕ) ∧ b=lower a i) by tauto),
          mul_zero]
      · simp
    · have hz : (i a : ℕ)=0 := by omega
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, annihilator, hz]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hi : 0 < (i a : ℕ) ∧ b=lower a i
    · have hn : ¬(0 < (j a : ℕ) ∧ b=lower a j) := by
        intro hj
        exact hij (lower_injective_active a i j hi.1 hj.1 (hi.2.symm.trans hj.2))
      simp only [Matrix.conjTranspose_apply, annihilator, if_neg hn, mul_zero]
    · simp only [Matrix.conjTranspose_apply, annihilator, if_neg hi, star_zero, zero_mul]

theorem annihilator_square_adjoint {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    annihilator (R := R) r a*(annihilator r a)ᴴ =
      Matrix.diagonal (fun v => ((((v a : ℝ)+1)*weight R r (total v+1)^2 : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i=j
  · subst j
    by_cases hi : (i a : ℕ)<R
    · let u := raise a i hi
      have hu : 0 < (u a : ℕ) := by simp [u, raise]
      have hlu : lower a u=i := lower_raise a i hi
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_eq_single u]
      · have ht : total u = total i+1 := total_raise a i hi
        have hv : (u a : ℕ) = (i a : ℕ)+1 := by simp [u, raise]
        have hstep : 0 < (u a : ℕ) ∧ i=lower a u := ⟨hu, hlu.symm⟩
        simp only [annihilator, if_pos hstep, Matrix.diagonal_apply_eq,
          Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1
        simpa [pow_two, ht, hv] using amplitude_square r a u
      · intro b _ hb
        have hn : ¬(0 < (b a : ℕ) ∧ i=lower a b) := by
          intro h
          exact hb (lower_injective_active a b u h.1 hu (h.2.symm.trans hlu.symm))
        simp only [annihilator, if_neg hn, zero_mul]
      · simp
    · have htop : (i a : ℕ)=R := by have := (i a).isLt; omega
      have hw : weight R r (total i+1)=0 := by
        have := coordinate_le_total i a
        simp [weight, show ¬total i+1 ≤ R by omega]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Matrix.diagonal_apply_eq]
      simp only [hw, zero_pow (by omega : 2 ≠ 0), mul_zero, Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro b _
      have hn : ¬(0 < (b a : ℕ) ∧ i=lower a b) := by
        intro h
        have he := congrArg (fun v => (v a : ℕ)) h.2
        simp [lower, htop] at he
        have := (b a).isLt
        omega
      simp only [annihilator, if_neg hn, zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hi : 0 < (b a : ℕ) ∧ i=lower a b
    · have hn : ¬(0 < (b a : ℕ) ∧ j=lower a b) := by
        intro hj; exact hij (hi.2.trans hj.2.symm)
      simp only [Matrix.conjTranspose_apply, annihilator, if_neg hn, star_zero, mul_zero]
    · simp only [Matrix.conjTranspose_apply, annihilator, if_neg hi, zero_mul]

theorem total_lower_le {m R : ℕ} (a : Fin m) (v : Occupation m R) :
    total (lower a v) ≤ total v := by
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : b=a
  · subst b; simp [lower]
  · simp [lower,Function.update_of_ne hb]

/-- Rows and columns beyond the retained simplex are identically zero.
Thus the box representation adds only an inert direct summand. -/
theorem annihilator_outside {m R : ℕ} (r : ℕ → ℝ) (a : Fin m)
    (i j : Occupation m R) (h : R < total i ∨ R < total j) : annihilator r a i j=0 := by
  by_cases he : 0 < (j a : ℕ) ∧ i=lower a j
  · have hj : R < total j := by
      rcases h with h|h
      · have hh := total_lower_le a j
        rw [← he.2] at hh
        omega
      · exact h
    simp [annihilator,amplitude,weight,show ¬total j ≤ R by omega]
  · exact if_neg he

def activeProjection (m R : ℕ) : Matrix (Occupation m R) (Occupation m R) ℂ :=
  Matrix.diagonal (fun v => if total v ≤ R then 1 else 0)

theorem annihilator_supported {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    activeProjection m R*annihilator r a*activeProjection m R=annihilator r a := by
  ext i j
  simp only [activeProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : total i ≤ R <;> by_cases hj : total j ≤ R
  · simp [hi,hj]
  · simp [hi,hj,annihilator_outside r a i j (Or.inr (by omega))]
  · simp [hi,hj,annihilator_outside r a i j (Or.inl (by omega))]
  · simp [hi,hj,annihilator_outside r a i j (Or.inl (by omega))]

abbrev Active (m R : ℕ) := {v : Occupation m R // total v ≤ R}

def compress {m R : ℕ} (A : Matrix (Occupation m R) (Occupation m R) ℂ) :
    Matrix (Active m R) (Active m R) ℂ := A.submatrix Subtype.val Subtype.val

theorem compress_mul {m R : ℕ} (A B : Matrix (Occupation m R) (Occupation m R) ℂ)
    (hA : ∀ i j, R < total j → A i j=0) : compress (A*B)=compress A*compress B := by
  ext i j
  exact Finset.sum_congr_set {v : Occupation m R | total v ≤ R}
    (fun k => A i.val k*B k j.val) (fun k => A i.val k.val*B k.val j.val)
    (fun _ _ => rfl) (by intro k hk; simp [hA _ k (by simpa using hk)])

theorem compress_adjoint {m R : ℕ} (A : Matrix (Occupation m R) (Occupation m R) ℂ) :
    compress Aᴴ=(compress A)ᴴ := rfl

theorem compress_diagonal {m R : ℕ} (f : Occupation m R → ℂ) :
    compress (Matrix.diagonal f)=Matrix.diagonal (fun v : Active m R => f v.val) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [compress]
  · have hn : i.val ≠ j.val := fun he => h (Subtype.ext he)
    simp [compress,h,hn]

/-- The two products also hold on precisely the retained N<=R space. -/
theorem active_adjoint_square {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    (compress (annihilator (R := R) r a))ᴴ*compress (annihilator r a)=
      Matrix.diagonal (fun v : Active m R => (((v.val a : ℝ)*weight R r (total v.val)^2 : ℝ) : ℂ)) := by
  rw [← compress_adjoint, ← compress_mul]
  · rw [annihilator_adjoint_square,compress_diagonal]
  · intro i j hj
    simp [Matrix.conjTranspose_apply,annihilator_outside r a j i (Or.inl hj)]

theorem active_square_adjoint {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    compress (annihilator (R := R) r a)*(compress (annihilator r a))ᴴ=
      Matrix.diagonal (fun v : Active m R => ((((v.val a : ℝ)+1)*weight R r (total v.val+1)^2 : ℝ) : ℂ)) := by
  rw [← compress_adjoint, ← compress_mul]
  · rw [annihilator_square_adjoint,compress_diagonal]
  · intro i j hj
    exact annihilator_outside r a i j (Or.inr hj)

#print axioms active_adjoint_square
#print axioms active_square_adjoint
#print axioms annihilator_outside
#print axioms annihilator_supported
#print axioms annihilator_adjoint_square
#print axioms annihilator_square_adjoint

end
end UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
