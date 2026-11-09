/- The normalized, shifted physicists' Hermite multipliers form a basis
of the entire finite complex polynomial space at every positive width.
Thus all finite Hermite superpositions exhaust the polynomial trial
family; this is not completeness in an operator graph norm. -/
import UnifiedTheory.Audit.KFCausalHermitePolynomials
import Mathlib.Algebra.Polynomial.Sequence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralHermiteBasis
noncomputable section
open Polynomial
open UnifiedTheory.Audit.KFCausalNeutralHermiteDomain (physicistsHermite multiplier)

theorem physicistsHermite_degree (n : ℕ) : (physicistsHermite n).degree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [physicistsHermite]
  | one => simp [physicistsHermite]
  | more n hn hn1 =>
    have htop : (C 2*X*physicistsHermite (n+1)).degree = (↑(n+2):WithBot ℕ) := by
      rw [mul_assoc,degree_C_mul (by norm_num : (2:ℂ) ≠ 0),degree_mul,degree_X,hn1]
      norm_cast
      omega
    have hlow : (C (2*((n+1:ℕ):ℂ))*physicistsHermite n).degree = n := by
      rw [degree_C_mul (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))),hn]
    rw [KFCausalNeutralHermiteDomain.physicistsHermite_recurrence,
      degree_sub_eq_left_of_degree_lt (by rw [hlow,htop]; exact_mod_cast (by omega : n<n+2))]
    exact htop

theorem multiplier_degree (w B : ℝ) (hw : 0 < w) (n : ℕ) :
    (multiplier w B n).degree = n := by
  have hd : (C (Real.sqrt (2*w):ℂ)*(X-C (B:ℂ))).degree = 1 := by
    rw [degree_C_mul (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne')]
    simp
  unfold multiplier
  rw [degree_C_mul (inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.2 (by positivity : 0 < (2:ℝ)^n*n.factorial)).ne')),
    degree_comp (by rw [hd]; norm_num),physicistsHermite_degree,hd,mul_one]

def sequence (w B : ℝ) (hw : 0 < w) : Polynomial.Sequence ℂ where
  elems' := multiplier w B
  degree_eq' := multiplier_degree w B hw

def hermiteBasis (w B : ℝ) (hw : 0 < w) : Module.Basis ℕ ℂ (Polynomial ℂ) :=
  (sequence w B hw).basis (fun n =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((sequence w B hw).ne_zero n)))

theorem hermiteBasis_apply (w B : ℝ) (hw : 0 < w) (n : ℕ) :
    hermiteBasis w B hw n = multiplier w B n :=
  (sequence w B hw).basis_eq_self _ n

theorem multiplier_linearIndependent (w B : ℝ) (hw : 0 < w) :
    LinearIndependent ℂ (multiplier w B) :=
  (sequence w B hw).linearIndependent

theorem multiplier_span (w B : ℝ) (hw : 0 < w) :
    Submodule.span ℂ (Set.range (multiplier w B)) = ⊤ :=
  (sequence w B hw).span (fun n =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((sequence w B hw).ne_zero n)))

def expansion (w B : ℝ) (S : Finset ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ i ∈ S, c i • multiplier w B i

theorem exists_expansion (w B : ℝ) (hw : 0 < w) (P : Polynomial ℂ) :
    ∃ S : Finset ℕ, ∃ c : ℕ → ℂ, P = expansion w B S c := by
  let v := (hermiteBasis w B hw).repr P
  refine ⟨v.support,v,?_⟩
  have he := (hermiteBasis w B hw).linearCombination_repr P
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum,hermiteBasis_apply] using he.symm

theorem exists_truncation (w B : ℝ) (hw : 0 < w) (P : Polynomial ℂ) :
    ∃ N : ℕ, ∃ c : ℕ → ℂ, P = expansion w B (Finset.range N) c := by
  classical
  obtain ⟨S,c,hP⟩ := exists_expansion w B hw P
  let N := S.sup id+1
  let d : ℕ → ℂ := fun i => if i ∈ S then c i else 0
  have hs : S ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  refine ⟨N,d,?_⟩
  rw [hP]
  unfold expansion
  calc
    _ = ∑ i ∈ S, d i • multiplier w B i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [d,hi]
    _ = _ := Finset.sum_subset hs (fun i _ hi => by simp [d,hi])

#print axioms physicistsHermite_degree
#print axioms multiplier_degree
#print axioms hermiteBasis_apply
#print axioms multiplier_linearIndependent
#print axioms multiplier_span
#print axioms exists_expansion
#print axioms exists_truncation
end
end UnifiedTheory.Audit.KFCausalNeutralHermiteBasis
