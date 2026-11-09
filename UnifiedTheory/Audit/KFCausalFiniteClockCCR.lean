/- Exact finite clock commutators, with the capacity boundary retained.
The expectation estimates are state-dependent. Their large-capacity use
requires occupation moments to be controlled by the dynamics. -/
import UnifiedTheory.Audit.KFCausalConcreteClockConstraint
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFiniteClockCCR
noncomputable section
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalGradedSpinSource

def bracketCoefficient {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) (v : Active m R) : ℝ :=
  ((v.val a : ℝ)+1)*weight R r (total v.val+1)^2-
    (v.val a : ℝ)*weight R r (total v.val)^2

theorem ladder_bracket {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) :
    compress (annihilator (R := R) r a)*(compress (annihilator r a))ᴴ-
      (compress (annihilator r a))ᴴ*compress (annihilator r a)=
        diagonal (fun v => (bracketCoefficient r a v : ℂ)) := by
  rw [active_square_adjoint,active_adjoint_square,diagonal_sub]
  congr 1
  funext v
  simp [bracketCoefficient]

def bareWeight (R N : ℕ) : ℝ := Real.sqrt (1-((N : ℝ)-1)/(R : ℝ))

theorem bare_weight_square (R N : ℕ) (hR : 0 < R) (hN : N ≤ R+1) :
    weight R (bareWeight R) N^2=1-((N : ℝ)-1)/(R : ℝ) := by
  have hr : (0 : ℝ)<R := by exact_mod_cast hR
  by_cases h : N ≤ R
  · rw [weight,if_pos h,bareWeight,Real.sq_sqrt]
    have hn : (N : ℝ) ≤ R+1 := by exact_mod_cast hN
    exact sub_nonneg.mpr ((div_le_one hr).mpr (by linarith))
  · have hn : N=R+1 := by omega
    subst N
    simp only [weight,if_neg (by omega : ¬R+1 ≤ R),zero_pow (by decide : 2 ≠ 0)]
    push_cast
    field_simp
    ring

theorem bare_bracket_coefficient {m R : ℕ} (a : Fin m) (v : Active m R) (hR : 0 < R) :
    bracketCoefficient (bareWeight R) a v=
      1-((total v.val : ℝ)+(v.val a : ℝ))/(R : ℝ) := by
  unfold bracketCoefficient
  rw [bare_weight_square R _ hR (by have := v.property; omega),
    bare_weight_square R _ hR (by have := v.property; omega)]
  push_cast
  ring

theorem exact_bracket_coefficient {m R : ℕ} (a : Fin m) (v : Active m R) :
    bracketCoefficient (fun _ => 1) a v=
      1-(if total v.val=R then (v.val a : ℝ)+1 else 0) := by
  have hn := v.property
  by_cases ht : total v.val=R
  · simp [bracketCoefficient,weight,ht]
  · have hlt : total v.val+1 ≤ R := by omega
    simp [bracketCoefficient,weight,hn,hlt,ht]

/-- This is the commutator of the clock matrices already used in the
specified Hamiltonian, for arbitrary radial weights. -/
theorem concrete_clock_bracket (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    clockS R r hbar*clockPs R r hbar-clockPs R r hbar*clockS R r hbar=
      (Complex.I*(hbar : ℂ)) • diagonal (fun v : State R => (bracketCoefficient r 0 v : ℂ)) := by
  have hs : (Real.sqrt (hbar/2) : ℂ)^2=(hbar/2 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have hid (A : Matrix (State R) (State R) ℂ) :
      (A+Aᴴ)*(A-Aᴴ)-(A-Aᴴ)*(A+Aᴴ)=(-2 : ℂ) • (A*Aᴴ-Aᴴ*A) := by
    simp only [add_mul,mul_add,sub_mul,mul_sub]
    module
  unfold clockS clockPs skew
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [show (Real.sqrt (hbar/2) : ℂ)*((Real.sqrt (hbar/2) : ℂ)* -Complex.I)=
      -Complex.I*(hbar/2) by rw [← mul_assoc,← pow_two,hs]; ring,
    show ((Real.sqrt (hbar/2) : ℂ)* -Complex.I)*(Real.sqrt (hbar/2) : ℂ)=
      -Complex.I*(hbar/2) by
        calc
          _ = -Complex.I*(Real.sqrt (hbar/2) : ℂ)^2 := by ring
          _ = _ := by rw [hs]]
  rw [← smul_sub,hid,smul_smul]
  rw [show (-Complex.I*(hbar/2))*(-2)=Complex.I*hbar by ring]
  exact congrArg (fun X => (Complex.I*(hbar : ℂ)) • X) (ladder_bracket r (0 : Fin 6))

def moment {m R : ℕ} (k : ℕ) (ψ : Active m R → ℂ) : ℝ :=
  ∑ v, (total v.val : ℝ)^k*‖ψ v‖^2

def expectationDefect {m R : ℕ} (r : ℕ → ℝ) (a : Fin m) (ψ : Active m R → ℂ) : ℝ :=
  ∑ v, (1-bracketCoefficient r a v)*‖ψ v‖^2

/-- The real defect above is exactly the matrix expectation of
I-[a,a†], including arbitrary unnormalized state vectors. -/
theorem defect_is_matrix_expectation {m R : ℕ} (r : ℕ → ℝ) (a : Fin m)
    (ψ : Active m R → ℂ) :
    (∑ v, star (ψ v)*(((1 : Matrix (Active m R) (Active m R) ℂ)-
      (compress (annihilator r a)*(compress (annihilator r a))ᴴ-
      (compress (annihilator r a))ᴴ*compress (annihilator r a))).mulVec ψ) v)=
        (expectationDefect r a ψ : ℂ) := by
  rw [ladder_bracket]
  have hd : (1 : Matrix (Active m R) (Active m R) ℂ)-
      diagonal (fun v => (bracketCoefficient r a v : ℂ))=
      diagonal (fun v => (1-bracketCoefficient r a v : ℂ)) := by
    ext i j
    by_cases h : i=j <;> simp [h]
  rw [hd]
  simp only [Matrix.mulVec_diagonal]
  unfold expectationDefect
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  rw [show star (ψ v)*((1-(bracketCoefficient r a v : ℂ))*ψ v)=
      (1-(bracketCoefficient r a v : ℂ))*(ψ v*star (ψ v)) by ring,
    Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem bare_defect_bound {m R : ℕ} (a : Fin m) (ψ : Active m R → ℂ) (hR : 0 < R) :
    0 ≤ expectationDefect (bareWeight R) a ψ ∧
      expectationDefect (bareWeight R) a ψ ≤ 2*moment 1 ψ/(R : ℝ) := by
  have hr : (0 : ℝ)<R := by exact_mod_cast hR
  constructor
  · apply Finset.sum_nonneg
    intro v _
    rw [bare_bracket_coefficient a v hR]
    ring_nf
    positivity
  · unfold expectationDefect moment
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_le_sum
    intro v _
    rw [bare_bracket_coefficient a v hR]
    have hn : (v.val a : ℝ) ≤ total v.val := by exact_mod_cast coordinate_le_total v.val a
    have he : 1-(1-((total v.val : ℝ)+(v.val a : ℝ))/(R : ℝ))=
        ((total v.val : ℝ)+(v.val a : ℝ))/(R : ℝ) := by ring
    rw [he]
    calc
      _ ≤ (2*(total v.val : ℝ)/(R : ℝ))*‖ψ v‖^2 := by gcongr; linarith
      _ = _ := by simp only [pow_one]; ring

theorem exact_defect_bound {m R : ℕ} (a : Fin m) (ψ : Active m R → ℂ) (hR : 0 < R) :
    0 ≤ expectationDefect (fun _ => 1) a ψ ∧
      expectationDefect (fun _ => 1) a ψ ≤ 2*moment 2 ψ/(R : ℝ) := by
  have hr : (0 : ℝ)<R := by exact_mod_cast hR
  have hr1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  constructor
  · apply Finset.sum_nonneg
    intro v _
    rw [exact_bracket_coefficient]
    split_ifs <;> ring_nf <;> positivity
  · unfold expectationDefect moment
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_le_sum
    intro v _
    rw [exact_bracket_coefficient]
    by_cases ht : total v.val=R
    · rw [if_pos ht]
      have hn : (v.val a : ℝ) ≤ R := by
        exact_mod_cast (coordinate_le_total v.val a).trans v.property
      have he : (2*((total v.val : ℝ)^2*‖ψ v‖^2))/(R : ℝ)=2*(R : ℝ)*‖ψ v‖^2 := by
        rw [ht]; field_simp
      rw [he]
      have hh : 1-(1-((v.val a : ℝ)+1)) ≤ 2*(R : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    · rw [if_neg ht]
      simp only [sub_zero,sub_self,zero_mul]
      positivity

/-- The exact compensation is canonical on states strictly below the
capacity boundary. This is a matrix-state statement, not a CCR axiom. -/
theorem exact_defect_zero_below_boundary {m R : ℕ} (a : Fin m) (ψ : Active m R → ℂ)
    (hψ : ∀ v, total v.val=R → ψ v=0) : expectationDefect (fun _ => 1) a ψ=0 := by
  apply Finset.sum_eq_zero
  intro v _
  rw [exact_bracket_coefficient]
  by_cases ht : total v.val=R
  · simp [ht,hψ v ht]
  · simp [ht]

/-- This is conditional on a uniform moment bound. It does not assume
that dilution at the initial time is preserved by the Hamiltonian. -/
theorem bare_defect_tendsto_zero (m : ℕ) (a : Fin m)
    (ψ : ∀ R : ℕ, Active m (R+1) → ℂ) (C : ℝ)
    (hC : ∀ R, moment 1 (ψ R) ≤ C) :
    Tendsto (fun R => expectationDefect (bareWeight (R+1)) a (ψ R)) atTop (𝓝 0) := by
  have hl : Tendsto (fun R : ℕ => 2*C/((R+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (2*C))
  apply squeeze_zero (fun R => (bare_defect_bound a (ψ R) (by omega)).1) _ hl
  intro R
  apply (bare_defect_bound a (ψ R) (by omega)).2.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hC R) (by norm_num)) (by positivity)

theorem exact_defect_tendsto_zero (m : ℕ) (a : Fin m)
    (ψ : ∀ R : ℕ, Active m (R+1) → ℂ) (C : ℝ)
    (hC : ∀ R, moment 2 (ψ R) ≤ C) :
    Tendsto (fun R => expectationDefect (fun _ => 1) a (ψ R)) atTop (𝓝 0) := by
  have hl : Tendsto (fun R : ℕ => 2*C/((R+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (2*C))
  apply squeeze_zero (fun R => (exact_defect_bound a (ψ R) (by omega)).1) _ hl
  intro R
  apply (exact_defect_bound a (ψ R) (by omega)).2.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hC R) (by norm_num)) (by positivity)

#print axioms ladder_bracket
#print axioms bare_bracket_coefficient
#print axioms exact_bracket_coefficient
#print axioms concrete_clock_bracket
#print axioms defect_is_matrix_expectation
#print axioms bare_defect_bound
#print axioms exact_defect_bound
#print axioms exact_defect_zero_below_boundary
#print axioms bare_defect_tendsto_zero
#print axioms exact_defect_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalFiniteClockCCR
