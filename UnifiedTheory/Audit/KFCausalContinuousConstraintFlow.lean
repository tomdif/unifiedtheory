/- Exact conservation along differentiable, time-dependent finite quantum
propagators. This is independent of an exponential time-stepping scheme.
Existence of the supplied propagator is a separate analytic obligation. -/
import UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalContinuousConstraintFlow
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- H may depend on time arbitrarily; only its value at the derivative
point enters the Heisenberg conservation identity. -/
theorem conserved_operator_derivative (H P : M) (hH : H.IsHermitian)
    (hP : Commute H P) (omega : ℝ) (U : ℝ → M) (t : ℝ)
    (hU : HasDerivAt U ((-Complex.I*(omega : ℂ)) • (H*U t)) t) :
    HasDerivAt (fun s => (U s)ᴴ*P*U s) 0 t := by
  have hd := (hU.star.mul_const P).mul hU
  convert hd using 1
  simp only [star_eq_conjTranspose,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
    hH.eq,Complex.star_def,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg,
    smul_mul_assoc,mul_smul_comm]
  rw [show (U t)ᴴ*P*(H*U t)=(U t)ᴴ*H*P*U t by
    simpa only [mul_assoc] using congrArg (fun A => (U t)ᴴ*(A*U t)) hP.eq.symm]
  module

/-- Exact conservation for a global differentiable propagator. No
commutation between Hamiltonians at different times is assumed. -/
theorem conserved_operator (H : ℝ → M) (P : M) (hH : ∀ t, (H t).IsHermitian)
    (hP : ∀ t, Commute (H t) P) (omega : ℝ) (U : ℝ → M)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (H t*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) : (U t)ᴴ*P*U t=P := by
  have hd (s : ℝ) := conserved_operator_derivative (H s) P (hH s) (hP s) omega U s (hU s)
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t t₀
  simpa [hinit] using he

theorem propagator_unitary (H : ℝ → M) (hH : ∀ t, (H t).IsHermitian)
    (omega : ℝ) (U : ℝ → M)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (H t*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) : (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1 := by
  have h := conserved_operator H 1 hH (fun s => Commute.one_right (H s)) omega U hU t₀ t hinit
  simp only [mul_one] at h
  exact ⟨h,mul_eq_one_comm.mp h⟩

theorem propagator_commutes (H : ℝ → M) (P : M) (hH : ∀ t, (H t).IsHermitian)
    (hP : ∀ t, Commute (H t) P) (omega : ℝ) (U : ℝ → M)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (H t*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) : Commute (U t) P := by
  have hp := conserved_operator H P hH hP omega U hU t₀ t hinit
  have hu := (propagator_unitary H hH omega U hU t₀ t hinit).2
  have he := congrArg (fun A => U t*A) hp
  simpa only [← mul_assoc,hu,one_mul] using he.symm

/-- The zero-charge sector is invariant under the exact time-dependent
Schrodinger equation, along every supplied global differentiable flow. -/
theorem physical_sector_continuous (q : n → ℤ) (H : ℝ → M)
    (hH : ∀ t, (dephase q (H t)).IsHermitian) (omega : ℝ) (U : ℝ → M)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (dephase q (H t)*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) (v : n → ℂ) (hv : (sector q 0).mulVec v=v) :
    (sector q 0).mulVec ((U t).mulVec v)=(U t).mulVec v := by
  have hc := propagator_commutes (fun s => dephase q (H s)) (sector q 0)
    hH (fun s => dephase_commutes_sector q (H s) 0) omega U hU t₀ t hinit
  rw [Matrix.mulVec_mulVec,← hc.eq,← Matrix.mulVec_mulVec,hv]

theorem constraint_continuous (q : n → ℤ) (D : M) (hD : D*sector q 0=0)
    (H : ℝ → M) (hH : ∀ t, (dephase q (H t)).IsHermitian)
    (omega : ℝ) (U : ℝ → M)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (dephase q (H t)*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) (v : n → ℂ) (hv : (sector q 0).mulVec v=v) :
    D.mulVec ((U t).mulVec v)=0 := by
  have hp := physical_sector_continuous q H hH omega U hU t₀ t hinit v hv
  rw [← hp,Matrix.mulVec_mulVec,hD,Matrix.zero_mulVec]

#print axioms conserved_operator_derivative
#print axioms conserved_operator
#print axioms propagator_unitary
#print axioms propagator_commutes
#print axioms physical_sector_continuous
#print axioms constraint_continuous

end
end UnifiedTheory.Audit.KFCausalContinuousConstraintFlow
