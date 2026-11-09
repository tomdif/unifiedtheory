/- The exact source primitive is a symmetric dilation/shear polynomial in
the physical position and momentum quadratures. No CCR is used, so this
identification also holds at finite capacity. -/
import UnifiedTheory.Audit.KFCausalQuadraticSourcePrimitive
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSourcePrimitiveQuadratures
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
open UnifiedTheory.Audit.KFCausalQuadraticSourcePrimitive
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity

variable {n : Type*} [Fintype n]
local notation "M" => Matrix n n ℂ

def position (hbar : ℝ) (A : M) : M := (Real.sqrt (hbar/2):ℂ) • (A+Aᴴ)
def momentum (hbar : ℝ) (A : M) : M := (Real.sqrt (hbar/2):ℂ) • (-Complex.I • skew A)

theorem raw_dilation (A : M) : current (A+Aᴴ) (-Complex.I • skew A) =
    -Complex.I • (A*A-Aᴴ*Aᴴ) := by
  simp only [current,skew,smul_mul_assoc,mul_smul_comm,mul_add,add_mul,mul_sub,sub_mul]
  module

theorem physical_dilation (hbar : ℝ) (hh : 0 ≤ hbar) (A : M) :
    current (position hbar A) (momentum hbar A) = (-Complex.I*(hbar/2:ℝ)) • (A*A-Aᴴ*Aᴴ) := by
  have hs : (Real.sqrt (hbar/2):ℂ)^2 = ((hbar/2:ℝ):ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [position,momentum,current_scale,hs,raw_dilation,smul_smul]
  congr 1
  ring

theorem physical_shear (hbar : ℝ) (hh : 0 ≤ hbar) (C D Z : M) :
    current (momentum hbar Z) (position hbar C+position hbar D) =
      (-Complex.I*(hbar/4:ℝ)) • (skew Z*(C+Cᴴ+D+Dᴴ)+(C+Cᴴ+D+Dᴴ)*skew Z) := by
  have hs : (Real.sqrt (hbar/2):ℂ)^2 = ((hbar/2:ℝ):ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  unfold position momentum
  rw [← smul_add,current_scale,hs]
  simp only [current,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.ofReal_div,Complex.ofReal_ofNat,
    mul_add,add_mul]
  module

def dilationShear (hbar : ℝ) (A B C D Z : M) : M :=
  (1/2:ℂ) • (current (position hbar A) (momentum hbar A)+
    current (position hbar B) (momentum hbar B)+current (position hbar C) (momentum hbar C)+
    current (position hbar D) (momentum hbar D))+
  current (momentum hbar Z) (position hbar C+position hbar D)

theorem quadraticPrimitive_eq_dilationShear (hbar : ℝ) (hh : 0 ≤ hbar) (A B C D Z : M) :
    quadraticPrimitive hbar A B C D Z = dilationShear hbar A B C D Z := by
  rw [dilationShear,physical_dilation hbar hh A,physical_dilation hbar hh B,
    physical_dilation hbar hh C,physical_dilation hbar hh D,physical_shear hbar hh C D Z]
  simp only [quadraticPrimitive,Complex.ofReal_div,Complex.ofReal_ofNat]
  module

theorem actual_source_dilationShear (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    primitive charge (source R r hbar) = dilationShear hbar
      (ladder r 1) (ladder r 2) (ladder r 3) (ladder r 4) (ladder r 5) := by
  rw [actual_source_primitive,quadraticPrimitive_eq_dilationShear hbar hh]

#print axioms physical_dilation
#print axioms physical_shear
#print axioms quadraticPrimitive_eq_dilationShear
#print axioms actual_source_dilationShear

end
end UnifiedTheory.Audit.KFCausalSourcePrimitiveQuadratures
