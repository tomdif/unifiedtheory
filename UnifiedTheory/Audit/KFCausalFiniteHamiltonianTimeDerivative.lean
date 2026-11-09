/- The time dependence of the actual finite-family Hamiltonian output is
differentiated in physical Hilbert space.  Both that output and its time
derivative belong to every instantaneous Hamiltonian domain.  These are
statements about the original fixed input, not its evolved trajectory. -/
import UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquare
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteHamiltonianTimeDerivative
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalFiniteSecondHamiltonianColumns (second)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteHamiltonianSquare (firstOutput secondOutput)

def coefficient (mass2 quartic vacuum t : ℝ) (j : Fin 8) : ℂ :=
  star (energyWeight mass2 quartic vacuum t j)*energyWeight mass2 quartic vacuum t j

def coefficientDerivative (mass2 quartic vacuum t : ℝ) (j : Fin 8) : ℂ :=
  if j.val < 3 then 0 else 2*coefficient mass2 quartic vacuum t j

private theorem growing_derivative (q t : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp s*q:ℝ):ℂ)*((Real.exp s*q:ℝ):ℂ))
      (2*((Real.exp t*q:ℝ):ℂ)*((Real.exp t*q:ℝ):ℂ)) t := by
  have hd : HasDerivAt (fun s : ℝ => (Real.exp s*q)*(Real.exp s*q))
      (2*(Real.exp t*q)*(Real.exp t*q)) t := by
    convert ((Real.hasDerivAt_exp t).mul_const q).mul
      ((Real.hasDerivAt_exp t).mul_const q) using 1
    ring
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hd.ofReal_comp

theorem coefficient_derivative (mass2 quartic vacuum t : ℝ) (j : Fin 8) :
    HasDerivAt (fun s => coefficient mass2 quartic vacuum s j)
      (coefficientDerivative mass2 quartic vacuum t j) t := by
  fin_cases j <;>
    simp only [coefficientDerivative,coefficient,energyWeight,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Complex.star_def,
      Complex.conj_ofReal] <;> norm_num only
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa only [mul_assoc] using growing_derivative (Real.sqrt (1/2)) t
  · simpa only [mul_assoc] using growing_derivative (Real.sqrt (1/2)) t
  · simpa only [mul_assoc] using growing_derivative (Real.sqrt (mass2/2)) t
  · simpa only [mul_assoc] using growing_derivative (Real.sqrt (quartic/4)) t
  · simpa only [mul_assoc] using growing_derivative (Real.sqrt vacuum) t

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum : ℝ)
local notation "H" => hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum
local notation "Z" => fun j => zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb j)
local notation "F" => firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum

def outputDerivative (s : ℝ) : Hilbert :=
  ∑ j, coefficientDerivative mass2 quartic vacuum s j • Z j

theorem output_derivative (s : ℝ) :
    HasDerivAt F (outputDerivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s) s := by
  have he : F = fun t => ∑ j, coefficient mass2 quartic vacuum t j • Z j := by
    funext t
    exact KFCausalFiniteSecondHamiltonianColumns.hamiltonianOutput_sum
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
  rw [he]
  exact HasDerivAt.fun_sum (fun j _ =>
    (coefficient_derivative mass2 quartic vacuum s j).smul_const (Z j))

theorem output_cross_domain (s t : ℝ) : F s ∈ (H t).domain := by
  change KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∈ _
  rw [KFCausalFiniteSecondHamiltonianColumns.hamiltonianOutput_sum
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s]
  apply (H t).domain.sum_mem
  intro j _
  exact (H t).domain.smul_mem _
    (KFCausalFiniteHamiltonianSquare.projected_second_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t j)

theorem derivative_cross_domain (s t : ℝ) :
    outputDerivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s ∈ (H t).domain := by
  apply (H t).domain.sum_mem
  intro j _
  exact (H t).domain.smul_mem _
    (KFCausalFiniteHamiltonianSquare.projected_second_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t j)

def mixedOutput (s t : ℝ) : Hilbert :=
  H t ⟨F s,output_cross_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s t⟩

theorem mixed_graph (s t : ℝ) :
    (F s,mixedOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s t) ∈ (H t).graph :=
  (H t).mem_graph ⟨F s,output_cross_domain
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s t⟩

theorem mixed_diagonal (s : ℝ) :
    mixedOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s s =
      secondOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s := rfl

#print axioms coefficient_derivative
#print axioms output_derivative
#print axioms output_cross_domain
#print axioms derivative_cross_domain
#print axioms mixed_graph
#print axioms mixed_diagonal
end
end UnifiedTheory.Audit.KFCausalFiniteHamiltonianTimeDerivative
