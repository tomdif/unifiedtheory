/- The canonical Hamiltonian vector field on the actual paired phase space.
Its symplectic cancellation is proved algebraically for every differential.
The autonomous clock variable supplies the explicit time dependence. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
import UnifiedTheory.Audit.KFCausalGlobalLipschitzODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalPairedRotation (Space)

def positionBasis (i : Index) : Phase := (PiLp.basisFun 2 ℝ Index i,0)
def momentumBasis (i : Index) : Phase := (0,PiLp.basisFun 2 ℝ Index i)

theorem phase_expansion (z : Phase) :
    z = ∑ i : Index, (z.1 i • positionBasis i+z.2 i • momentumBasis i) := by
  ext j <;> rcases j with j | j <;> fin_cases j <;>
    simp [positionBasis, momentumBasis, PiLp.basisFun_apply, Fin.sum_univ_succ]

theorem dual_expansion (l : Phase →L[ℝ] ℝ) (z : Phase) :
    l z = ∑ i : Index, (z.1 i*l (positionBasis i)+z.2 i*l (momentumBasis i)) := by
  conv_lhs => rw [phase_expansion z]
  simp only [map_sum, map_add, map_smul, smul_eq_mul]

def poissonLinear : (Phase →L[ℝ] ℝ) →ₗ[ℝ] Phase where
  toFun l := (WithLp.toLp 2 (fun i => l (momentumBasis i)),
    WithLp.toLp 2 (fun i => -l (positionBasis i)))
  map_add' l k := by ext i <;> simp [add_comm]
  map_smul' c l := by ext i <;> simp

def poisson : (Phase →L[ℝ] ℝ) →L[ℝ] Phase := poissonLinear.toContinuousLinearMap

theorem poisson_q (l : Phase →L[ℝ] ℝ) (i : Index) :
    (poisson l).1 i = l (momentumBasis i) := rfl

theorem poisson_p (l : Phase →L[ℝ] ℝ) (i : Index) :
    (poisson l).2 i = -l (positionBasis i) := rfl

theorem dual_poisson_zero (l : Phase →L[ℝ] ℝ) : l (poisson l) = 0 := by
  rw [dual_expansion]
  apply Finset.sum_eq_zero
  intro i _
  rw [poisson_q, poisson_p]
  ring

def stateInclusion : Phase →L[ℝ] TimePhase := ContinuousLinearMap.inr ℝ ℝ Phase

def stateDifferential (ε κ : ℝ) (x : TimePhase) : Phase →L[ℝ] ℝ :=
  (fderiv ℝ (fullHamiltonian ε κ) x).comp stateInclusion

def field (ε κ : ℝ) (x : TimePhase) : TimePhase := (1,poisson (stateDifferential ε κ x))

theorem field_contDiff (ε κ : ℝ) (hε : 0 ≤ ε) : ContDiff ℝ 1 (field ε κ) := by
  have hd := (fullHamiltonian_contDiff ε κ hε 2).fderiv_right (m := 1) (by norm_num)
  have hs : ContDiff ℝ 1 (stateDifferential ε κ) := hd.clm_comp contDiff_const
  exact contDiff_const.prodMk (poisson.contDiff.comp hs)

theorem hamiltonian_field (ε κ : ℝ) (x : TimePhase) :
    fderiv ℝ (fullHamiltonian ε κ) x (field ε κ x) =
      fderiv ℝ (fullHamiltonian ε κ) x (1,0) := by
  let l := fderiv ℝ (fullHamiltonian ε κ) x
  change l (1,poisson (l.comp stateInclusion)) = l (1,0)
  rw [show (1,poisson (l.comp stateInclusion)) =
    (1,0)+stateInclusion (poisson (l.comp stateInclusion)) by simp [stateInclusion], map_add]
  have h : l (stateInclusion (poisson (l.comp stateInclusion))) = 0 :=
    dual_poisson_zero (l.comp stateInclusion)
  rw [h, add_zero]

#print axioms phase_expansion
#print axioms dual_expansion
#print axioms poisson_q
#print axioms poisson_p
#print axioms dual_poisson_zero
#print axioms field_contDiff
#print axioms hamiltonian_field

end
end UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
