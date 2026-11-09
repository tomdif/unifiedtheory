/- Translation invariance removes the cyclic neutral position from every
component of the full canonical vector field, not just from the energy. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumNeutral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumNeutral

theorem differential_neutralShift (ε κ : ℝ) (hε : 0 ≤ ε) (t u : ℝ) (z : Phase) :
    fderiv ℝ (fullHamiltonian ε κ) (t,neutralShift u z) =
      fderiv ℝ (fullHamiltonian ε κ) (t,z) := by
  let v : TimePhase := (0,u • positionBasis (.inr 3))
  have htrans (x : TimePhase) : fullHamiltonian ε κ (x+v) = fullHamiltonian ε κ x := by
    rcases x with ⟨a,b⟩
    simpa only [v,Prod.mk_add_mk,add_zero,neutralShift] using fullHamiltonian_neutralShift ε κ a u b
  have hd := ((fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num)
    ((t,z)+v)).hasFDerivAt
  have hc := hd.comp (t,z) ((hasFDerivAt_id (t,z)).add_const v)
  simp only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] at hc
  have he : (fun x : TimePhase => fullHamiltonian ε κ (x+v)) = fullHamiltonian ε κ := funext htrans
  rw [he] at hc
  simpa only [v,Prod.mk_add_mk,add_zero,neutralShift] using hc.fderiv.symm

theorem field_neutralShift (ε κ : ℝ) (hε : 0 ≤ ε) (t u : ℝ) (z : Phase) :
    field ε κ (t,neutralShift u z) = field ε κ (t,z) := by
  simp only [field,stateDifferential,differential_neutralShift ε κ hε]

def eraseNeutral : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.id ℝ Phase - (q (.inr 3)).smulRight (positionBasis (.inr 3))

theorem eraseNeutral_apply (z : Phase) :
    eraseNeutral z = neutralShift (-q (.inr 3) z) z := by
  simp [eraseNeutral,neutralShift,sub_eq_add_neg]

theorem eraseNeutral_position (z : Phase) : q (.inr 3) (eraseNeutral z) = 0 := by
  simp [eraseNeutral_apply,neutralShift,q_apply,positionBasis,PiLp.basisFun_apply]

theorem field_eraseNeutral (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    field ε κ (x.1,eraseNeutral x.2) = field ε κ x := by
  rw [eraseNeutral_apply]
  exact field_neutralShift ε κ hε x.1 _ x.2

theorem neutralSpeed_bounded (ε κ : ℝ) (hε : 0 ≤ ε) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : TimePhase, ‖(x.1,eraseNeutral x.2)‖ ≤ R →
      |q (.inr 3) (field ε κ x).2| ≤ M := by
  have hc : Continuous (fun x : TimePhase => q (.inr 3) (field ε κ x).2) :=
    (q (.inr 3)).continuous.comp ((field_contDiff ε κ hε).continuous.snd)
  obtain ⟨M,hM⟩ := ((isCompact_closedBall (0 : TimePhase) R).image hc).isBounded.exists_norm_le
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hx
  rw [← field_eraseNeutral ε κ hε x]
  have hb := hM _ (Set.mem_image_of_mem _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))
  exact le_trans (by simpa only [Real.norm_eq_abs] using hb) (le_max_left _ _)

#print axioms differential_neutralShift
#print axioms field_neutralShift
#print axioms eraseNeutral_apply
#print axioms eraseNeutral_position
#print axioms field_eraseNeutral
#print axioms neutralSpeed_bounded

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
