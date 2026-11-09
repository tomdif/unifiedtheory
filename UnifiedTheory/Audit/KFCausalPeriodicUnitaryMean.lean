/- Averaging one full period of an actual strongly continuous unitary group
is a contractive self-adjoint projection onto its fixed vectors. This is a
Hilbert-space result; it does not assert preservation of an energy domain. -/
import UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : StrongUnitaryGroup H)

def fixedSpace : Submodule ℂ H where
  carrier := {x | ∀ θ, U.action θ x = x}
  zero_mem' θ := map_zero _
  add_mem' hx hy θ := by rw [map_add, hx θ, hy θ]
  smul_mem' c x hx θ := by rw [map_smul, hx θ]

omit [CompleteSpace H] in
theorem fixedSpace_closed : IsClosed (fixedSpace U : Set H) := by
  have he : (fixedSpace U : Set H) = ⋂ θ : ℝ, {x | U.action θ x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter (fun θ => isClosed_eq (U.action θ).continuous continuous_id)

omit [CompleteSpace H] in
theorem fixed_of_zero_derivative (x : H)
    (hx : HasDerivAt (fun θ => U.action θ x) 0 0) : x ∈ fixedSpace U := by
  have hd (θ : ℝ) : HasDerivAt (fun φ => U.action φ x) 0 θ := by
    simpa only [map_zero] using derivative_at_time U x 0 hx θ
  intro θ
  simpa only [U.initial] using is_const_of_deriv_eq_zero
    (fun φ => (hd φ).differentiableAt) (fun φ => (hd φ).deriv) θ 0

omit [CompleteSpace H] in
theorem generator_zero_iff_fixed (x : H) :
    (x,0) ∈ (generator U).graph ↔ x ∈ fixedSpace U := by
  rw [generator_graph_iff]
  constructor
  · exact fixed_of_zero_derivative U x
  · intro hx
    change ∀ θ, U.action θ x = x at hx
    simpa only [hx] using hasDerivAt_const (0 : ℝ) x

theorem average_fixed (T : ℝ) (hperiod : ∀ x, U.action T x = x) (x : H) :
    average U x T ∈ fixedSpace U := by
  apply fixed_of_zero_derivative U _
  simpa only [hperiod, sub_self, smul_zero] using average_derivative U x T

theorem average_of_fixed (T : ℝ) (hT : T ≠ 0) (x : H) (hx : x ∈ fixedSpace U) :
    average U x T = x := by
  change ∀ θ, U.action θ x = x at hx
  simp only [average, primitive, hx, intervalIntegral.integral_const, sub_zero,
    smul_smul, inv_mul_cancel₀ hT, one_smul]

theorem average_inner_fixed (T : ℝ) (hT : T ≠ 0) (x y : H) (hy : y ∈ fixedSpace U) :
    inner ℂ y (average U x T) = inner ℂ y x := by
  have hi (θ : ℝ) : inner ℂ y (U.action θ x) = inner ℂ y x := by
    rw [inner_transport, hy (-θ)]
  change (innerSL ℂ y) (T⁻¹ • primitive U x T) = _
  rw [map_real_smul (innerSL ℂ y) (innerSL ℂ y).continuous]
  change T⁻¹ • (innerSL ℂ y) (∫ θ in 0..T, U.action θ x) = _
  rw [← (innerSL ℂ y).intervalIntegral_comp_comm ((U.continuous_orbit x).intervalIntegrable 0 T)]
  simp only [innerSL_apply_apply, hi, intervalIntegral.integral_const, sub_zero,
    smul_smul, inv_mul_cancel₀ hT, one_smul]

theorem average_idempotent (T : ℝ) (hT : T ≠ 0) (hperiod : ∀ x, U.action T x = x) (x : H) :
    average U (average U x T) T = average U x T :=
  average_of_fixed U T hT _ (average_fixed U T hperiod x)

theorem average_symmetric (T : ℝ) (hT : T ≠ 0) (hperiod : ∀ x, U.action T x = x) (x y : H) :
    inner ℂ (average U x T) y = inner ℂ x (average U y T) := by
  have h1 := average_inner_fixed U T hT y (average U x T) (average_fixed U T hperiod x)
  have h2 := average_inner_fixed U T hT x (average U y T) (average_fixed U T hperiod y)
  have h2' := congrArg (starRingEnd ℂ) h2
  simp only [inner_conj_symm] at h2'
  exact h1.symm.trans h2'

omit [CompleteSpace H] in
theorem average_norm_le (T : ℝ) (hT : 0 < T) (x : H) : ‖average U x T‖ ≤ ‖x‖ := by
  have hb : ‖primitive U x T‖ ≤ ‖x‖*|T-0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun θ _ => ((U.action θ).norm_map x).le)
  rw [sub_zero, abs_of_pos hT] at hb
  rw [average, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  calc
    _ ≤ T⁻¹*(‖x‖*T) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)
    _ = ‖x‖ := by field_simp

def meanLinear (T : ℝ) : H →ₗ[ℂ] H where
  toFun x := average U x T
  map_add' x y := by
    simp only [average, primitive, map_add]
    rw [intervalIntegral.integral_add ((U.continuous_orbit x).intervalIntegrable 0 T)
      ((U.continuous_orbit y).intervalIntegrable 0 T), smul_add]
  map_smul' c x := by
    simp only [average, primitive, map_smul, intervalIntegral.integral_smul, RingHom.id_apply]
    exact smul_comm _ _ _

def meanOperator (T : ℝ) (hT : 0 < T) : H →L[ℂ] H :=
  (meanLinear U T).mkContinuous 1 (fun x => by simpa only [one_mul] using average_norm_le U T hT x)

omit [CompleteSpace H] in
theorem meanOperator_apply (T : ℝ) (hT : 0 < T) (x : H) : meanOperator U T hT x = average U x T := rfl

theorem meanOperator_selfAdjoint (T : ℝ) (hT : 0 < T) (hperiod : ∀ x, U.action T x = x) :
    IsSelfAdjoint (meanOperator U T hT) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact average_symmetric U T hT.ne' hperiod

#print axioms fixedSpace_closed
#print axioms fixed_of_zero_derivative
#print axioms generator_zero_iff_fixed
#print axioms average_fixed
#print axioms average_of_fixed
#print axioms average_inner_fixed
#print axioms average_idempotent
#print axioms average_symmetric
#print axioms average_norm_le
#print axioms meanOperator
#print axioms meanOperator_apply
#print axioms meanOperator_selfAdjoint

end
end UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
