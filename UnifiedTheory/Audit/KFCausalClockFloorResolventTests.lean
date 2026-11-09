/- The actual averaged Hamiltonian supplies bounded form lifts for
resolvent-regularized versions of every bounded physical observable.
Their error on a form state is controlled by its actual energy. -/
import UnifiedTheory.Audit.KFCausalFormResolventError
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventTests
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "R₀" => shiftedResolvent ε hε h hne hh m g k

def regularizer (a τ : ℝ) : Hilbert →L[ℂ] Hilbert := a • R₀ a τ

def regularizerLift (a τ : ℝ) : Hilbert →L[ℂ] V₀ :=
  a • ((referenceInverse ε hε h hne hh m g k a τ).comp
    (referenceAdjoint ε hε h hne hh m g k))

theorem regularizerLift_embedding (a τ : ℝ) (f : Hilbert) :
    J (regularizerLift ε hε h hne hh m g k a τ f) =
      regularizer ε hε h hne hh m g k a τ f := by
  change J (a • resolventFormLift ε hε h hne hh m g k a τ f) = a • R₀ a τ f
  exact ContinuousLinearMap.map_smul_of_tower J a (resolventFormLift ε hε h hne hh m g k a τ f)

theorem regularizer_symmetric (a τ : ℝ) (ha : 0 < a) (f z : Hilbert) :
    inner ℂ (regularizer ε hε h hne hh m g k a τ f) z =
      inner ℂ f (regularizer ε hε h hne hh m g k a τ z) := by
  change inner ℂ (a • R₀ a τ f) z = inner ℂ f (a • R₀ a τ z)
  rw [inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  exact congrArg (fun z : ℂ => a • z)
    ((shiftedResolvent_selfAdjoint ε hε h hne hh m g k a τ ha).isSymmetric f z)

theorem regularizer_contraction (a τ : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖regularizer ε hε h hne hh m g k a τ f‖ ≤ ‖f‖ := by
  change ‖a • R₀ a τ f‖ ≤ ‖f‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hr := (R₀ a τ).le_opNorm f
  have hb := shiftedResolvent_norm ε hε h hne hh m g k a τ ha
  calc
    _ ≤ a*(a⁻¹*‖f‖) := mul_le_mul_of_nonneg_left
      (hr.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f))) ha.le
    _ = ‖f‖ := by rw [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]

theorem regularizer_variational (a τ : ℝ) (ha : 0 < a) (f : Hilbert) (z : V₀) :
    inner ℂ (regularizerLift ε hε h hne hh m g k a τ f) (Q τ z) =
      (a:ℂ)*inner ℂ (f-regularizer ε hε h hne hh m g k a τ f) (J z) := by
  change inner ℂ (a • resolventFormLift ε hε h hne hh m g k a τ f) (Q τ z) = _
  exact (inner_smul_left_eq_smul (𝕜 := ℂ) _ _ a).trans
    (congrArg (fun c : ℂ => a • c)
      (shiftedResolvent_variational ε hε h hne hh m g k a τ ha f z))

def referenceEnergyMap (τ : ℝ) : V₀ →L[ℂ] KFCausalAveragedOutputRescaling.EnergyOutputSpace :=
  (energyOutput ε hε h hne hh m g k τ).comp
    (formTransfer ε hε h hne hh m g k 0 τ)

theorem referenceEnergyMap_apply (τ : ℝ) (x : V₀) :
    referenceEnergyMap ε hε h hne hh m g k τ x =
      energyOutput ε hε h hne hh m g k τ (formTransfer ε hε h hne hh m g k 0 τ x) :=
  ContinuousLinearMap.comp_apply _ _ x

theorem referenceEnergyMap_pairing (τ : ℝ) (x y : V₀) :
    inner ℂ (referenceEnergyMap ε hε h hne hh m g k τ x)
      (referenceEnergyMap ε hε h hne hh m g k τ y) = inner ℂ x (Q τ y) :=
  (congrArg₂ (inner ℂ) (referenceEnergyMap_apply ε hε h hne hh m g k τ x)
    (referenceEnergyMap_apply ε hε h hne hh m g k τ y)).trans
      (referenceForm_represents_closed_form ε hε h hne hh m g k τ x y).symm

theorem referenceEnergyMap_square (τ : ℝ) (x : V₀) :
    ‖referenceEnergyMap ε hε h hne hh m g k τ x‖^2 =
      timeEnergy ε hε h hne hh m g k τ x :=
  (congrArg (fun v : KFCausalAveragedOutputRescaling.EnergyOutputSpace => ‖v‖^2)
    (referenceEnergyMap_apply ε hε h hne hh m g k τ x)).trans
      (timeEnergy_actual ε hε h hne hh m g k τ x)

theorem regularizer_error_square (a τ : ℝ) (ha : 0 < a) (x : V₀) :
    ‖J x-regularizer ε hε h hne hh m g k a τ (J x)‖^2 ≤
      timeEnergy ε hε h hne hh m g k τ x/(4*a) := by
  let L := referenceEnergyMap ε hε h hne hh m g k τ
  let y := regularizerLift ε hε h hne hh m g k a τ (J x)
  have hj : J y = regularizer ε hε h hne hh m g k a τ (J x) :=
    regularizerLift_embedding ε hε h hne hh m g k a τ (J x)
  have hv (z : V₀) : inner ℂ (L y) (L z) = (a:ℂ)*inner ℂ (J x-J y) (J z) :=
    ((referenceEnergyMap_pairing ε hε h hne hh m g k τ y z).trans
      (regularizer_variational ε hε h hne hh m g k a τ ha (J x) z)).trans
        (congrArg (fun v : Hilbert => (a:ℂ)*inner ℂ (J x-v) (J z)) hj.symm)
  calc
    _ = ‖J x-J y‖^2 := congrArg (fun v : Hilbert => ‖J x-v‖^2) hj.symm
    _ ≤ ‖L x‖^2/(4*a) := KFCausalFormResolventError.variational_error_square J L a ha x y hv
    _ = _ := congrArg (fun v : ℝ => v/(4*a))
      (referenceEnergyMap_square ε hε h hne hh m g k τ x)

theorem regularizer_error_norm (a τ : ℝ) (ha : 0 < a) (x : V₀) :
    ‖regularizer ε hε h hne hh m g k a τ (J x)-J x‖ ≤
      Real.sqrt (timeEnergy ε hε h hne hh m g k τ x/(4*a)) := by
  rw [norm_sub_rev]
  exact (Real.le_sqrt (norm_nonneg _) (div_nonneg
    (timeEnergy_nonneg ε hε h hne hh m g k τ x) (by positivity))).mpr
      (regularizer_error_square ε hε h hne hh m g k a τ ha x)

def observable (a τ : ℝ) (D : Hilbert →L[ℂ] Hilbert) : Hilbert →L[ℂ] Hilbert :=
  (regularizer ε hε h hne hh m g k a τ).comp
    (D.comp (regularizer ε hε h hne hh m g k a τ))

def formLift (a τ : ℝ) (D : Hilbert →L[ℂ] Hilbert) : V₀ →L[ℂ] V₀ :=
  (regularizerLift ε hε h hne hh m g k a τ).comp
    (D.comp ((regularizer ε hε h hne hh m g k a τ).comp J))

theorem formLift_embedding (a τ : ℝ) (D : Hilbert →L[ℂ] Hilbert) (x : V₀) :
    J (formLift ε hε h hne hh m g k a τ D x) =
      observable ε hε h hne hh m g k a τ D (J x) :=
  regularizerLift_embedding ε hε h hne hh m g k a τ _

theorem observable_dual (a τ : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert) (x y : Hilbert) :
    inner ℂ (observable ε hε h hne hh m g k a τ D x) y =
      inner ℂ x (observable ε hε h hne hh m g k a τ D.adjoint y) := by
  let R := regularizer ε hε h hne hh m g k a τ
  have hs := regularizer_symmetric ε hε h hne hh m g k a τ ha
  change inner ℂ (R (D (R x))) y = inner ℂ x (R (D.adjoint (R y)))
  exact (hs (D (R x)) y).trans ((D.adjoint_inner_right (R x) (R y)).symm.trans
    (hs x (D.adjoint (R y))))

theorem observable_expectation_error (a τ : ℝ) (ha : 0 < a)
    (D : Hilbert →L[ℂ] Hilbert) (x : V₀) :
    ‖inner ℂ (J x) (observable ε hε h hne hh m g k a τ D (J x))-
      inner ℂ (J x) (D (J x))‖ ≤
        2*‖D‖*‖J x‖*Real.sqrt (timeEnergy ε hε h hne hh m g k τ x/(4*a)) := by
  have hb := KFCausalFormResolventError.sandwich_expectation_error
    (regularizer ε hε h hne hh m g k a τ) D
    (regularizer_contraction ε hε h hne hh m g k a τ ha)
    (regularizer_symmetric ε hε h hne hh m g k a τ ha) (J x)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (regularizer_error_norm ε hε h hne hh m g k a τ ha x) (by positivity))

#print axioms regularizerLift_embedding
#print axioms regularizer_symmetric
#print axioms regularizer_contraction
#print axioms regularizer_variational
#print axioms referenceEnergyMap_apply
#print axioms referenceEnergyMap_pairing
#print axioms referenceEnergyMap_square
#print axioms regularizer_error_square
#print axioms regularizer_error_norm
#print axioms formLift_embedding
#print axioms observable_dual
#print axioms observable_expectation_error

end
end UnifiedTheory.Audit.KFCausalClockFloorResolventTests
