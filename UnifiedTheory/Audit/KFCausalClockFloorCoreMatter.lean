/- Physical field bounds and maximal field-domain membership for the
revised shifted product states, including the full neutral shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoreStates
import UnifiedTheory.Audit.KFCausalTransversePositionMoments
import UnifiedTheory.Audit.KFCausalShiftedScalarMoments
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoreMatter
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorProductStates
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseFlowBounds
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalClockTrialWeights (clock)
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar
open UnifiedTheory.Audit.KFCausalShiftedScalarMoments
open UnifiedTheory.Audit.KFCausalTransversePositionMoments (packet_square_moment)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare

theorem flow_position_fourth_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) (x : Transverse) :
    ‖flow ((chartIso ε hε).symm q) x‖^4 ≤
      5000*(1+(clock ε hε q)^2)*‖x‖^4 := by
  have hs := flow_norm_square_bound (-((chartIso ε hε).symm q)) x
  simp only [neg_neg] at hs
  have h₂ : ‖flow ((chartIso ε hε).symm q) x‖^2 ≤
      50*(1+clock ε hε q)*‖x‖^2 := by
    exact hs
  have h₄ := pow_le_pow_left₀ (sq_nonneg _) h₂ 2
  have hb : (1+clock ε hε q)^2 ≤ 2*(1+(clock ε hε q)^2) := by
    nlinarith [sq_nonneg (clock ε hε q-1)]
  nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ 2500*‖x‖^4 by positivity)]

def pulledField (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (z : Configuration) : ℝ :=
  l (((coordinateHomeomorph ε hε).symm z).2)

theorem pulledField_continuous (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) :
    Continuous (pulledField ε hε l) :=
  l.continuous.comp (continuous_snd.comp (coordinateHomeomorph ε hε).symm.continuous)

theorem pulledField_fourth_bound (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (z : Configuration) :
    (pulledField ε hε l z)^4 ≤ (5000*‖l‖^4)*(1+(clock ε hε z.1)^2)*‖z.2‖^4 := by
  have hl := pow_le_pow_left₀ (norm_nonneg _) (l.le_opNorm (((coordinateHomeomorph ε hε).symm z).2)) 4
  have hf := mul_le_mul_of_nonneg_left (flow_position_fourth_bound ε hε z.1 z.2) (pow_nonneg (norm_nonneg l) 4)
  rw [mul_pow,Real.norm_eq_abs] at hl
  have he (r : ℝ) : |r|^4=r^4 := by nlinarith only [sq_abs r]
  rw [he] at hl
  change (pulledField ε hε l z)^4 ≤ ‖l‖^4*‖flow ((chartIso ε hε).symm z.1) z.2‖^4 at hl
  nlinarith

def shiftedFunction (ε a p y : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) : Configuration → ℂ :=
  weightedFunction ε hε (configurationProduct (shiftedScalar ε a p y) ψ)

def quadraticInput (ε a p y : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (l : Transverse →L[ℝ] ℝ) (z : Configuration) : ℂ :=
  (pulledField ε hε l z:ℂ)^2*configurationProduct (shiftedScalar ε a p y) ψ z

def quadraticFunction (ε a p y : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (l : Transverse →L[ℝ] ℝ) (z : Configuration) : ℂ :=
  (l z.2:ℂ)^2*shiftedFunction ε a p y hε ψ z

theorem quadraticInput_continuous (ε a p y : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (l : Transverse →L[ℝ] ℝ) : Continuous (quadraticInput ε a p y hε ψ l) :=
  ((Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).pow 2).mul
    (((shiftedScalar_continuous ε a p y).comp continuous_fst).mul
      ((unflattenSchwartz ψ).continuous.comp continuous_snd))

theorem quadraticInput_square (ε a p y : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (l : Transverse →L[ℝ] ℝ) (z : Configuration) :
    ‖quadraticInput ε a p y hε ψ l z‖^2 =
      (pulledField ε hε l z)^4*‖shiftedScalar ε a p y z.1‖^2*‖unflattenSchwartz ψ z.2‖^2 := by
  simp only [quadraticInput,configurationProduct,norm_mul,norm_pow,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change ((pulledField ε hε l z)^2)^2 *
    (‖shiftedScalar ε a p y z.1‖^2*‖unflattenSchwartz ψ z.2‖^2) = _
  ring

theorem quadraticInput_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    MemLp (quadraticInput ε a p y hε ψ l) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (quadraticInput_continuous ε a p y hε ψ l).aestronglyMeasurable).mpr
  have hi := ((shiftedScalar_one_add_clock_square_energy ε a p y hε ha hy).mul_prod
    (packet_square_moment ψ 4)).const_mul (5000*‖l‖^4)
  rw [Measure.volume_eq_prod ℝ Transverse]
  apply hi.mono' ((quadraticInput_continuous ε a p y hε ψ l).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),quadraticInput_square]
  calc
    _ ≤ ((5000*‖l‖^4)*(1+(clock ε hε z.1)^2)*‖z.2‖^4)*
        ‖shiftedScalar ε a p y z.1‖^2*‖unflattenSchwartz ψ z.2‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pulledField_fourth_bound ε hε l z) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

theorem quadraticFunction_eq_weighted (ε a p y : ℝ) (hε : 0 < ε)
    (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    quadraticFunction ε a p y hε ψ l = weightedFunction ε hε (quadraticInput ε a p y hε ψ l) := by
  funext z
  simp only [quadraticFunction,shiftedFunction,weightedFunction,quadraticInput,pulledField,
    Homeomorph.symm_apply_apply]
  ring

theorem quadraticFunction_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    MemLp (quadraticFunction ε a p y hε ψ l) 2 := by
  rw [quadraticFunction_eq_weighted]
  exact weighted_memLp ε hε _ (quadraticInput_memLp ε a p y hε ha hy ψ l)

theorem shiftedState_fieldSquare_domain (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    shiftedState ε a p y hε ha hy ψ (ψ.memLp 2 volume) ∈ (fieldSquare l).domain := by
  apply (fieldSquare_domain l _).mpr
  apply (quadraticFunction_memLp ε a p y hε ha hy ψ l).ae_eq
  filter_upwards [productState_coe ε hε (shiftedScalar ε a p y) ψ
    (shiftedScalar_memLp ε a p y hε ha hy) (ψ.memLp 2 volume)] with z hz
  unfold shiftedState
  rw [hz]
  rfl

theorem shiftedState_physicalField_domain (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    shiftedState ε a p y hε ha hy ψ (ψ.memLp 2 volume) ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l (shiftedState_fieldSquare_domain ε a p y hε ha hy ψ l)

#print axioms flow_position_fourth_bound
#print axioms pulledField_continuous
#print axioms pulledField_fourth_bound
#print axioms quadraticInput_continuous
#print axioms quadraticInput_square
#print axioms quadraticInput_memLp
#print axioms quadraticFunction_eq_weighted
#print axioms quadraticFunction_memLp
#print axioms shiftedState_fieldSquare_domain
#print axioms shiftedState_physicalField_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorCoreMatter
