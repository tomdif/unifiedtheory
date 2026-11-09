/- Linear and quadratic transverse field factors applied after the
actual longitudinal exponential output have finite L2 energy. -/
import UnifiedTheory.Audit.KFCausalShiftedProductAction
import UnifiedTheory.Audit.KFCausalShiftedScalarMoments
import UnifiedTheory.Audit.KFCausalTransversePositionMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedFieldEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar
open UnifiedTheory.Audit.KFCausalShiftedScalarMoments
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalTransversePositionMoments

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

theorem linear_field_memLp_of_quadratic (f : Configuration → ℂ) (l : Transverse →L[ℝ] ℝ)
    (hf : MemLp f 2) (hq : MemLp (fun z : Configuration => (l z.2:ℂ)^2*f z) 2) :
    MemLp (fun z : Configuration => (l z.2:ℂ)*f z) 2 := by
  have hm : AEStronglyMeasurable (fun z : Configuration => (l z.2:ℂ)*f z) volume :=
    (Complex.continuous_ofReal.comp (l.continuous.comp continuous_snd)).aestronglyMeasurable.mul hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have h₀ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have h₄ := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  apply (h₀.add h₄).mono' (hm.norm.pow 2)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  dsimp only [Pi.add_apply,Pi.pow_apply,Pi.mul_apply]
  simp only [norm_mul,norm_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hb : (l z.2)^2 ≤ 1+((l z.2)^2)^2 := by nlinarith [sq_nonneg ((l z.2)^2-1/2)]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f z‖)]

theorem linearFunction_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun z : Configuration => (l z.2:ℂ)*shiftedFunction ε a p y hε ψ z) 2 :=
  linear_field_memLp_of_quadratic _ l (shiftedFunction_memLp ε a p y hε ha hy ψ (ψ.memLp 2 volume))
    (quadraticFunction_memLp ε a p y hε ha hy ψ l)

#print axioms quadraticInput_continuous
#print axioms quadraticInput_square
#print axioms quadraticInput_memLp
#print axioms quadraticFunction_eq_weighted
#print axioms quadraticFunction_memLp
#print axioms linear_field_memLp_of_quadratic
#print axioms linearFunction_memLp

end
end UnifiedTheory.Audit.KFCausalShiftedFieldEnergy
