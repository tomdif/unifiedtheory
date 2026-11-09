/- Measure-preserving physical coordinate symmetries for the exact clock
and kinetic cancellation. All changes of variables act on the full
configuration space and retain the clock coordinate. -/
import UnifiedTheory.Audit.KFCausalChargedPairDifferential
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairKineticSymmetries
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalChargedPairCoordinates (pairPolynomial)

def swap (q : Transverse) : Transverse := ![q 2,q 3,q 0,q 1,q 4]
def reflect (q : Transverse) : Transverse := ![q 0,q 1,q 2,q 3,-q 4]

theorem swap_twice (q : Transverse) : swap (swap q) = q := by
  funext i
  fin_cases i <;> simp [swap]

theorem reflect_twice (q : Transverse) : reflect (reflect q) = q := by
  funext i
  fin_cases i <;> simp [reflect]

theorem swap_preserving : MeasurePreserving swap volume volume := by
  have hm := volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ)
    ((Equiv.swap (0 : Fin 5) 2).trans (Equiv.swap (1 : Fin 5) 3))
  convert hm using 1
  funext q i
  fin_cases i <;> simp [swap,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
    Equiv.swap_apply_def]

theorem reflect_preserving : MeasurePreserving reflect volume volume := by
  have hm := volume_preserving_pi (f := fun i : Fin 5 =>
    fun x : ℝ => if i=4 then -x else x) (by
      intro i
      by_cases hi : i=4
      · simpa only [if_pos hi] using Measure.measurePreserving_neg (volume : Measure ℝ)
      · simpa only [if_neg hi] using MeasurePreserving.id (volume : Measure ℝ))
  convert hm using 1
  funext q i
  fin_cases i <;> simp [reflect]

def swapEquiv : Transverse ≃ᵐ Transverse :=
  { toEquiv := ⟨swap,swap,swap_twice,swap_twice⟩
    measurable_toFun := swap_preserving.measurable
    measurable_invFun := swap_preserving.measurable }

def reflectEquiv : Transverse ≃ᵐ Transverse :=
  { toEquiv := ⟨reflect,reflect,reflect_twice,reflect_twice⟩
    measurable_toFun := reflect_preserving.measurable
    measurable_invFun := reflect_preserving.measurable }

def fullSwap : Configuration ≃ᵐ Configuration :=
  (MeasurableEquiv.refl ℝ).prodCongr swapEquiv

def fullReflect : Configuration ≃ᵐ Configuration :=
  (MeasurableEquiv.refl ℝ).prodCongr reflectEquiv

theorem fullSwap_apply (x : Configuration) : fullSwap x = (x.1,swap x.2) := rfl
theorem fullReflect_apply (x : Configuration) : fullReflect x = (x.1,reflect x.2) := rfl

theorem fullSwap_preserving : MeasurePreserving fullSwap volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod swap_preserving

theorem fullReflect_preserving : MeasurePreserving fullReflect volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod reflect_preserving

theorem pair_swap (q : Transverse) : pairPolynomial (swap q) = -pairPolynomial q := by
  simp only [pairPolynomial,swap]
  dsimp
  ring

theorem gaussian_swap (α β : ℝ) (q : Transverse) :
    physicalGaussian α β (swap q) = physicalGaussian α β q := by
  simp [physicalGaussian,swap,Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc]
  congr 1
  ring!

theorem gaussian_reflect (α β : ℝ) (q : Transverse) :
    physicalGaussian α β (reflect q) = physicalGaussian α β q := by
  simp [physicalGaussian,reflect,Fin.sum_univ_succ]

theorem odd_integral_zero (f : Configuration → ℂ) (e : Configuration ≃ᵐ Configuration)
    (he : MeasurePreserving e volume volume) (hf : ∀ x, f (e x) = -f x) :
    (∫ x, f x) = 0 := by
  have hi := he.integral_comp e.measurableEmbedding f
  simp_rw [hf] at hi
  rw [integral_neg] at hi
  linear_combination -hi/2

theorem four_integral_zero (f : Configuration → ℂ) (hf : Integrable f volume)
    (hzero : ∀ x, f x+f (fullReflect x)+f (fullSwap x)+f (fullReflect (fullSwap x)) = 0) :
    (∫ x, f x) = 0 := by
  have hr : Integrable (fun x => f (fullReflect x)) volume :=
    fullReflect_preserving.integrable_comp_of_integrable hf
  have hs : Integrable (fun x => f (fullSwap x)) volume :=
    fullSwap_preserving.integrable_comp_of_integrable hf
  have hrs : Integrable (fun x => f (fullReflect (fullSwap x))) volume :=
    fullSwap_preserving.integrable_comp_of_integrable hr
  have hfr : Integrable (fun x => f x+f (fullReflect x)) volume := hf.add hr
  have hfrs : Integrable (fun x => f x+f (fullReflect x)+f (fullSwap x)) volume :=
    hfr.add hs
  have he : (∫ x, f x+f (fullReflect x)+f (fullSwap x)+f (fullReflect (fullSwap x))) = 0 := by
    simp_rw [hzero]
    simp
  rw [integral_add hfrs hrs,integral_add hfr hs,integral_add hf hr,
    fullReflect_preserving.integral_comp fullReflect.measurableEmbedding f,
    fullSwap_preserving.integral_comp fullSwap.measurableEmbedding f,
    fullSwap_preserving.integral_comp fullSwap.measurableEmbedding (fun x => f (fullReflect x)),
    fullReflect_preserving.integral_comp fullReflect.measurableEmbedding f] at he
  linear_combination he/4

#print axioms swap_twice
#print axioms reflect_twice
#print axioms swap_preserving
#print axioms reflect_preserving
#print axioms fullSwap_apply
#print axioms fullReflect_apply
#print axioms fullSwap_preserving
#print axioms fullReflect_preserving
#print axioms pair_swap
#print axioms gaussian_swap
#print axioms gaussian_reflect
#print axioms odd_integral_zero
#print axioms four_integral_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairKineticSymmetries
