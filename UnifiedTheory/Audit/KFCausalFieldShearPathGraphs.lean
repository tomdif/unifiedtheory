/- Actual field/shear graphs throughout imaginary-shear interpolation.
The commuted output is differentiated strongly, with its derivative in
the actual shear graph. No unbounded operator interchange is assumed. -/
import UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve
import UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
import UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalFieldShearPathGraphs
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)
open UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)

def state (s : Seed) (P : Weight) : ℝ → Hilbert :=
  input P ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
def firstState (s : Seed) (P : Weight) : ℝ → Hilbert :=
  weightedFirst P ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
def secondState (s : Seed) (P : Weight) : Interval → Hilbert :=
  weightedSecond P ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b

variable (s : Seed) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "g" => KFCausalActualImaginaryShearCurve.input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "jg" => KFCausalActualImaginaryShearCurve.shear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "j2g" => KFCausalActualImaginaryShearCurve.secondShear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "U" => state ε h hε hb s (fieldWeight l i)
local notation "V" => firstState ε h hε hb s (fieldWeight l i)
local notation "T" => secondState ε h hε hb s (fieldWeight l i)
local notation "E" => state ε h hε hb s (slopeWeight l i)
local notation "E1" => firstState ε h hε hb s (slopeWeight l i)
local notation "η" => (-Complex.I*(h:ℂ))

def fieldShear (t : ℝ) : Hilbert := V t+η • E t
def firstShear (t : Interval) : Hilbert := T t+η • E1 t

theorem base_coe (t : Interval) : g t =ᵐ[volume]
    KFCausalImaginaryShearInterpolation.actualPath ε s.a s.α s.β s.p h s.b t := by
  rw [KFCausalActualImaginaryShearCurve.input_eq_state ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t]
  exact KFCausalImaginaryShearPathDomain.actualState_coe s.α s.β s.hα s.hβ s.hw s.b ε s.a s.p h hε s.ha hb t

theorem field_graph (t : Interval) : (g t,U t) ∈ (fieldPower l i).graph := by
  apply (fieldPower_graph l i _ _).mpr
  filter_upwards [input_coe (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    base_coe ε h hε hb s t] with x hu hg
  change U t x = _ at hu
  rw [hu,hg]
  rfl

theorem first_field_graph (t : Interval) : (jg t,V t) ∈ (fieldPower l i).graph := by
  apply (fieldPower_graph l i _ _).mpr
  filter_upwards [weightedFirst_coe (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    KFCausalActualImaginaryShearCurve.shear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t] with x hu hg
  change V t x = _ at hu
  rw [hu,hg]
  change η*((l x.2:ℂ)^(i.val+1)*_) = (l x.2:ℂ)^(i.val+1)*(η*_)
  ring

theorem second_field_graph (t : Interval) : (j2g t,T t) ∈ (fieldPower l i).graph := by
  apply (fieldPower_graph l i _ _).mpr
  filter_upwards [weightedSecond_coe (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    KFCausalActualImaginaryShearCurve.secondShear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t] with x hu hg
  change T t x = _ at hu
  rw [hu,hg]
  change η^2*((l x.2:ℂ)^(i.val+1)*_) = (l x.2:ℂ)^(i.val+1)*(η^2*_)
  ring

theorem derivative_coe (t : Interval) : E t =ᵐ[volume] fun x => powerSlope l i x*g t x := by
  filter_upwards [input_coe (slopeWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    base_coe ε h hε hb s t] with x hu hg
  change E t x = _ at hu
  rw [hu,hg]
  rfl

theorem derivativeFirst_coe (t : Interval) : E1 t =ᵐ[volume] fun x => powerSlope l i x*jg t x := by
  filter_upwards [weightedFirst_coe (slopeWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    KFCausalActualImaginaryShearCurve.shear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t] with x hu hg
  change E1 t x = _ at hu
  rw [hu,hg]
  change η*(powerSlope l i x*_) = powerSlope l i x*(η*_)
  ring

variable (hh : h ≠ 0)
include hh in
theorem field_shear_graph (t : Interval) :
    (U t,fieldShear ε h hε hb s l i t) ∈ (shearMomentum h).graph := by
  exact KFCausalCoherentFieldShearGraph.smooth_power_graph h hh l i
    (KFCausalImaginaryShearInterpolation.actualPath ε s.a s.α s.β s.p h s.b t)
    (KFCausalImaginaryShearInterpolation.path_smooth _ _
      (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε s.a s.p (-h/2) hε
        (KFCausalImaginaryShearCoefficient.half_shift_bound ε h hb))
      (KFCausalImaginaryShearCoefficient.displacement_smooth ε h hε hb) s.α s.β s.b t)
    (g t) (jg t) (U t) (V t) (E t) (base_coe ε h hε hb s t)
    (KFCausalActualImaginaryShearCurve.input_shear_graph ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t)
    (field_graph ε h hε hb s l i t) (first_field_graph ε h hε hb s l i t)
    (derivative_coe ε h hε hb s l i t)

include hh in
theorem first_shear_graph (t : Interval) :
    (V t,firstShear ε h hε hb s l i t) ∈ (shearMomentum h).graph := by
  let A := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε s.a s.p (-h/2)
  let D := KFCausalImaginaryShearCoefficient.displacement ε h
  let φ := KFCausalGaussianSecondShearDifferential.first
    (KFCausalImaginaryShearInterpolation.timeAmplitude A D t)
    (KFCausalImaginaryShearInterpolation.timeScale D t) s.α s.β s.b
  have hs : ContDiff ℝ 1 φ := KFCausalGaussianSecondShearDifferential.first_smooth _ _
    (KFCausalImaginaryShearInterpolation.timeAmplitude_smooth _ _
      (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε s.a s.p (-h/2) hε
        (KFCausalImaginaryShearCoefficient.half_shift_bound ε h hb))
      (KFCausalImaginaryShearCoefficient.displacement_smooth ε h hε hb) t)
    (KFCausalImaginaryShearInterpolation.timeScale_smooth _
      (KFCausalImaginaryShearCoefficient.displacement_smooth ε h hε hb) t) s.α s.β s.b
  exact KFCausalCoherentFieldShearGraph.smooth_power_graph h hh l i (fun x => η*φ x)
    (contDiff_const.mul hs) (jg t) (j2g t) (V t) (T t) (E1 t)
    (KFCausalActualImaginaryShearCurve.shear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t)
    (KFCausalActualImaginaryShearCurve.shear_second_graph ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t)
    (first_field_graph ε h hε hb s l i t) (second_field_graph ε h hε hb s l i t)
    (derivativeFirst_coe ε h hε hb s l i t)

theorem fieldShear_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fieldShear ε h hε hb s l i)
      (coefficientOperator ε h hε hb hh (firstShear ε h hε hb s l i ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hv := weightedFirst_strong_derivative (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t ht
  have hd := (input_strong_derivative (slopeWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t ht).const_smul η
  convert hv.add hd using 1
  simp only [firstShear,secondState,firstState,map_add,map_smul]

omit hh in
theorem fieldShear_continuous : Continuous (fieldShear ε h hε hb s l i) :=
  (weightedFirst_continuous (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b).add
    ((input_continuous (slopeWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b).const_smul η)

include hh in
theorem actual_variation_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    -(h^2/(4*ε))*‖W (E t)‖^2 ≤ deriv
      (KFCausalClockShearPositiveVariation.expectation W U (fieldShear ε h hε hb s l i)) t := by
  apply KFCausalForcedShearVariation.forced_expectation_lower ε h hε hb hh W w hW U
    (fieldShear ε h hε hb s l i) (V t) (firstShear ε h hε hb s l i ⟨t,ht.1.le,ht.2.le⟩) (E t) t
    (input_strong_derivative (fieldWeight l i) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t ht)
    (fieldShear_derivative ε h hε hb s l i hh t ht)
    (field_shear_graph ε h hε hb s l i hh ⟨t,ht.1.le,ht.2.le⟩)
    (first_shear_graph ε h hε hb s l i hh ⟨t,ht.1.le,ht.2.le⟩)
  have hz : η+Complex.I*(h:ℂ) = 0 := by ring
  simp only [fieldShear,add_assoc,← add_smul,hz,zero_smul,add_zero]

#print axioms base_coe
#print axioms field_graph
#print axioms first_field_graph
#print axioms second_field_graph
#print axioms derivative_coe
#print axioms derivativeFirst_coe
#print axioms field_shear_graph
#print axioms first_shear_graph
#print axioms fieldShear_derivative
#print axioms fieldShear_continuous
#print axioms actual_variation_lower
end
end UnifiedTheory.Audit.KFCausalFieldShearPathGraphs
