/- Explicit representatives of the actual coupled coordinate unitary and
its inverse on every L2 vector, including noncompact functions. -/
import UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
import UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
import UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
open UnifiedTheory.Audit.KFCausalCoupledTestPullback
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative

def weightedFunction (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  weight ε x*f (coordinateHomeomorph ε hε x)

def inverseFunction (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (weight ε ((coordinateHomeomorph ε hε).symm x))⁻¹*f ((coordinateHomeomorph ε hε).symm x)

theorem coordinates_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    coordinates ε hε f =ᵐ[volume] weightedFunction ε hε f := by
  apply dense_weighted_representative embedding embedding_dense (coordinates ε hε)
    (coordinates ε hε).continuous (coordinateHomeomorph ε hε)
    (coordinate_quasiMeasurePreserving ε hε) (weight ε) _ f
  intro d
  filter_upwards [coordinates_test_representative ε hε d,
    (coordinate_quasiMeasurePreserving ε hε).ae (embedding_coe d)] with x hx hd
  rw [hx,hd]

theorem coordinates_inverse_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (coordinates ε hε).symm f =ᵐ[volume] inverseFunction ε hε f :=
  inverse_weighted_representative (coordinates ε hε) (coordinateHomeomorph ε hε).toMeasurableEquiv
    (coordinate_inverse_quasiMeasurePreserving ε hε) (weight ε) (weight_ne_zero ε hε)
    (coordinates_coe ε hε) f

theorem coordinates_toLp_coe (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    coordinates ε hε (hf.toLp f) =ᵐ[volume] weightedFunction ε hε f := by
  filter_upwards [coordinates_coe ε hε (hf.toLp f),
    (coordinate_quasiMeasurePreserving ε hε).ae hf.coeFn_toLp] with x hx hf'
  change (coordinates ε hε (hf.toLp f)) x = weight ε x*f (coordinateHomeomorph ε hε x)
  rw [hx]
  change weight ε x*(hf.toLp f) (coordinateHomeomorph ε hε x) = _
  rw [hf']

theorem coordinates_inverse_toLp_coe (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    (coordinates ε hε).symm (hf.toLp f) =ᵐ[volume] inverseFunction ε hε f := by
  filter_upwards [coordinates_inverse_coe ε hε (hf.toLp f),
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae hf.coeFn_toLp] with x hx hf'
  rw [hx]
  change (weight ε ((coordinateHomeomorph ε hε).symm x))⁻¹ *
    (hf.toLp f) ((coordinateHomeomorph ε hε).symm x) = _
  rw [hf']
  rfl

theorem weighted_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    MemLp (weightedFunction ε hε f) 2 :=
  (Lp.memLp (coordinates ε hε (hf.toLp f))).ae_eq (coordinates_toLp_coe ε hε f hf)

theorem inverse_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    MemLp (inverseFunction ε hε f) 2 :=
  (Lp.memLp ((coordinates ε hε).symm (hf.toLp f))).ae_eq (coordinates_inverse_toLp_coe ε hε f hf)

theorem inverse_weighted_function (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) :
    inverseFunction ε hε (weightedFunction ε hε f) = f := by
  funext x
  simp only [inverseFunction,weightedFunction,Homeomorph.apply_symm_apply]
  rw [← mul_assoc,inv_mul_cancel₀ (weight_ne_zero ε hε _),one_mul]

theorem weighted_inverse_function (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) :
    weightedFunction ε hε (inverseFunction ε hε f) = f := by
  funext x
  simp only [inverseFunction,weightedFunction,Homeomorph.symm_apply_apply]
  rw [← mul_assoc,mul_inv_cancel₀ (weight_ne_zero ε hε _),one_mul]

theorem weighted_memLp_iff (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) :
    MemLp (weightedFunction ε hε f) 2 ↔ MemLp f 2 := by
  constructor
  · intro hf
    simpa only [inverse_weighted_function] using inverse_memLp ε hε _ hf
  · exact weighted_memLp ε hε f

theorem inverse_memLp_iff (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) :
    MemLp (inverseFunction ε hε f) 2 ↔ MemLp f 2 := by
  constructor
  · intro hf
    simpa only [weighted_inverse_function] using weighted_memLp ε hε _ hf
  · exact inverse_memLp ε hε f

theorem coordinates_toLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    coordinates ε hε (hf.toLp f) = (weighted_memLp ε hε f hf).toLp (weightedFunction ε hε f) := by
  apply Lp.ext
  exact (coordinates_toLp_coe ε hε f hf).trans (weighted_memLp ε hε f hf).coeFn_toLp.symm

theorem coordinates_inverse_toLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    (coordinates ε hε).symm (hf.toLp f) = (inverse_memLp ε hε f hf).toLp (inverseFunction ε hε f) := by
  apply Lp.ext
  exact (coordinates_inverse_toLp_coe ε hε f hf).trans (inverse_memLp ε hε f hf).coeFn_toLp.symm

#print axioms coordinates_coe
#print axioms coordinates_inverse_coe
#print axioms coordinates_toLp_coe
#print axioms coordinates_inverse_toLp_coe
#print axioms weighted_memLp
#print axioms inverse_memLp
#print axioms inverse_weighted_function
#print axioms weighted_inverse_function
#print axioms weighted_memLp_iff
#print axioms inverse_memLp_iff
#print axioms coordinates_toLp
#print axioms coordinates_inverse_toLp

end
end UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
