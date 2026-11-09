import UnifiedTheory.Audit.KFCausalConformal4DConnection
import UnifiedTheory.Audit.KFCausalBDG4DCompactPhysicalTest

/-!
The coordinate covariant wave operator of the actual compact test field.
Both orders of field differentiation are ordinary coordinate derivatives;
the metric inverse and Christoffel symbols are those of the previously
constructed conformal metric.  At the origin this gives eight, and its
temporal curvature coupling gives eight minus six times the parameter.
No causal-domain identification or general curved BDG limit is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DCovariantWaveTest

noncomputable section
open scoped BigOperators
open KFCausalConformal4DDiamondBenchmark
open KFCausalConformal4DConnection
open KFCausalBDG4DCompactPhysicalTest (field axis)

def coordinatePartial (f : Point → ℝ) (i : Fin 4) (p : Point) : ℝ :=
  deriv (fun t => f (shift p i t)) 0

def covariantWave (att spatial : ℝ) (f : Point → ℝ) (p : Point) : ℝ :=
  ∑ i, ∑ j, inverseMetric att spatial p i j *
    (coordinatePartial (coordinatePartial f j) i p -
      ∑ k, christoffel att spatial p k i j * coordinatePartial f k p)

def scalarCurvature (att spatial : ℝ) : ℝ :=
  ∑ b, sign b * ∑ a, sign a * connectionRiemann att spatial a b a b

private theorem shift_axis (i : Fin 4) (s t : ℝ) :
    shift (axis i s) i t = axis i (s + t) := by
  funext j
  by_cases h : j = i <;> simp [shift, axis, h]

private theorem shift_origin (i : Fin 4) (t : ℝ) :
    shift 0 i t = axis i t := by
  funext j
  simp [shift, axis]

private theorem partial_axis (f : Point → ℝ) (i : Fin 4) (s : ℝ) :
    coordinatePartial f i (axis i s) = deriv (fun t => f (axis i t)) s := by
  unfold coordinatePartial
  simp only [shift_axis]
  simpa only [add_zero] using
    deriv_comp_const_add (fun t => f (axis i t)) s 0

theorem diagonal_second (f : Point → ℝ) (i : Fin 4) :
    coordinatePartial (coordinatePartial f i) i 0 =
      deriv (deriv (fun t => f (axis i t))) 0 := by
  change deriv (fun t => coordinatePartial f i (shift 0 i t)) 0 = _
  simp only [shift_origin, partial_axis]

theorem field_partial_origin (i : Fin 4) : coordinatePartial field i 0 = 0 := by
  have hzero : axis i 0 = (0 : Point) := by funext j; simp [axis]
  rw [← hzero, partial_axis]
  rw [(KFCausalBDG4DCompactPhysicalTest.axis_local i).deriv_eq]
  have hd := ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2).const_add 1).add
    ((hasDerivAt_id (0 : ℝ)).pow 4)
  simpa using hd.deriv

theorem field_diagonal_second (i : Fin 4) :
    coordinatePartial (coordinatePartial field i) i 0 = 4 := by
  rw [diagonal_second]
  exact KFCausalBDG4DCompactPhysicalTest.axis_second i

theorem covariant_wave_origin (att spatial : ℝ) :
    covariantWave att spatial field 0 = 8 := by
  simp only [covariantWave, christoffel_origin, zero_mul, Finset.sum_const_zero,
    sub_zero]
  simp only [inverseMetric, omega, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_div, add_zero, one_pow, inv_one, one_mul]
  simp only [eta, ite_mul, zero_mul, if_true,
    field_diagonal_second, sign, Fin.sum_univ_four]
  norm_num [Fin.ext_iff]

theorem scalar_curvature_value (att spatial : ℝ) :
    scalarCurvature att spatial = 6 * att - 18 * spatial :=
  connection_scalar att spatial

theorem temporal_wave_curvature (c : ℝ) :
    covariantWave (2 * c) 0 field 0 -
      scalarCurvature (2 * c) 0 / 2 * field 0 = 8 - 6 * c := by
  rw [covariant_wave_origin, scalar_curvature_value,
    KFCausalBDG4DCompactPhysicalTest.field_zero]
  ring

#print axioms diagonal_second
#print axioms field_partial_origin
#print axioms field_diagonal_second
#print axioms covariant_wave_origin
#print axioms scalar_curvature_value
#print axioms temporal_wave_curvature

end
end UnifiedTheory.Audit.KFCausalConformal4DCovariantWaveTest
