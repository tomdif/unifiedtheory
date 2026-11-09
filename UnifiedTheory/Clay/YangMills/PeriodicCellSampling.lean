/- Explicit measurable cell sampling of spacetime into periodic plaquettes.
This is a bare piecewise-constant interpolation, not an ultraviolet renormalization. -/
import UnifiedTheory.Clay.YangMills.PeriodicLattice4
import UnifiedTheory.Clay.YangMills.ContinuumControl
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicCellSampling
noncomputable section
open MeasureTheory LocalFields PeriodicLattice4

def point (m : ℕ) (j : Fin m) (x : ContinuumControl.Configuration m) : Spacetime :=
  WithLp.toLp 2 (fun μ => x (j, μ))

theorem point_continuous (m : ℕ) (j : Fin m) : Continuous (point m j) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun μ => PiLp.continuous_apply 2 _ (j, μ)))

def vertexSample (N : ℕ) (a : ℝ) (x : Spacetime) : Vertex N :=
  fun μ => (Int.floor (x μ / a) : ZMod N)

theorem vertexSample_measurable (N : ℕ) (a : ℝ) : Measurable (vertexSample N a) := by
  apply measurable_pi_lambda
  intro μ
  have hc : Continuous (fun x : Spacetime => x μ / a) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) μ).div_const a
  exact (measurable_of_countable (fun z : ℤ => (z : ZMod N))).comp
    (Int.measurable_floor.comp hc.measurable)

def sample (N : ℕ) (a : ℝ) (plane : Plane) (x : Spacetime) : PlaquetteIndex N :=
  (vertexSample N a x, plane)

theorem sample_measurable (N : ℕ) (a : ℝ) (plane : Plane) : Measurable (sample N a plane) :=
  (vertexSample_measurable N a).prodMk measurable_const

def sampleConfiguration (m N : ℕ) (a : ℝ) (plane : Plane)
    (x : ContinuumControl.Configuration m) : Fin m → PlaquetteIndex N :=
  fun j => sample N a plane (point m j x)

theorem sampleConfiguration_measurable (m N : ℕ) (a : ℝ) (plane : Plane) :
    Measurable (sampleConfiguration m N a plane) :=
  measurable_pi_lambda _ (fun j => (sample_measurable N a plane).comp (point_continuous m j).measurable)

end
end UnifiedTheory.Clay.YangMills.PeriodicCellSampling
