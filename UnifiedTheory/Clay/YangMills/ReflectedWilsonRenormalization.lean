/- Exact fixed-smear centering and rescaling in the original Wilson law.
The a^(-4) choice below is a proposed curvature-squared normalization; this
file does not prove a holonomy-to-curvature expansion or its analytic limit. -/
import UnifiedTheory.Clay.YangMills.AffineWilsonSmearing
import UnifiedTheory.Clay.YangMills.PeriodicTimeReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ReflectedWilsonRenormalization
noncomputable section
open MeasureTheory ContinuumControl RegulatedGauge PeriodicLattice4 PeriodicTimeReflection
open AffineWilsonSmearing WilsonSmearedObservable

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def centered (a : ℝ) (plane : Plane) (χ actionCharacter : G → ℂ)
    (beta offset : ℝ) (f : CorrelationTest 1) (U : Configuration (Vertex N) G) : ℂ :=
  observable G N a plane χ 1 f U -
    ∫ V, observable G N a plane χ 1 f V ∂wilsonLaw N G actionCharacter beta offset

def reflectedForm (a : ℝ) (plane : Plane) (χ actionCharacter : G → ℂ)
    (beta offset : ℝ) (f g : CorrelationTest 1) : ℂ :=
  ∫ U, star (centered G N a plane χ actionCharacter beta offset f
    (reflectConfiguration N G U)) * centered G N a plane χ actionCharacter beta offset g U
    ∂wilsonLaw N G actionCharacter beta offset

theorem centered_affine (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center scale : ℂ) (f : CorrelationTest 1) (U : Configuration (Vertex N) G) :
    centered G N a plane (affineCharacter χ center scale) actionCharacter beta offset f U =
      scale * centered G N a plane χ actionCharacter beta offset f U :=
  affine_centered G N a plane χ hcχ actionCharacter haction beta offset center scale f U

/-- A constant identity subtraction cancels from the connected reflected
form; its two legs retain exactly the scalar rescaling factor. -/
theorem reflectedForm_affine (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center scale : ℂ) (f g : CorrelationTest 1) :
    reflectedForm G N a plane (affineCharacter χ center scale) actionCharacter beta offset f g =
      (star scale * scale) * reflectedForm G N a plane χ actionCharacter beta offset f g := by
  unfold reflectedForm
  simp_rw [centered_affine G N a plane χ hcχ actionCharacter haction, star_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => by ring)

/-- This is the proposed a^(-4) normalization for a scalar curvature-squared
insertion. Choosing it does not establish the physical field identification. -/
def proposedCurvatureForm (a : ℝ) (plane : Plane) (χ actionCharacter : G → ℂ)
    (beta offset : ℝ) (center : ℂ) (f g : CorrelationTest 1) : ℂ :=
  reflectedForm G N a plane (affineCharacter χ center (((a^4)⁻¹ : ℝ) : ℂ))
    actionCharacter beta offset f g

theorem bare_eq_eighth_power_rescaled (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hcχ : Continuous χ) (actionCharacter : G → ℂ)
    (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center : ℂ) (f g : CorrelationTest 1) :
    reflectedForm G N a plane χ actionCharacter beta offset f g =
      ((a^8 : ℝ) : ℂ) * proposedCurvatureForm G N a plane χ actionCharacter
        beta offset center f g := by
  unfold proposedCurvatureForm
  rw [reflectedForm_affine G N a plane χ hcχ actionCharacter haction]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, star_inv₀, star_pow,
    Complex.star_def, Complex.conj_ofReal]
  field_simp
  <;> ring

/-- Boundedness of a proposed renormalized fixed-test form NECESSARILY
requires the bare connected form to be O(a^8). No such rate is assumed proved. -/
theorem necessary_bare_bound (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hcχ : Continuous χ) (actionCharacter : G → ℂ)
    (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center : ℂ) (f g : CorrelationTest 1) (M : ℝ)
    (hM : ‖proposedCurvatureForm G N a plane χ actionCharacter beta offset center f g‖ ≤ M) :
    ‖reflectedForm G N a plane χ actionCharacter beta offset f g‖ ≤ a^8 * M := by
  rw [bare_eq_eighth_power_rescaled G N a ha plane χ hcχ actionCharacter haction
    beta offset center f g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ a^8)]
  exact mul_le_mul_of_nonneg_left hM (by positivity)

end
end UnifiedTheory.Clay.YangMills.ReflectedWilsonRenormalization
