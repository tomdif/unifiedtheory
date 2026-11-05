/- An explicit static random-sign hierarchy: even moments are one and odd
moments vanish. It is continuous, normalized, bounded and reflection positive,
but its nonzero connected fluctuation is static. This is a counterexample to
an abstract inference, not an asserted Wilson limit or Yang--Mills model. -/
import UnifiedTheory.Clay.YangMills.OSTemperedDynamics
import UnifiedTheory.Clay.YangMills.FullSchwartzReflection
import UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.OSVacuumSector
import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.StaticSchwartzHierarchy
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion KernelHilbertRealization OSFactorizedCollapse
open SchwartzTranslations CellTranslationCovariance
open scoped NNReal Topology

def moment (m : ℕ) : ℂ := if Even m then 1 else 0

theorem moment_bound (m : ℕ) : ‖moment m‖ ≤ (1 : ℝ≥0) := by
  unfold moment
  split_ifs <;> norm_num

def hierarchy : Hierarchy where
  correlation m := BoundedKernelDistribution.functional volume (fun _ => moment m)
    measurable_const 1 (fun _ => moment_bound m)

theorem hierarchy_apply (m : ℕ) (f : CorrelationTest m) :
    hierarchy.correlation m f = moment m * ∫ x, f x := by
  change (∫ x, moment m * f x) = _
  exact integral_const_mul _ _

theorem normalized (f : CorrelationTest 0) : hierarchy.correlation 0 f = ∫ x, f x := by
  rw [hierarchy_apply]
  simp [moment]

theorem bounded : Bounded hierarchy 1 := by
  intro m f
  simpa only [one_pow] using BoundedKernelDistribution.functional_bound volume
    (fun _ : Configuration m => moment m) measurable_const 1 (fun _ => moment_bound m) f

theorem spacetime_translation (m : ℕ) (v : LocalFields.Spacetime) (f : CorrelationTest m) :
    hierarchy.correlation m (translationCLM (CellSpacetimeTranslation.displacement m v) f) =
      hierarchy.correlation m f := by
  rw [hierarchy_apply, hierarchy_apply]
  congr 1
  exact integral_sub_right_eq_self (fun x => f x) _

theorem stationary : Stationary hierarchy := by
  intro m t f
  rw [hierarchy_apply, hierarchy_apply]
  congr 1
  exact integral_sub_right_eq_self (fun x => f x) _

/-- Even and odd polynomials are the two independent random-sign modes. -/
def amplitude (i : Label) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single (if Even i.1 then 0 else 1) (∫ x, i.2.1 x)

theorem amplitude_shift (t : ℝ≥0) (i : Label) : amplitude (shift t i) = amplitude i := by
  unfold amplitude shift
  dsimp only
  congr 1
  exact integral_sub_right_eq_self (fun x => i.2.1 x) _

theorem amplitude_inner (plane : Plane) (i j : Label) :
    inner ℂ (amplitude i) (amplitude j) = kernel hierarchy plane (i,j) := by
  unfold kernel
  rw [hierarchy_apply, integral_reflectedTensor]
  simp only [amplitude, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  by_cases hi : Even i.1 <;> by_cases hj : Even j.1 <;>
    simp [moment, Nat.even_add, hi, hj]

theorem positive (plane : Plane) : Positive hierarchy plane := by
  have he : kernel hierarchy plane = fun p => inner ℂ (amplitude p.1) (amplitude p.2) := by
    funext p
    exact (amplitude_inner plane p.1 p.2).symm
  rw [Positive, he]
  exact (vectorKernel amplitude).positive

theorem full_positive (plane : Plane) : FullPositiveTimeReflection.Positive hierarchy plane :=
  FullSchwartzReflection.positive_of_positive hierarchy plane (positive plane)

def realization (plane : Plane) :
    Hilbert (positiveKernel hierarchy plane (positive plane)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin 2) :=
  KernelHilbertRealization.realization _ amplitude (amplitude_inner plane)

@[simp] theorem realization_canonical (plane : Plane) (i : Label) :
    realization plane (canonical (positiveKernel hierarchy plane (positive plane)) i) =
      amplitude i :=
  KernelHilbertRealization.realization_canonical _ _ _ i

/-- A concrete normalized smooth test supported strictly between times one
and three, rather than an assumed nonzero positive-time test. -/
def bump : ContDiffBump (timeVector 1 2) := ⟨1/2,1,by norm_num,by norm_num⟩

def witnessTest : CorrelationTest 1 :=
  ((bump.hasCompactSupport_normed (μ := volume)).comp_left
    (show Complex.ofReal 0 = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp bump.contDiff_normed)

@[simp] theorem witnessTest_apply (x : Configuration 1) :
    witnessTest x = (bump.normed volume x : ℂ) := rfl

theorem witness_integral : (∫ x, witnessTest x) = 1 := by
  simp only [witnessTest_apply, integral_complex_ofReal, bump.integral_normed, Complex.ofReal_one]

theorem witness_strict_support (x : Configuration 1) (hx : witnessTest x ≠ 0) (j : Fin 1) :
    1 < PeriodicCellSampling.point 1 j x 0 ∧ PeriodicCellSampling.point 1 j x 0 < 3 := by
  have hx' : x ∈ Function.support (bump.normed volume) := by
    change bump.normed volume x ≠ 0
    exact fun hz => hx (by simp [hz])
  rw [bump.support_normed_eq] at hx'
  have hd : ‖x-timeVector 1 2‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm, bump] using hx'
  have hv := (PiLp.norm_apply_le (x-timeVector 1 2) (j,0)).trans_lt hd
  change ‖x (j,0)-2‖ < 1 at hv
  rw [Real.norm_eq_abs, abs_lt] at hv
  change 1 < x (j,0) ∧ x (j,0) < 3
  constructor <;> linarith

theorem witness_supported : Supported 1 witnessTest := by
  refine ⟨3,fun x hx j => ?_⟩
  have h := witness_strict_support x hx j
  exact ⟨by linarith [h.1],h.2.le⟩

def witnessLabel : Label := ⟨1,witnessTest,witness_supported⟩

theorem amplitude_vacuum : amplitude vacuumLabel = EuclideanSpace.single 0 (1 : ℂ) := by
  have he : (∫ x, vacuumTest x) = 1 := by
    simpa only [OSFactorizedCollapse.amplitude, vacuumLabel, pow_zero, one_mul] using
      OSFactorizedCollapse.amplitude_vacuum 1
  change EuclideanSpace.single (if Even 0 then 0 else 1) (∫ x, vacuumTest x) = _
  rw [he]
  norm_num

theorem amplitude_witness : amplitude witnessLabel = EuclideanSpace.single 1 (1 : ℂ) := by
  change EuclideanSpace.single (if Even 1 then 0 else 1) (∫ x, witnessTest x) = _
  rw [witness_integral]
  norm_num

def witness (plane : Plane) : Hilbert (positiveKernel hierarchy plane (positive plane)) :=
  canonical _ witnessLabel

theorem witness_norm (plane : Plane) : ‖witness plane‖ = 1 := by
  rw [← (realization plane).norm_map]
  change ‖realization plane (canonical _ witnessLabel)‖ = 1
  rw [realization_canonical, amplitude_witness, EuclideanSpace.norm_single, norm_one]

theorem witness_nonzero (plane : Plane) : witness plane ≠ 0 := by
  intro hz
  have h := witness_norm plane
  rw [hz,norm_zero] at h
  norm_num at h

theorem witness_orthogonal (plane : Plane) :
    inner ℂ (OSVacuumSector.vacuum hierarchy plane (positive plane)) (witness plane) = 0 := by
  rw [← (realization plane).inner_map_map]
  change inner ℂ (realization plane (canonical _ vacuumLabel))
    (realization plane (canonical _ witnessLabel)) = 0
  rw [realization_canonical, realization_canonical, amplitude_vacuum, amplitude_witness]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

theorem connected_floor (plane : Plane) :
    KernelHilbertCompletion.connectedVariance (positiveKernel hierarchy plane (positive plane))
      vacuumLabel witnessLabel = 1 := by
  unfold KernelHilbertCompletion.connectedVariance
  change (kernel hierarchy plane (witnessLabel,witnessLabel) -
    kernel hierarchy plane (witnessLabel,vacuumLabel) *
      kernel hierarchy plane (vacuumLabel,witnessLabel)).re = 1
  simp only [← amplitude_inner, amplitude_witness, amplitude_vacuum]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

end
end UnifiedTheory.Clay.YangMills.StaticSchwartzHierarchy
