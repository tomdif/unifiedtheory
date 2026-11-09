/- Gauge averaging and symmetry for the actual Wilson time-slab kernel.
The normalized temporal product-Haar average is an idempotent projection onto
gauge-invariant functions. Its spatial-Haar pairing is symmetric and its
quadratic form is the integral of a square for continuous real tests. The full
kernel, including both spatial plaquette factors and temporal integration, is
symmetric for unitary characters and gauge-invariant in each argument.
These finite-cutoff statements do not establish compactness, a positive
transfer eigenpair, a cutoff-uniform spectral gap, or a continuum theory. -/
import UnifiedTheory.Clay.YangMills.WilsonTimeSlab
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabGauge
noncomputable section
open MeasureTheory RegulatedGauge WilsonTimeSlab

variable {n : ℕ} {G : Type*} [Group G]

theorem gaugeSlice_one (u : SpatialLinks n G) : gaugeSlice 1 u = u := by
  funext e
  simp [gaugeSlice]

theorem gaugeSlice_mul (h k : SliceGauge n G) (u : SpatialLinks n G) :
    gaugeSlice (h * k) u = gaugeSlice h (gaugeSlice k u) := by
  funext e
  simp [gaugeSlice, mul_assoc]

theorem gaugeSlice_inv (h : SliceGauge n G) (u : SpatialLinks n G) :
    gaugeSlice h⁻¹ (gaugeSlice h u) = u := by
  rw [← gaugeSlice_mul, inv_mul_cancel, gaugeSlice_one]

theorem spatialStep_comm (x : SpatialVertex n) (i j : Fin 3) :
    spatialStep n (spatialStep n x i) j = spatialStep n (spatialStep n x j) i := by
  simp only [spatialStep]
  abel

theorem spatialHolonomy_gauge (h : SliceGauge n G) (u : SpatialLinks n G)
    (x : SpatialVertex n) (i j : Fin 3) :
    spatialHolonomy (gaugeSlice h u) x i j =
      h x * spatialHolonomy u x i j * (h x)⁻¹ := by
  simp only [spatialHolonomy, gaugeSlice, spatialStep_comm (n := n) x j i]
  group

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem unitaryCharacter_class (ρ : G →* Matrix.unitaryGroup d ℂ) :
    ClassFunction G (WilsonCrossingKernel.unitaryCharacter ρ) := by
  exact matrixCharacter_class G (Unitary.toUnits.comp ρ)

theorem unitaryCharacter_inv_re (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    (WilsonCrossingKernel.unitaryCharacter ρ g⁻¹).re =
      (WilsonCrossingKernel.unitaryCharacter ρ g).re := by
  simp [WilsonCrossingKernel.unitaryCharacter, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]

variable [NeZero n]

theorem potential_gauge (χ : G → ℂ) (hχ : ClassFunction G χ) (c : ℝ)
    (h : SliceGauge n G) (u : SpatialLinks n G) :
    potential χ c (gaugeSlice h u) = potential χ c u := by
  unfold ClassFunction at hχ
  simp only [potential, spatialHolonomy_gauge, hχ]

theorem spatialWeight_gauge (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (h : SliceGauge n G) (u : SpatialLinks n G) :
    spatialWeight χ β c (gaugeSlice h u) = spatialWeight χ β c u := by
  rw [spatialWeight, potential_gauge χ hχ]
  rfl

theorem kineticAction_gauge (χ : G → ℂ) (hχ : ClassFunction G χ) (c : ℝ)
    (h : SliceGauge n G) (u v : SpatialLinks n G) :
    kineticAction χ c (gaugeSlice h u) (gaugeSlice h v) = kineticAction χ c u v := by
  apply Finset.sum_congr rfl
  intro e _
  have he : (gaugeSlice h u e)⁻¹ * gaugeSlice h v e =
      h (spatialStep n e.1 e.2) * ((u e)⁻¹ * v e) *
        (h (spatialStep n e.1 e.2))⁻¹ := by
    simp only [gaugeSlice]
    group
  rw [he, hχ]

theorem kineticAction_symm (χ : G → ℂ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (c : ℝ) (u v : SpatialLinks n G) :
    kineticAction χ c u v = kineticAction χ c v u := by
  apply Finset.sum_congr rfl
  intro e _
  have hi := hinv ((u e)⁻¹ * v e)
  simpa using congrArg (fun x : ℝ => c - x) hi.symm

theorem kineticWeight_gauge (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (h : SliceGauge n G) (u v : SpatialLinks n G) :
    kineticWeight χ β c (gaugeSlice h u) (gaugeSlice h v) = kineticWeight χ β c u v := by
  rw [kineticWeight, kineticAction_gauge χ hχ]
  rfl

theorem kineticWeight_symm (χ : G → ℂ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ) (u v : SpatialLinks n G) :
    kineticWeight χ β c u v = kineticWeight χ β c v u := by
  rw [kineticWeight, kineticAction_symm χ hinv]
  rfl

theorem kineticWeight_reverse (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (u v : SpatialLinks n G) (h : SliceGauge n G) :
    kineticWeight χ β c u (gaugeSlice h v) =
      kineticWeight χ β c v (gaugeSlice h⁻¹ u) := by
  rw [← kineticWeight_gauge χ hχ β c h⁻¹ u (gaugeSlice h v), gaugeSlice_inv,
    kineticWeight_symm χ hinv]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance compactHaar_inv : (compactHaar G).IsInvInvariant := by
  letI : IsProbabilityMeasure (compactHaar G).inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  constructor
  exact ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts G)
    (compactHaar G).inv).2 (by simp)).symm

local instance temporalHaar_left :
    (temporalHaar (n := n) (G := G)).IsMulLeftInvariant := by
  unfold temporalHaar
  infer_instance

local instance temporalHaar_right :
    (temporalHaar (n := n) (G := G)).IsMulRightInvariant := by
  unfold temporalHaar
  infer_instance

local instance temporalHaar_inv :
    (temporalHaar (n := n) (G := G)).IsInvInvariant := by
  unfold temporalHaar
  infer_instance

/-- Independent normalized Haar measure on the actual spatial slice. -/
def spatialHaar : Measure (SpatialLinks n G) :=
  Measure.pi (fun _ : SpatialVertex n × Fin 3 => compactHaar G)

instance spatialHaar_probability : IsProbabilityMeasure (spatialHaar (n := n) (G := G)) := by
  unfold spatialHaar
  infer_instance

def gaugeHomeomorph (h : SliceGauge n G) : SpatialLinks n G ≃ₜ SpatialLinks n G where
  toFun := gaugeSlice h
  invFun := gaugeSlice h⁻¹
  left_inv := gaugeSlice_inv h
  right_inv u := by simpa only [inv_inv] using gaugeSlice_inv h⁻¹ u
  continuous_toFun := by unfold gaugeSlice; fun_prop
  continuous_invFun := by unfold gaugeSlice; fun_prop

theorem gauge_preserves_spatial (h : SliceGauge n G) :
    MeasurePreserving (gaugeSlice h) spatialHaar spatialHaar := by
  exact measurePreserving_pi
    (fun _ : SpatialVertex n × Fin 3 => compactHaar G)
    (fun _ : SpatialVertex n × Fin 3 => compactHaar G)
    (fun e => (measurePreserving_mul_right (compactHaar G)
      (h (spatialStep n e.1 e.2))⁻¹).comp
        (measurePreserving_mul_left (compactHaar G) (h e.1)))

/-- Actual normalized product-Haar projection onto gauge-invariant functions. -/
def gaugeAverage (f : SpatialLinks n G → ℝ) (u : SpatialLinks n G) : ℝ :=
  ∫ h, f (gaugeSlice h u) ∂temporalHaar

theorem gaugeAverage_invariant (f : SpatialLinks n G → ℝ)
    (k : SliceGauge n G) (u : SpatialLinks n G) :
    gaugeAverage f (gaugeSlice k u) = gaugeAverage f u := by
  simp only [gaugeAverage, ← gaugeSlice_mul]
  exact integral_mul_right_eq_self (fun h => f (gaugeSlice h u)) k

omit [SecondCountableTopology G] in
theorem gaugeAverage_fixed (f : SpatialLinks n G → ℝ)
    (hf : ∀ h u, f (gaugeSlice h u) = f u) (u : SpatialLinks n G) :
    gaugeAverage f u = f u := by
  simp only [gaugeAverage, hf, integral_const, probReal_univ, one_smul]

theorem gaugeAverage_idempotent (f : SpatialLinks n G → ℝ) :
    gaugeAverage (gaugeAverage f) = gaugeAverage f := by
  funext u
  exact gaugeAverage_fixed _ (gaugeAverage_invariant f) u

theorem gaugeAverage_continuous (f : SpatialLinks n G → ℝ) (hf : Continuous f) :
    Continuous (gaugeAverage f) := by
  have hc : Continuous (fun uh : SpatialLinks n G × SliceGauge n G =>
      f (gaugeSlice uh.2 uh.1)) := by
    unfold gaugeSlice
    fun_prop
  simpa only [Measure.restrict_univ, gaugeAverage] using
    (continuous_parametric_integral_of_continuous (μ := temporalHaar) hc isCompact_univ)

theorem gauge_pairing_translate (f g : SpatialLinks n G → ℝ)
    (h : SliceGauge n G) :
    (∫ u, f u * g (gaugeSlice h u) ∂spatialHaar) =
      ∫ u, f (gaugeSlice h⁻¹ u) * g u ∂spatialHaar := by
  have he := (gauge_preserves_spatial h).integral_comp
    (gaugeHomeomorph h).measurableEmbedding
    (fun u => f (gaugeSlice h⁻¹ u) * g u)
  simpa only [gaugeHomeomorph, Equiv.coe_fn_mk, gaugeSlice_inv] using he

/-- Gauge averaging is symmetric for the actual spatial product-Haar pairing. -/
theorem gaugeAverage_pairing (f g : SpatialLinks n G → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ u, f u * gaugeAverage g u ∂spatialHaar) =
      ∫ u, gaugeAverage f u * g u ∂spatialHaar := by
  have hi : Integrable (fun uh : SpatialLinks n G × SliceGauge n G =>
      f uh.1 * g (gaugeSlice uh.2 uh.1)) (spatialHaar.prod temporalHaar) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold gaugeSlice
    fun_prop
  have hj : Integrable (fun uh : SpatialLinks n G × SliceGauge n G =>
      f (gaugeSlice uh.2 uh.1) * g uh.1) (spatialHaar.prod temporalHaar) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold gaugeSlice
    fun_prop
  calc
    _ = ∫ u, ∫ h, f u * g (gaugeSlice h u) ∂temporalHaar ∂spatialHaar := by
      simp only [gaugeAverage, integral_const_mul]
    _ = ∫ h, ∫ u, f u * g (gaugeSlice h u) ∂spatialHaar ∂temporalHaar :=
      integral_integral_swap hi
    _ = ∫ h, ∫ u, f (gaugeSlice h⁻¹ u) * g u ∂spatialHaar ∂temporalHaar := by
      exact integral_congr_ae (Filter.Eventually.of_forall (gauge_pairing_translate f g))
    _ = ∫ h, ∫ u, f (gaugeSlice h u) * g u ∂spatialHaar ∂temporalHaar :=
      integral_inv_eq_self (fun h => ∫ u, f (gaugeSlice h u) * g u ∂spatialHaar) temporalHaar
    _ = ∫ u, ∫ h, f (gaugeSlice h u) * g u ∂temporalHaar ∂spatialHaar :=
      (integral_integral_swap hj).symm
    _ = _ := by simp only [gaugeAverage, integral_mul_const]

/-- The pairing of a function with its gauge projection is a genuine square. -/
theorem gaugeAverage_quadratic (f : SpatialLinks n G → ℝ) (hf : Continuous f) :
    (∫ u, f u * gaugeAverage f u ∂spatialHaar) =
      ∫ u, (gaugeAverage f u) ^ 2 ∂spatialHaar := by
  have he := gaugeAverage_pairing f (gaugeAverage f) hf (gaugeAverage_continuous f hf)
  simpa only [gaugeAverage_idempotent, pow_two] using he

theorem gaugeAverage_quadratic_nonneg (f : SpatialLinks n G → ℝ) (hf : Continuous f) :
    0 ≤ ∫ u, f u * gaugeAverage f u ∂spatialHaar := by
  rw [gaugeAverage_quadratic f hf]
  exact integral_nonneg (fun u => sq_nonneg _)

theorem kernel_gauge_right (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (u v : SpatialLinks n G) (k : SliceGauge n G) :
    kernel χ β c u (gaugeSlice k v) = kernel χ β c u v := by
  rw [kernel_eq_gauge_average χ hχ, kernel_eq_gauge_average χ hχ,
    spatialWeight_gauge χ hχ]
  congr 2
  exact gaugeAverage_invariant (kineticWeight χ β c u) k v

/-- The full slab kernel, including both spatial weights and temporal Haar
integration, is symmetric. No temporal link is fixed to the identity. -/
theorem kernel_symm (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) (u v : SpatialLinks n G) :
    kernel χ β c u v = kernel χ β c v u := by
  rw [kernel_eq_gauge_average χ hχ, kernel_eq_gauge_average χ hχ]
  have hi : (∫ h, kineticWeight χ β c u (gaugeSlice h v) ∂temporalHaar) =
      ∫ h, kineticWeight χ β c v (gaugeSlice h u) ∂temporalHaar := by
    trans ∫ h, kineticWeight χ β c v (gaugeSlice h⁻¹ u) ∂temporalHaar
    · exact integral_congr_ae (Filter.Eventually.of_forall
        (fun h => kineticWeight_reverse χ hχ hinv β c u v h))
    exact integral_inv_eq_self (fun h => kineticWeight χ β c v (gaugeSlice h u)) temporalHaar
  rw [hi]
  ring

theorem kernel_gauge_left (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (u v : SpatialLinks n G) (k : SliceGauge n G) :
    kernel χ β c (gaugeSlice k u) v = kernel χ β c u v := by
  rw [kernel_symm χ hχ hinv, kernel_gauge_right χ hχ,
    kernel_symm χ hχ hinv β c v u]

theorem unitary_kernel_symm (ρ : G →* Matrix.unitaryGroup d ℂ) (β c : ℝ)
    (u v : SpatialLinks n G) :
    kernel (WilsonCrossingKernel.unitaryCharacter ρ) β c u v =
      kernel (WilsonCrossingKernel.unitaryCharacter ρ) β c v u :=
  kernel_symm _ (unitaryCharacter_class ρ) (unitaryCharacter_inv_re ρ) β c u v

end
end UnifiedTheory.Clay.YangMills.WilsonSlabGauge
