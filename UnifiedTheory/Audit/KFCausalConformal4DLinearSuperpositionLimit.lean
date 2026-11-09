import UnifiedTheory.Audit.KFCausalConformal4DFullCoordinateOperator

/-! Linear superposition and two-probe curvature extraction for the full
four-coordinate chronological causal-diamond BDG operator on the conformal
curved spacetime patch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DLinearSuperpositionLimit
noncomputable section

open Set MeasureTheory Real Filter Topology
open scoped BigOperators
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DEndpointVolume (volumeDensity endpointVolume)
open KFCausalConformal4DCovariantWaveTest (covariantWave scalarCurvature
  covariant_wave_origin scalar_curvature_value temporal_wave_curvature)
open KFCausalBDG4DCompactPhysicalTest (field field_zero)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalConformal4DFullCoordinateOperator

/-- Pointwise integrand of the full 4D conformal chronological operator for an
arbitrary probe field `ϕ`. -/
def probeIntegrand (rho c : ℝ) (ϕ : Point → ℝ) (p : Point) : ℝ :=
  volumeDensity c p * f4D (rho * endpointVolume c p) * ϕ p

/-- Outer chronological integral on `pastPatch c` for an arbitrary probe `ϕ`. -/
def probeOuter (rho c : ℝ) (ϕ : Point → ℝ) : ℝ :=
  ∫ p in pastPatch c, probeIntegrand rho c ϕ p

/-- Discrete curved 4D BDG operator at density `rho` and conformal curvature
parameter `c` acting on a probe field `ϕ`. -/
def actual4DOperator (rho c : ℝ) (ϕ : Point → ℝ) : ℝ :=
  (4 / sqrt 6) * sqrt rho * (rho * probeOuter rho c ϕ - ϕ 0)

/-- Small-scale parameterization `ε ↦ actual4DOperator ε⁻¹ c ϕ` for `ε → 0⁺`. -/
def scaleOperator (ε c : ℝ) (ϕ : Point → ℝ) : ℝ :=
  actual4DOperator ε⁻¹ c ϕ

/-- Continuum wave-curvature operator `□_g ϕ(0) - (1/2) R(0) ϕ(0)` at the origin
of the 4D conformal spacetime. -/
def continuumWaveCurvature (c : ℝ) (ϕ : Point → ℝ) : ℝ :=
  covariantWave (2 * c) 0 ϕ 0 - scalarCurvature (2 * c) 0 / 2 * ϕ 0

/-- Pointwise linear combination `a * ϕ₁ + b * ϕ₂` of two probe fields. -/
def linearCombo (a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ) : Point → ℝ :=
  fun p => a * ϕ₁ p + b * ϕ₂ p

/-- Identically zero probe field. -/
def zeroProbe : Point → ℝ := fun _ => 0

theorem probeIntegrand_field_eq (rho c : ℝ) :
    probeIntegrand rho c field = actualIntegrand rho c := rfl

theorem probeOuter_field_eq (rho c : ℝ) :
    probeOuter rho c field = fullOuter rho c := rfl

theorem actual4DOperator_field_eq (rho c : ℝ) :
    actual4DOperator rho c field = fullOperator rho c := rfl

theorem probeIntegrand_zero (rho c : ℝ) (p : Point) :
    probeIntegrand rho c zeroProbe p = 0 := by
  simp [probeIntegrand, zeroProbe]

theorem probeIntegrand_zero_integrable (rho c : ℝ) :
    IntegrableOn (probeIntegrand rho c zeroProbe) (pastPatch c) := by
  have heq : probeIntegrand rho c zeroProbe = fun _ => (0 : ℝ) :=
    funext (probeIntegrand_zero rho c)
  rw [heq]
  exact integrableOn_zero

theorem probeOuter_zero (rho c : ℝ) :
    probeOuter rho c zeroProbe = 0 := by
  simp [probeOuter, probeIntegrand_zero]

theorem actual4DOperator_zero (rho c : ℝ) :
    actual4DOperator rho c zeroProbe = 0 := by
  simp [actual4DOperator, probeOuter_zero, zeroProbe]

theorem probeIntegrand_smul (rho c a : ℝ) (ϕ : Point → ℝ) (p : Point) :
    probeIntegrand rho c (fun q => a * ϕ q) p = a * probeIntegrand rho c ϕ p := by
  unfold probeIntegrand
  ring

theorem probeIntegrand_linear (rho c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ) (p : Point) :
    probeIntegrand rho c (linearCombo a b ϕ₁ ϕ₂) p =
      a * probeIntegrand rho c ϕ₁ p + b * probeIntegrand rho c ϕ₂ p := by
  unfold probeIntegrand linearCombo
  ring

theorem probeIntegrand_integrable_smul (rho c a : ℝ) (ϕ : Point → ℝ)
    (hϕ : IntegrableOn (probeIntegrand rho c ϕ) (pastPatch c)) :
    IntegrableOn (probeIntegrand rho c (fun q => a * ϕ q)) (pastPatch c) := by
  have heq : probeIntegrand rho c (fun q => a * ϕ q) =
      fun p => a * probeIntegrand rho c ϕ p :=
    funext (probeIntegrand_smul rho c a ϕ)
  rw [heq]
  exact hϕ.const_mul a

theorem probeIntegrand_integrable_linear (rho c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : IntegrableOn (probeIntegrand rho c ϕ₁) (pastPatch c))
    (h₂ : IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c)) :
    IntegrableOn (probeIntegrand rho c (linearCombo a b ϕ₁ ϕ₂)) (pastPatch c) := by
  have heq : probeIntegrand rho c (linearCombo a b ϕ₁ ϕ₂) =
      fun p => a * probeIntegrand rho c ϕ₁ p + b * probeIntegrand rho c ϕ₂ p :=
    funext (probeIntegrand_linear rho c a b ϕ₁ ϕ₂)
  rw [heq]
  exact (h₁.const_mul a).add (h₂.const_mul b)

theorem probeOuter_smul (rho c a : ℝ) (ϕ : Point → ℝ) :
    probeOuter rho c (fun q => a * ϕ q) = a * probeOuter rho c ϕ := by
  unfold probeOuter
  simp_rw [probeIntegrand_smul]
  exact integral_const_mul a _

theorem actual4DOperator_smul (rho c a : ℝ) (ϕ : Point → ℝ) :
    actual4DOperator rho c (fun q => a * ϕ q) = a * actual4DOperator rho c ϕ := by
  unfold actual4DOperator
  rw [probeOuter_smul]
  ring

theorem probeOuter_linear (rho c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : IntegrableOn (probeIntegrand rho c ϕ₁) (pastPatch c))
    (h₂ : IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c)) :
    probeOuter rho c (linearCombo a b ϕ₁ ϕ₂) =
      a * probeOuter rho c ϕ₁ + b * probeOuter rho c ϕ₂ := by
  unfold probeOuter
  have heq : probeIntegrand rho c (linearCombo a b ϕ₁ ϕ₂) =
      fun p => a * probeIntegrand rho c ϕ₁ p + b * probeIntegrand rho c ϕ₂ p :=
    funext (probeIntegrand_linear rho c a b ϕ₁ ϕ₂)
  rw [heq, integral_add (h₁.const_mul a) (h₂.const_mul b),
    integral_const_mul, integral_const_mul]

theorem actual4DOperator_linear (rho c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : IntegrableOn (probeIntegrand rho c ϕ₁) (pastPatch c))
    (h₂ : IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c)) :
    actual4DOperator rho c (linearCombo a b ϕ₁ ϕ₂) =
      a * actual4DOperator rho c ϕ₁ + b * actual4DOperator rho c ϕ₂ := by
  unfold actual4DOperator
  rw [probeOuter_linear rho c a b ϕ₁ ϕ₂ h₁ h₂]
  unfold linearCombo
  ring

theorem scaleOperator_linear (ε c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : IntegrableOn (probeIntegrand ε⁻¹ c ϕ₁) (pastPatch c))
    (h₂ : IntegrableOn (probeIntegrand ε⁻¹ c ϕ₂) (pastPatch c)) :
    scaleOperator ε c (linearCombo a b ϕ₁ ϕ₂) =
      a * scaleOperator ε c ϕ₁ + b * scaleOperator ε c ϕ₂ :=
  actual4DOperator_linear ε⁻¹ c a b ϕ₁ ϕ₂ h₁ h₂

theorem probeIntegrand_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (rho c : ℝ) (p : Point) :
    probeIntegrand rho c (fun q => ∑ i ∈ s, w i * Φ i q) p =
      ∑ i ∈ s, w i * probeIntegrand rho c (Φ i) p := by
  unfold probeIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem probeIntegrand_integrable_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (rho c : ℝ)
    (hΦ : ∀ i ∈ s, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c)) :
    IntegrableOn (probeIntegrand rho c (fun q => ∑ i ∈ s, w i * Φ i q)) (pastPatch c) := by
  have heq : probeIntegrand rho c (fun q => ∑ i ∈ s, w i * Φ i q) =
      fun p => ∑ i ∈ s, w i * probeIntegrand rho c (Φ i) p :=
    funext (probeIntegrand_finset_sum s w Φ rho c)
  rw [heq]
  exact integrable_finset_sum s (fun i hi => (hΦ i hi).const_mul (w i))

theorem probeOuter_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (rho c : ℝ)
    (hΦ : ∀ i ∈ s, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c)) :
    probeOuter rho c (fun q => ∑ i ∈ s, w i * Φ i q) =
      ∑ i ∈ s, w i * probeOuter rho c (Φ i) := by
  unfold probeOuter
  have heq : probeIntegrand rho c (fun q => ∑ i ∈ s, w i * Φ i q) =
      fun p => ∑ i ∈ s, w i * probeIntegrand rho c (Φ i) p :=
    funext (probeIntegrand_finset_sum s w Φ rho c)
  rw [heq, integral_finset_sum s (fun i hi => (hΦ i hi).const_mul (w i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul (w i) _

theorem actual4DOperator_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (rho c : ℝ)
    (hΦ : ∀ i ∈ s, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c)) :
    actual4DOperator rho c (fun q => ∑ i ∈ s, w i * Φ i q) =
      ∑ i ∈ s, w i * actual4DOperator rho c (Φ i) := by
  unfold actual4DOperator
  rw [probeOuter_finset_sum s w Φ rho c hΦ]
  simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actual4DOperator_linear_tendsto (c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₁) (pastPatch c))
    (h₂ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c))
    (ht₁ : Tendsto (fun rho => actual4DOperator rho c ϕ₁) atTop
      (𝓝 (continuumWaveCurvature c ϕ₁)))
    (ht₂ : Tendsto (fun rho => actual4DOperator rho c ϕ₂) atTop
      (𝓝 (continuumWaveCurvature c ϕ₂))) :
    Tendsto (fun rho => actual4DOperator rho c (linearCombo a b ϕ₁ ϕ₂)) atTop
      (𝓝 (a * continuumWaveCurvature c ϕ₁ + b * continuumWaveCurvature c ϕ₂)) := by
  have heq : (fun rho => actual4DOperator rho c (linearCombo a b ϕ₁ ϕ₂)) =
      fun rho => a * actual4DOperator rho c ϕ₁ + b * actual4DOperator rho c ϕ₂ :=
    funext (fun rho => actual4DOperator_linear rho c a b ϕ₁ ϕ₂ (h₁ rho) (h₂ rho))
  rw [heq]
  exact (ht₁.const_mul a).add (ht₂.const_mul b)

theorem scaleOperator_linear_tendsto (c a b : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (h₁ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₁) (pastPatch c))
    (h₂ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c))
    (ht₁ : Tendsto (fun rho => actual4DOperator rho c ϕ₁) atTop
      (𝓝 (continuumWaveCurvature c ϕ₁)))
    (ht₂ : Tendsto (fun rho => actual4DOperator rho c ϕ₂) atTop
      (𝓝 (continuumWaveCurvature c ϕ₂))) :
    Tendsto (fun ε => scaleOperator ε c (linearCombo a b ϕ₁ ϕ₂)) (𝓝[>] (0 : ℝ))
      (𝓝 (a * continuumWaveCurvature c ϕ₁ + b * continuumWaveCurvature c ϕ₂)) := by
  exact (actual4DOperator_linear_tendsto c a b ϕ₁ ϕ₂ h₁ h₂ ht₁ ht₂).comp
    tendsto_inv_nhdsGT_zero

theorem actual4DOperator_field_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => actual4DOperator rho c field) atTop
      (𝓝 (continuumWaveCurvature c field)) := by
  simpa [actual4DOperator_field_eq, continuumWaveCurvature] using
    full_operator_covariant_limit c hc

theorem scaleOperator_field_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun ε => scaleOperator ε c field) (𝓝[>] (0 : ℝ))
      (𝓝 (continuumWaveCurvature c field)) :=
  (actual4DOperator_field_tendsto c hc).comp tendsto_inv_nhdsGT_zero

theorem actual4DOperator_scaled_field_tendsto (c a : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => actual4DOperator rho c (fun p => a * field p)) atTop
      (𝓝 (a * continuumWaveCurvature c field)) := by
  simp_rw [actual4DOperator_smul]
  exact (actual4DOperator_field_tendsto c hc).const_mul a

theorem scaleOperator_scaled_field_tendsto (c a : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun ε => scaleOperator ε c (fun p => a * field p)) (𝓝[>] (0 : ℝ))
      (𝓝 (a * continuumWaveCurvature c field)) :=
  (actual4DOperator_scaled_field_tendsto c a hc).comp tendsto_inv_nhdsGT_zero

theorem continuumWaveCurvature_field (c : ℝ) :
    continuumWaveCurvature c field = 8 - 6 * c :=
  temporal_wave_curvature c

/-- Exact separation of the covariant wave operator `□_g field(0) = 8` from the
Ricci scalar coupling `-(1/2) R(0)` by subtracting a homogeneous probe `ϕ₂`
satisfying `ϕ₂ 0 = 1` and `□_g ϕ₂(0) = 0`. -/
theorem two_probe_wave_separation (c : ℝ) (ϕ₂ : Point → ℝ)
    (hval : ϕ₂ 0 = 1) (hwave : covariantWave (2 * c) 0 ϕ₂ 0 = 0) :
    continuumWaveCurvature c field - continuumWaveCurvature c ϕ₂ =
      covariantWave (2 * c) 0 field 0 ∧
    continuumWaveCurvature c field - continuumWaveCurvature c ϕ₂ = 8 := by
  have heq : continuumWaveCurvature c field - continuumWaveCurvature c ϕ₂ =
      covariantWave (2 * c) 0 field 0 := by
    unfold continuumWaveCurvature
    rw [field_zero, hval, hwave]
    ring
  exact ⟨heq, heq.trans (covariant_wave_origin (2 * c) 0)⟩

/-- Exact extraction of the Ricci scalar curvature coupling `-(1/2) R(0) = -6c`
and the scalar curvature `R(0) = 12c` from a homogeneous probe `ϕ₂` satisfying
`ϕ₂ 0 = 1` and `□_g ϕ₂(0) = 0`. -/
theorem two_probe_ricci_coupling_extraction (c : ℝ) (ϕ₂ : Point → ℝ)
    (hval : ϕ₂ 0 = 1) (hwave : covariantWave (2 * c) 0 ϕ₂ 0 = 0) :
    continuumWaveCurvature c ϕ₂ = -(1 / 2) * scalarCurvature (2 * c) 0 ∧
    (-2) * continuumWaveCurvature c ϕ₂ = scalarCurvature (2 * c) 0 ∧
    (-2) * continuumWaveCurvature c ϕ₂ = 12 * c := by
  have h1 : continuumWaveCurvature c ϕ₂ = -(1 / 2) * scalarCurvature (2 * c) 0 := by
    unfold continuumWaveCurvature
    rw [hval, hwave]
    ring
  have h2 : (-2) * continuumWaveCurvature c ϕ₂ = scalarCurvature (2 * c) 0 := by
    rw [h1]
    ring
  have h3 : (-2) * continuumWaveCurvature c ϕ₂ = 12 * c := by
    rw [h2, scalar_curvature_value]
    ring
  exact ⟨h1, h2, h3⟩

/-- General two-probe curvature extraction formula: for any two unit-normalized
probes `ϕ₁ 0 = 1, ϕ₂ 0 = 1` with distinct wave values `w₁ ≠ w₂` at the origin,
the linear combination `(-w₂ / (w₁ - w₂)) * L(ϕ₁) + (w₁ / (w₁ - w₂)) * L(ϕ₂)`
cancels the wave terms and isolates `-(1/2) R(0)`. -/
theorem two_probe_general_curvature_extraction (c : ℝ) (ϕ₁ ϕ₂ : Point → ℝ)
    (hval₁ : ϕ₁ 0 = 1) (hval₂ : ϕ₂ 0 = 1)
    (hw : covariantWave (2 * c) 0 ϕ₁ 0 ≠ covariantWave (2 * c) 0 ϕ₂ 0) :
    (-covariantWave (2 * c) 0 ϕ₂ 0 /
        (covariantWave (2 * c) 0 ϕ₁ 0 - covariantWave (2 * c) 0 ϕ₂ 0)) *
      continuumWaveCurvature c ϕ₁ +
    (covariantWave (2 * c) 0 ϕ₁ 0 /
        (covariantWave (2 * c) 0 ϕ₁ 0 - covariantWave (2 * c) 0 ϕ₂ 0)) *
      continuumWaveCurvature c ϕ₂ =
      -(1 / 2) * scalarCurvature (2 * c) 0 := by
  have hsub : covariantWave (2 * c) 0 ϕ₁ 0 - covariantWave (2 * c) 0 ϕ₂ 0 ≠ 0 :=
    sub_ne_zero.mpr hw
  unfold continuumWaveCurvature
  rw [hval₁, hval₂]
  field_simp [hsub]
  ring

/-- Continuum limit of the two-probe difference `field - ϕ₂`, converging to the
pure flat wave value `□_g field(0) = 8` as `rho → ∞` and as `ε → 0⁺`. -/
theorem two_probe_wave_separation_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54)
    (ϕ₂ : Point → ℝ)
    (h₂ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c))
    (ht₂ : Tendsto (fun rho => actual4DOperator rho c ϕ₂) atTop
      (𝓝 (continuumWaveCurvature c ϕ₂)))
    (hval : ϕ₂ 0 = 1) (hwave : covariantWave (2 * c) 0 ϕ₂ 0 = 0) :
    Tendsto (fun rho => actual4DOperator rho c (linearCombo 1 (-1) field ϕ₂)) atTop
      (𝓝 (covariantWave (2 * c) 0 field 0)) ∧
    Tendsto (fun ε => scaleOperator ε c (linearCombo 1 (-1) field ϕ₂)) (𝓝[>] (0 : ℝ))
      (𝓝 (covariantWave (2 * c) 0 field 0)) := by
  have hlim := actual4DOperator_linear_tendsto c 1 (-1) field ϕ₂
    (fun rho => actual_integrable rho c hc) h₂
    (actual4DOperator_field_tendsto c hc) ht₂
  have htarget : 1 * continuumWaveCurvature c field + (-1) * continuumWaveCurvature c ϕ₂ =
      covariantWave (2 * c) 0 field 0 := by
    linarith [(two_probe_wave_separation c ϕ₂ hval hwave).1]
  rw [htarget] at hlim
  exact ⟨hlim, hlim.comp tendsto_inv_nhdsGT_zero⟩

/-- Continuum limit of the curvature-isolating probe combination, converging to
the scalar curvature `R(0) = 12c` as `rho → ∞` and as `ε → 0⁺`. -/
theorem two_probe_curvature_extraction_tendsto (c : ℝ) (hc : |c| ≤ 1 / 54)
    (ϕ₂ : Point → ℝ)
    (h₂ : ∀ rho, IntegrableOn (probeIntegrand rho c ϕ₂) (pastPatch c))
    (ht₂ : Tendsto (fun rho => actual4DOperator rho c ϕ₂) atTop
      (𝓝 (continuumWaveCurvature c ϕ₂)))
    (hval : ϕ₂ 0 = 1) (hwave : covariantWave (2 * c) 0 ϕ₂ 0 = 0) :
    Tendsto (fun rho => actual4DOperator rho c (linearCombo 0 (-2) field ϕ₂)) atTop
      (𝓝 (scalarCurvature (2 * c) 0)) ∧
    Tendsto (fun ε => scaleOperator ε c (linearCombo 0 (-2) field ϕ₂)) (𝓝[>] (0 : ℝ))
      (𝓝 (scalarCurvature (2 * c) 0)) := by
  have hlim := actual4DOperator_linear_tendsto c 0 (-2) field ϕ₂
    (fun rho => actual_integrable rho c hc) h₂
    (actual4DOperator_field_tendsto c hc) ht₂
  have htarget : 0 * continuumWaveCurvature c field + (-2) * continuumWaveCurvature c ϕ₂ =
      scalarCurvature (2 * c) 0 := by
    linarith [(two_probe_ricci_coupling_extraction c ϕ₂ hval hwave).2.1]
  rw [htarget] at hlim
  exact ⟨hlim, hlim.comp tendsto_inv_nhdsGT_zero⟩

#print axioms probeIntegrand_field_eq
#print axioms probeOuter_field_eq
#print axioms actual4DOperator_field_eq
#print axioms probeIntegrand_zero
#print axioms probeIntegrand_zero_integrable
#print axioms probeOuter_zero
#print axioms actual4DOperator_zero
#print axioms probeIntegrand_smul
#print axioms probeIntegrand_linear
#print axioms probeIntegrand_integrable_smul
#print axioms probeIntegrand_integrable_linear
#print axioms probeOuter_smul
#print axioms actual4DOperator_smul
#print axioms probeOuter_linear
#print axioms actual4DOperator_linear
#print axioms scaleOperator_linear
#print axioms probeIntegrand_finset_sum
#print axioms probeIntegrand_integrable_finset_sum
#print axioms probeOuter_finset_sum
#print axioms actual4DOperator_finset_sum
#print axioms actual4DOperator_linear_tendsto
#print axioms scaleOperator_linear_tendsto
#print axioms actual4DOperator_field_tendsto
#print axioms scaleOperator_field_tendsto
#print axioms actual4DOperator_scaled_field_tendsto
#print axioms scaleOperator_scaled_field_tendsto
#print axioms continuumWaveCurvature_field
#print axioms two_probe_wave_separation
#print axioms two_probe_ricci_coupling_extraction
#print axioms two_probe_general_curvature_extraction
#print axioms two_probe_wave_separation_tendsto
#print axioms two_probe_curvature_extraction_tendsto

end
end UnifiedTheory.Audit.KFCausalConformal4DLinearSuperpositionLimit
