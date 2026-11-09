import UnifiedTheory.Audit.KFCausalConformal4DLinearSuperpositionLimit
import UnifiedTheory.Audit.KFCausalConformal4DLorentzianBianchiTraceSynthesis

/-! Anisotropic multi-axis spatial probes, finite-sum superposition linearity,
and axis-by-axis decomposition of the 4D Lorentzian wave operator, Ricci tensor,
scalar curvature, and Einstein tensor on the conformal curved spacetime patch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DAnisotropicSpatialProbeSynthesis
noncomputable section

open Set MeasureTheory Filter Topology
open scoped Real BigOperators
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric)
open KFCausalConformal4DDiamondBenchmark (Point sign eta coefficient derivativeData)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein)
open KFCausalConformal4DLorentzianBianchiTraceSynthesis (einsteinTrace
  lorentzian_einsteinTrace_eq_neg_scalar)
open KFCausalConformal4DCovariantWaveTest (covariantWave scalarCurvature)
open KFCausalBDG4DCompactPhysicalTest (field axis)
open KFCausalConformal4DFullCoordinateOperator (pastPatch)
open KFCausalConformal4DLinearSuperpositionLimit (probeIntegrand probeOuter
  actual4DOperator scaleOperator continuumWaveCurvature
  probeIntegrand_finset_sum probeIntegrand_integrable_finset_sum
  probeOuter_finset_sum actual4DOperator_finset_sum)

/-- Four-component diagonal second-derivative jet `(∂_t² φ, ∂_x² φ, ∂_y² φ, ∂_z² φ)`
of a 4D conformal factor or probe profile at the origin. -/
abbrev TransformedJet4D := Fin 4 → ℝ

/-- Coordinate-axis basis jet `e_μ` in the 4D diagonal jet space. -/
def jetBasis4D (μ : Fin 4) : TransformedJet4D :=
  fun ν => if ν = μ then 1 else 0

/-- Explicit constructor for a 4D diagonal jet from temporal component `att`
and three spatial axis components `sx, sy, sz`. -/
def mkJet4D (att sx sy sz : ℝ) : TransformedJet4D :=
  ![att, sx, sy, sz]

/-- Isotropic diagonal jet `(att, spatial, spatial, spatial)`. -/
def isotropicJet4D (att spatial : ℝ) : TransformedJet4D :=
  coefficient att spatial

/-- Diagonal second-derivative jet of an arbitrary probe `ϕ : Point → ℝ` along
the four coordinate axes at the origin. -/
def transformedJet4D (ϕ : Point → ℝ) : TransformedJet4D :=
  fun μ => deriv (deriv (fun s => ϕ (axis μ s))) 0

/-- 4D Lorentzian wave operator `□ H = -H₀ + H₁ + H₂ + H₃` on a diagonal jet `H`. -/
def fullCoordinateWaveOperator4D (H : TransformedJet4D) : ℝ :=
  ∑ μ : Fin 4, sign μ * H μ

/-- Spatial Laplacian `Δ₃ H = H₁ + H₂ + H₃` on the three spatial axes. -/
def spatialLaplacian4D (H : TransformedJet4D) : ℝ :=
  H 1 + H 2 + H 3

/-- Spatial anisotropy defect `H_i - (1/3) H₀` along axis `i` relative to one-third
of the temporal second derivative. -/
def spatialAnisotropyDefect (H : TransformedJet4D) (i : Fin 4) : ℝ :=
  H i - (1 / 3) * H 0

/-- Second-derivative metric tensor `∂_e ∂_f g_{ab}(0) = 2 δ_{ef} H_e η_{ab}` for an
anisotropic 4D conformal factor with diagonal Hessian `H`. -/
def anisotropicMetricSecond (H : TransformedJet4D) (e f a b : Fin 4) : ℝ :=
  2 * (if e = f then H e else 0) * eta a b

/-- Normal-coordinate metric derivative data for an anisotropic diagonal 4D
conformal profile `H`. -/
def anisotropicMetricDerivs (H : TransformedJet4D) : MetricDerivs 4 where
  h := anisotropicMetricSecond H
  h_metric := by
    intro e f a b
    by_cases h : a = b
    · subst b; rfl
    · simp [anisotropicMetricSecond, eta, h, Ne.symm h]
  h_comm := by
    intro e f a b
    by_cases h : e = f
    · subst f; rfl
    · simp [anisotropicMetricSecond, h, Ne.symm h]
  k := fun _ _ _ _ _ => 0
  k_metric := by intros; rfl
  k_sym12 := by intros; rfl
  k_sym23 := by intros; rfl

/-- 4D conformal Ricci tensor `R_{μν}(H)` at the origin for an anisotropic
diagonal jet `H`. -/
def ricciTensor4D (H : TransformedJet4D) (μ ν : Fin 4) : ℝ :=
  ricci (anisotropicMetricDerivs H) sign μ ν

/-- 4D conformal scalar curvature `R(H)` at the origin for an anisotropic
diagonal jet `H`. -/
def scalarCurvature4D (H : TransformedJet4D) : ℝ :=
  scalar (anisotropicMetricDerivs H) sign

/-- 4D conformal Einstein tensor `G_{μν}(H)` at the origin for an anisotropic
diagonal jet `H`. -/
def einsteinTensor4D (H : TransformedJet4D) (μ ν : Fin 4) : ℝ :=
  einstein (anisotropicMetricDerivs H) sign μ ν

/-- Lorentzian trace `Tr_η(G(H)) = ∑ μ, sign μ * G_{μμ}(H)` of the 4D conformal
Einstein tensor. -/
def einsteinTrace4D (H : TransformedJet4D) : ℝ :=
  einsteinTrace (anisotropicMetricDerivs H) sign

/-- Curvature coupling contribution `-(1/2) R(H)` appearing in the continuum limit
of the 4D chronological causal-diamond operator on a unit-normalized probe. -/
def chronologicalCurvatureLimit4D (H : TransformedJet4D) : ℝ :=
  -(1 / 2) * scalarCurvature4D H

/-- Finite difference quotient in the curvature parameter `c` for the full 4D
chronological operator acting on an arbitrary probe `ϕ`. -/
def probeTemporalDifferenceQuotient (rho c δ : ℝ) (ϕ : Point → ℝ) : ℝ :=
  (actual4DOperator rho (c + δ) ϕ - actual4DOperator rho c ϕ) / δ

/-- Anisotropic wave + quadrupole profile with temporal second derivative `w`
and spatial quadrupole parameters `q₁, q₂`. -/
def anisotropicWaveQuadrupole (w q₁ q₂ : ℝ) : TransformedJet4D :=
  mkJet4D w (w / 3 + q₁) (w / 3 + q₂) (w / 3 - q₁ - q₂)

theorem anisotropicMetricDerivs_isotropic (att spatial : ℝ) :
    anisotropicMetricDerivs (isotropicJet4D att spatial) =
      derivativeData att spatial := rfl

theorem transformedJet4D_field (μ : Fin 4) :
    transformedJet4D field μ = 4 :=
  KFCausalBDG4DCompactPhysicalTest.axis_second μ

theorem jet_basis_expansion (H : TransformedJet4D) (ν : Fin 4) :
    H ν = ∑ μ : Fin 4, H μ * jetBasis4D μ ν := by
  simp only [jetBasis4D, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem jet_four_axis_decomposition (H : TransformedJet4D) (ν : Fin 4) :
    H ν = H 0 * jetBasis4D 0 ν + H 1 * jetBasis4D 1 ν +
      H 2 * jetBasis4D 2 ν + H 3 * jetBasis4D 3 ν := by
  rw [jet_basis_expansion H ν, Fin.sum_univ_four]

theorem fullCoordinateWaveOperator4D_explicit (H : TransformedJet4D) :
    fullCoordinateWaveOperator4D H = -H 0 + H 1 + H 2 + H 3 ∧
    fullCoordinateWaveOperator4D H = -H 0 + spatialLaplacian4D H := by
  have h1 : fullCoordinateWaveOperator4D H = -H 0 + H 1 + H 2 + H 3 := by
    unfold fullCoordinateWaveOperator4D
    rw [Fin.sum_univ_four]
    simp +decide only [sign, ite_true, ite_false]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, spatialLaplacian4D]
  ring

theorem fullCoordinateWaveOperator4D_field :
    fullCoordinateWaveOperator4D (transformedJet4D field) = 8 := by
  rw [(fullCoordinateWaveOperator4D_explicit (transformedJet4D field)).1]
  simp only [transformedJet4D_field]
  ring

theorem ricciTensor4D_time (H : TransformedJet4D) :
    ricciTensor4D H 0 0 = -3 * H 0 + H 1 + H 2 + H 3 := by
  simp +decide only [ricciTensor4D, ricci, R_metric, anisotropicMetricDerivs,
    anisotropicMetricSecond, eta, sign, Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem ricciTensor4D_x (H : TransformedJet4D) :
    ricciTensor4D H 1 1 = H 0 - 3 * H 1 - H 2 - H 3 := by
  simp +decide only [ricciTensor4D, ricci, R_metric, anisotropicMetricDerivs,
    anisotropicMetricSecond, eta, sign, Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem ricciTensor4D_y (H : TransformedJet4D) :
    ricciTensor4D H 2 2 = H 0 - H 1 - 3 * H 2 - H 3 := by
  simp +decide only [ricciTensor4D, ricci, R_metric, anisotropicMetricDerivs,
    anisotropicMetricSecond, eta, sign, Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem ricciTensor4D_z (H : TransformedJet4D) :
    ricciTensor4D H 3 3 = H 0 - H 1 - H 2 - 3 * H 3 := by
  simp +decide only [ricciTensor4D, ricci, R_metric, anisotropicMetricDerivs,
    anisotropicMetricSecond, eta, sign, Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem ricciTensor4D_diag (H : TransformedJet4D) (μ : Fin 4) :
    ricciTensor4D H μ μ = -2 * H μ - sign μ * fullCoordinateWaveOperator4D H := by
  fin_cases μ
  · change ricciTensor4D H 0 0 = -2 * H 0 - sign 0 * fullCoordinateWaveOperator4D H
    rw [ricciTensor4D_time, (fullCoordinateWaveOperator4D_explicit H).1]
    simp +decide only [sign, ite_true]
    ring
  · change ricciTensor4D H 1 1 = -2 * H 1 - sign 1 * fullCoordinateWaveOperator4D H
    rw [ricciTensor4D_x, (fullCoordinateWaveOperator4D_explicit H).1]
    simp +decide only [sign, ite_false]
    ring
  · change ricciTensor4D H 2 2 = -2 * H 2 - sign 2 * fullCoordinateWaveOperator4D H
    rw [ricciTensor4D_y, (fullCoordinateWaveOperator4D_explicit H).1]
    simp +decide only [sign, ite_false]
    ring
  · change ricciTensor4D H 3 3 = -2 * H 3 - sign 3 * fullCoordinateWaveOperator4D H
    rw [ricciTensor4D_z, (fullCoordinateWaveOperator4D_explicit H).1]
    simp +decide only [sign, ite_false]
    ring

theorem ricciTensor4D_offDiag (H : TransformedJet4D) (μ ν : Fin 4) (h : μ ≠ ν) :
    ricciTensor4D H μ ν = 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp +decide only [ricciTensor4D, ricci, R_metric, anisotropicMetricDerivs,
      anisotropicMetricSecond, eta, sign, Fin.sum_univ_four, ite_true, ite_false] at h ⊢ <;> ring

theorem ricciTensor4D_formula (H : TransformedJet4D) (μ ν : Fin 4) :
    ricciTensor4D H μ ν =
      (if μ = ν then -2 * H μ else 0) - fullCoordinateWaveOperator4D H * eta μ ν := by
  by_cases h : μ = ν
  · subst ν
    rw [ricciTensor4D_diag]
    simp only [eta, if_true]
    ring
  · rw [ricciTensor4D_offDiag H μ ν h]
    simp [eta, h]

theorem scalarCurvature4D_eq (H : TransformedJet4D) :
    scalarCurvature4D H = 6 * (H 0 - H 1 - H 2 - H 3) ∧
    scalarCurvature4D H = -6 * fullCoordinateWaveOperator4D H := by
  have h1 : scalarCurvature4D H = 6 * (H 0 - H 1 - H 2 - H 3) := by
    unfold scalarCurvature4D scalar
    rw [Fin.sum_univ_four]
    change sign 0 * ricciTensor4D H 0 0 + sign 1 * ricciTensor4D H 1 1 +
      sign 2 * ricciTensor4D H 2 2 + sign 3 * ricciTensor4D H 3 3 = _
    rw [ricciTensor4D_time, ricciTensor4D_x, ricciTensor4D_y, ricciTensor4D_z]
    simp +decide only [sign, ite_true, ite_false]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, (fullCoordinateWaveOperator4D_explicit H).1]
  ring

theorem chronologicalCurvatureLimit4D_eq (H : TransformedJet4D) :
    chronologicalCurvatureLimit4D H = 3 * fullCoordinateWaveOperator4D H ∧
    chronologicalCurvatureLimit4D H = 3 * (-H 0 + H 1 + H 2 + H 3) := by
  unfold chronologicalCurvatureLimit4D
  rw [(scalarCurvature4D_eq H).2, (fullCoordinateWaveOperator4D_explicit H).1]
  constructor <;> ring

theorem einsteinTensor4D_diag (H : TransformedJet4D) (μ : Fin 4) :
    einsteinTensor4D H μ μ = -2 * H μ + 2 * sign μ * fullCoordinateWaveOperator4D H := by
  unfold einsteinTensor4D einstein
  change ricciTensor4D H μ μ - scalarCurvature4D H / 2 * (if μ = μ then sign μ else 0) = _
  rw [if_pos rfl, ricciTensor4D_diag, (scalarCurvature4D_eq H).2]
  ring

theorem einsteinTensor4D_offDiag (H : TransformedJet4D) (μ ν : Fin 4) (h : μ ≠ ν) :
    einsteinTensor4D H μ ν = 0 := by
  unfold einsteinTensor4D einstein
  change ricciTensor4D H μ ν - scalarCurvature4D H / 2 * (if μ = ν then sign μ else 0) = 0
  rw [if_neg h, ricciTensor4D_offDiag H μ ν h]
  ring

theorem einsteinTensor4D_formula (H : TransformedJet4D) (μ ν : Fin 4) :
    einsteinTensor4D H μ ν =
      (if μ = ν then -2 * H μ else 0) + 2 * fullCoordinateWaveOperator4D H * eta μ ν := by
  by_cases h : μ = ν
  · subst ν
    rw [einsteinTensor4D_diag]
    simp only [eta, if_true]
    ring
  · rw [einsteinTensor4D_offDiag H μ ν h]
    simp [eta, h]

theorem einsteinTensor4D_time (H : TransformedJet4D) :
    einsteinTensor4D H 0 0 = -2 * (H 1 + H 2 + H 3) ∧
    einsteinTensor4D H 0 0 = -2 * spatialLaplacian4D H := by
  have h1 : einsteinTensor4D H 0 0 = -2 * (H 1 + H 2 + H 3) := by
    rw [einsteinTensor4D_diag H 0, (fullCoordinateWaveOperator4D_explicit H).1]
    simp +decide only [sign, ite_true]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, spatialLaplacian4D]

theorem einsteinTensor4D_x (H : TransformedJet4D) :
    einsteinTensor4D H 1 1 = -2 * H 0 + 2 * (H 2 + H 3) := by
  rw [einsteinTensor4D_diag H 1, (fullCoordinateWaveOperator4D_explicit H).1]
  simp +decide only [sign, ite_false]
  ring

theorem einsteinTensor4D_y (H : TransformedJet4D) :
    einsteinTensor4D H 2 2 = -2 * H 0 + 2 * (H 1 + H 3) := by
  rw [einsteinTensor4D_diag H 2, (fullCoordinateWaveOperator4D_explicit H).1]
  simp +decide only [sign, ite_false]
  ring

theorem einsteinTensor4D_z (H : TransformedJet4D) :
    einsteinTensor4D H 3 3 = -2 * H 0 + 2 * (H 1 + H 2) := by
  rw [einsteinTensor4D_diag H 3, (fullCoordinateWaveOperator4D_explicit H).1]
  simp +decide only [sign, ite_false]
  ring

theorem einsteinTrace4D_eq (H : TransformedJet4D) :
    einsteinTrace4D H = -scalarCurvature4D H ∧
    einsteinTrace4D H = 6 * fullCoordinateWaveOperator4D H ∧
    einsteinTrace4D H = -6 * H 0 + 6 * (H 1 + H 2 + H 3) := by
  have htr := (lorentzian_einsteinTrace_eq_neg_scalar (anisotropicMetricDerivs H)).2
  change einsteinTrace4D H = -scalarCurvature4D H at htr
  have h2 : einsteinTrace4D H = 6 * fullCoordinateWaveOperator4D H := by
    rw [htr, (scalarCurvature4D_eq H).2]
    ring
  have h3 : einsteinTrace4D H = -6 * H 0 + 6 * (H 1 + H 2 + H 3) := by
    rw [h2, (fullCoordinateWaveOperator4D_explicit H).1]
    ring
  exact ⟨htr, h2, h3⟩

/-- Arbitrary finite linear combinations commute with `fullCoordinateWaveOperator4D`. -/
theorem fullCoordinateWaveOperator4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) :
    fullCoordinateWaveOperator4D (fun μ => ∑ i ∈ s, c i * Φ i μ) =
      ∑ i ∈ s, c i * fullCoordinateWaveOperator4D (Φ i) := by
  unfold fullCoordinateWaveOperator4D
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Arbitrary finite linear combinations commute with `scalarCurvature4D`. -/
theorem scalarCurvature4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) :
    scalarCurvature4D (fun μ => ∑ i ∈ s, c i * Φ i μ) =
      ∑ i ∈ s, c i * scalarCurvature4D (Φ i) := by
  rw [(scalarCurvature4D_eq _).2, fullCoordinateWaveOperator4D_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(scalarCurvature4D_eq (Φ i)).2]
  ring

/-- Arbitrary finite linear combinations commute with `chronologicalCurvatureLimit4D`. -/
theorem chronologicalCurvatureLimit4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) :
    chronologicalCurvatureLimit4D (fun μ => ∑ i ∈ s, c i * Φ i μ) =
      ∑ i ∈ s, c i * chronologicalCurvatureLimit4D (Φ i) := by
  unfold chronologicalCurvatureLimit4D
  rw [scalarCurvature4D_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Arbitrary finite linear combinations commute with `ricciTensor4D`. -/
theorem ricciTensor4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) (μ ν : Fin 4) :
    ricciTensor4D (fun a => ∑ i ∈ s, c i * Φ i a) μ ν =
      ∑ i ∈ s, c i * ricciTensor4D (Φ i) μ ν := by
  by_cases h : μ = ν
  · subst ν
    rw [ricciTensor4D_diag, fullCoordinateWaveOperator4D_finset_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ricciTensor4D_diag]
    ring
  · rw [ricciTensor4D_offDiag _ μ ν h]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ricciTensor4D_offDiag (Φ i) μ ν h, mul_zero]

/-- Arbitrary finite linear combinations commute with `einsteinTensor4D`. -/
theorem einsteinTensor4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) (μ ν : Fin 4) :
    einsteinTensor4D (fun a => ∑ i ∈ s, c i * Φ i a) μ ν =
      ∑ i ∈ s, c i * einsteinTensor4D (Φ i) μ ν := by
  by_cases h : μ = ν
  · subst ν
    rw [einsteinTensor4D_diag, fullCoordinateWaveOperator4D_finset_sum]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [einsteinTensor4D_diag]
    ring
  · rw [einsteinTensor4D_offDiag _ μ ν h]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [einsteinTensor4D_offDiag (Φ i) μ ν h, mul_zero]

/-- Arbitrary finite linear combinations commute with `einsteinTrace4D`. -/
theorem einsteinTrace4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → TransformedJet4D) :
    einsteinTrace4D (fun μ => ∑ i ∈ s, c i * Φ i μ) =
      ∑ i ∈ s, c i * einsteinTrace4D (Φ i) := by
  rw [(einsteinTrace4D_eq _).2.1, fullCoordinateWaveOperator4D_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(einsteinTrace4D_eq (Φ i)).2.1]
  ring

/-- Coordinate-axis basis decomposition of `fullCoordinateWaveOperator4D`,
`scalarCurvature4D`, `ricciTensor4D`, and `einsteinTensor4D` across the 4
spacetime axes `μ : Fin 4`. -/
theorem curvature_operators_four_axis_basis_decomposition
    (H : TransformedJet4D) (α β : Fin 4) :
    fullCoordinateWaveOperator4D H =
      ∑ μ : Fin 4, H μ * fullCoordinateWaveOperator4D (jetBasis4D μ) ∧
    scalarCurvature4D H =
      ∑ μ : Fin 4, H μ * scalarCurvature4D (jetBasis4D μ) ∧
    ricciTensor4D H α β =
      ∑ μ : Fin 4, H μ * ricciTensor4D (jetBasis4D μ) α β ∧
    einsteinTensor4D H α β =
      ∑ μ : Fin 4, H μ * einsteinTensor4D (jetBasis4D μ) α β := by
  have hH : H = fun ν => ∑ μ ∈ Finset.univ, H μ * jetBasis4D μ ν :=
    funext (jet_basis_expansion H)
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hH]
    exact fullCoordinateWaveOperator4D_finset_sum Finset.univ H jetBasis4D
  · conv_lhs => rw [hH]
    exact scalarCurvature4D_finset_sum Finset.univ H jetBasis4D
  · conv_lhs => rw [hH]
    exact ricciTensor4D_finset_sum Finset.univ H jetBasis4D α β
  · conv_lhs => rw [hH]
    exact einsteinTensor4D_finset_sum Finset.univ H jetBasis4D α β

/-- Small-scale operator `scaleOperator` commutes with arbitrary finite sums. -/
theorem scaleOperator_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (ε c : ℝ)
    (hΦ : ∀ i ∈ s, IntegrableOn (probeIntegrand ε⁻¹ c (Φ i)) (pastPatch c)) :
    scaleOperator ε c (fun q => ∑ i ∈ s, w i * Φ i q) =
      ∑ i ∈ s, w i * scaleOperator ε c (Φ i) :=
  actual4DOperator_finset_sum s w Φ ε⁻¹ c hΦ

/-- Continuum limit `rho → ∞` of `actual4DOperator` commutes with arbitrary
finite linear combinations `∑ i ∈ s, w i * Φ i`. -/
theorem actual4DOperator_finset_sum_tendsto {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (c : ℝ)
    (hΦ : ∀ i ∈ s, ∀ rho, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c))
    (ht : ∀ i ∈ s, Tendsto (fun rho => actual4DOperator rho c (Φ i)) atTop
      (𝓝 (continuumWaveCurvature c (Φ i)))) :
    Tendsto (fun rho => actual4DOperator rho c (fun q => ∑ i ∈ s, w i * Φ i q)) atTop
      (𝓝 (∑ i ∈ s, w i * continuumWaveCurvature c (Φ i))) := by
  have heq : (fun rho => actual4DOperator rho c (fun q => ∑ i ∈ s, w i * Φ i q)) =
      fun rho => ∑ i ∈ s, w i * actual4DOperator rho c (Φ i) :=
    funext (fun rho => actual4DOperator_finset_sum s w Φ rho c (fun i hi => hΦ i hi rho))
  rw [heq]
  exact tendsto_finset_sum s (fun i hi => (ht i hi).const_mul (w i))

/-- Small-scale continuum limit `ε → 0⁺` of `scaleOperator` commutes with
arbitrary finite linear combinations `∑ i ∈ s, w i * Φ i`. -/
theorem scaleOperator_finset_sum_tendsto {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Φ : ι → Point → ℝ) (c : ℝ)
    (hΦ : ∀ i ∈ s, ∀ rho, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c))
    (ht : ∀ i ∈ s, Tendsto (fun rho => actual4DOperator rho c (Φ i)) atTop
      (𝓝 (continuumWaveCurvature c (Φ i)))) :
    Tendsto (fun ε => scaleOperator ε c (fun q => ∑ i ∈ s, w i * Φ i q)) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i ∈ s, w i * continuumWaveCurvature c (Φ i))) :=
  (actual4DOperator_finset_sum_tendsto s w Φ c hΦ ht).comp tendsto_inv_nhdsGT_zero

/-- The curvature-parameter difference quotient `probeTemporalDifferenceQuotient`
commutes with arbitrary finite linear combinations `∑ i ∈ s, w i * Φ i`. -/
theorem probeTemporalDifferenceQuotient_finset_sum {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (Φ : ι → Point → ℝ) (rho c δ : ℝ)
    (hΦ₁ : ∀ i ∈ s, IntegrableOn (probeIntegrand rho (c + δ) (Φ i)) (pastPatch (c + δ)))
    (hΦ₂ : ∀ i ∈ s, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c)) :
    probeTemporalDifferenceQuotient rho c δ (fun q => ∑ i ∈ s, w i * Φ i q) =
      ∑ i ∈ s, w i * probeTemporalDifferenceQuotient rho c δ (Φ i) := by
  unfold probeTemporalDifferenceQuotient
  rw [actual4DOperator_finset_sum s w Φ rho (c + δ) hΦ₁,
    actual4DOperator_finset_sum s w Φ rho c hΦ₂,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Continuum limit `rho → ∞` of `probeTemporalDifferenceQuotient` commutes with
arbitrary finite linear combinations `∑ i ∈ s, w i * Φ i`. -/
theorem probeTemporalDifferenceQuotient_finset_sum_tendsto {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (Φ : ι → Point → ℝ) (c δ : ℝ)
    (hΦ₁ : ∀ i ∈ s, ∀ rho, IntegrableOn (probeIntegrand rho (c + δ) (Φ i)) (pastPatch (c + δ)))
    (hΦ₂ : ∀ i ∈ s, ∀ rho, IntegrableOn (probeIntegrand rho c (Φ i)) (pastPatch c))
    (ht₁ : ∀ i ∈ s, Tendsto (fun rho => actual4DOperator rho (c + δ) (Φ i)) atTop
      (𝓝 (continuumWaveCurvature (c + δ) (Φ i))))
    (ht₂ : ∀ i ∈ s, Tendsto (fun rho => actual4DOperator rho c (Φ i)) atTop
      (𝓝 (continuumWaveCurvature c (Φ i)))) :
    Tendsto (fun rho => probeTemporalDifferenceQuotient rho c δ
        (fun q => ∑ i ∈ s, w i * Φ i q)) atTop
      (𝓝 (∑ i ∈ s, w i *
        ((continuumWaveCurvature (c + δ) (Φ i) - continuumWaveCurvature c (Φ i)) / δ))) := by
  have heq : (fun rho => probeTemporalDifferenceQuotient rho c δ
      (fun q => ∑ i ∈ s, w i * Φ i q)) =
      fun rho => ∑ i ∈ s, w i * probeTemporalDifferenceQuotient rho c δ (Φ i) :=
    funext (fun rho => probeTemporalDifferenceQuotient_finset_sum s w Φ rho c δ
      (fun i hi => hΦ₁ i hi rho) (fun i hi => hΦ₂ i hi rho))
  rw [heq]
  exact tendsto_finset_sum s (fun i hi =>
    (((ht₁ i hi).sub (ht₂ i hi)).div_const δ).const_mul (w i))

/-- An anisotropic spatial wave profile satisfying `H 1 + H 2 + H 3 = H 0` has
vanishing 4D wave operator, vanishing scalar curvature, vanishing chronological
curvature limit, and vanishing Einstein trace, while its spatial diagonal Ricci
and Einstein components equal `-2 * H i`. -/
theorem anisotropic_wave_vanishing_scalar_and_trace (H : TransformedJet4D)
    (hwave : H 1 + H 2 + H 3 = H 0) :
    fullCoordinateWaveOperator4D H = 0 ∧
    scalarCurvature4D H = 0 ∧
    chronologicalCurvatureLimit4D H = 0 ∧
    einsteinTrace4D H = 0 ∧
    ricciTensor4D H 0 0 = -2 * H 0 ∧
    einsteinTensor4D H 0 0 = -2 * H 0 ∧
    ∀ i : Fin 4, ricciTensor4D H i i = -2 * H i ∧ einsteinTensor4D H i i = -2 * H i := by
  have hbox : fullCoordinateWaveOperator4D H = 0 := by
    rw [(fullCoordinateWaveOperator4D_explicit H).1]
    linarith
  have hR : scalarCurvature4D H = 0 := by
    rw [(scalarCurvature4D_eq H).2, hbox, mul_zero]
  have hlim : chronologicalCurvatureLimit4D H = 0 := by
    rw [(chronologicalCurvatureLimit4D_eq H).1, hbox, mul_zero]
  have htr : einsteinTrace4D H = 0 := by
    rw [(einsteinTrace4D_eq H).1, hR, neg_zero]
  have hdiag : ∀ i : Fin 4,
      ricciTensor4D H i i = -2 * H i ∧ einsteinTensor4D H i i = -2 * H i := by
    intro i
    rw [ricciTensor4D_diag H i, einsteinTensor4D_diag H i, hbox]
    constructor <;> ring
  exact ⟨hbox, hR, hlim, htr, (hdiag 0).1, (hdiag 0).2, hdiag⟩

/-- For any anisotropic profile `H` satisfying the wave condition
`H 1 + H 2 + H 3 = H 0`, the spatial anisotropy defects sum to zero and are
selectively extracted by the spatial Ricci and Einstein components relative to
either the spatial mean or `(1/3) G_{00}(H)`. -/
theorem anisotropic_spatial_defect_detection (H : TransformedJet4D)
    (hwave : H 1 + H 2 + H 3 = H 0) (i : Fin 4) :
    spatialAnisotropyDefect H 1 + spatialAnisotropyDefect H 2 +
      spatialAnisotropyDefect H 3 = 0 ∧
    ricciTensor4D H i i -
        (1 / 3) * (ricciTensor4D H 1 1 + ricciTensor4D H 2 2 + ricciTensor4D H 3 3) =
      -2 * spatialAnisotropyDefect H i ∧
    einsteinTensor4D H i i -
        (1 / 3) * (einsteinTensor4D H 1 1 + einsteinTensor4D H 2 2 + einsteinTensor4D H 3 3) =
      -2 * spatialAnisotropyDefect H i ∧
    einsteinTensor4D H i i - (1 / 3) * einsteinTensor4D H 0 0 =
      -2 * spatialAnisotropyDefect H i ∧
    ricciTensor4D H i i - (1 / 3) * einsteinTensor4D H 0 0 =
      -2 * spatialAnisotropyDefect H i := by
  have hw := anisotropic_wave_vanishing_scalar_and_trace H hwave
  have hR1 := (hw.2.2.2.2.2.2 1).1
  have hR2 := (hw.2.2.2.2.2.2 2).1
  have hR3 := (hw.2.2.2.2.2.2 3).1
  have hRi := (hw.2.2.2.2.2.2 i).1
  have hG1 := (hw.2.2.2.2.2.2 1).2
  have hG2 := (hw.2.2.2.2.2.2 2).2
  have hG3 := (hw.2.2.2.2.2.2 3).2
  have hGi := (hw.2.2.2.2.2.2 i).2
  have hG0 := hw.2.2.2.2.2.1
  unfold spatialAnisotropyDefect
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · rw [hRi, hR1, hR2, hR3]; linarith
  · rw [hGi, hG1, hG2, hG3]; linarith
  · rw [hGi, hG0]; ring
  · rw [hRi, hG0]; ring

/-- Explicit plane-wave + quadrupole witness: `anisotropicWaveQuadrupole w q₁ q₂`
has vanishing scalar curvature, vanishing chronological curvature limit, and
traceless Einstein tensor, while its spatial Ricci and Einstein components
detect the quadrupole anisotropies `-2 q₁`, `-2 q₂`, and `2 (q₁ + q₂)`. -/
theorem anisotropicWaveQuadrupole_properties (w q₁ q₂ : ℝ) :
    let H := anisotropicWaveQuadrupole w q₁ q₂
    H 1 + H 2 + H 3 = H 0 ∧
    fullCoordinateWaveOperator4D H = 0 ∧
    scalarCurvature4D H = 0 ∧
    chronologicalCurvatureLimit4D H = 0 ∧
    einsteinTrace4D H = 0 ∧
    einsteinTensor4D H 1 1 - (1 / 3) * einsteinTensor4D H 0 0 = -2 * q₁ ∧
    einsteinTensor4D H 2 2 - (1 / 3) * einsteinTensor4D H 0 0 = -2 * q₂ ∧
    einsteinTensor4D H 3 3 - (1 / 3) * einsteinTensor4D H 0 0 = 2 * (q₁ + q₂) := by
  intro H
  have h0 : H 0 = w := rfl
  have h1 : H 1 = w / 3 + q₁ := rfl
  have h2 : H 2 = w / 3 + q₂ := rfl
  have h3 : H 3 = w / 3 - q₁ - q₂ := rfl
  have hwave : H 1 + H 2 + H 3 = H 0 := by
    rw [h0, h1, h2, h3]
    ring
  have hvan := anisotropic_wave_vanishing_scalar_and_trace H hwave
  have hd1 := (anisotropic_spatial_defect_detection H hwave 1).2.2.2.1
  have hd2 := (anisotropic_spatial_defect_detection H hwave 2).2.2.2.1
  have hd3 := (anisotropic_spatial_defect_detection H hwave 3).2.2.2.1
  unfold spatialAnisotropyDefect at hd1 hd2 hd3
  rw [h0, h1] at hd1
  rw [h0, h2] at hd2
  rw [h0, h3] at hd3
  refine ⟨hwave, hvan.1, hvan.2.1, hvan.2.2.1, hvan.2.2.2.1, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

#print axioms anisotropicMetricDerivs_isotropic
#print axioms transformedJet4D_field
#print axioms jet_basis_expansion
#print axioms jet_four_axis_decomposition
#print axioms fullCoordinateWaveOperator4D_explicit
#print axioms fullCoordinateWaveOperator4D_field
#print axioms ricciTensor4D_time
#print axioms ricciTensor4D_x
#print axioms ricciTensor4D_y
#print axioms ricciTensor4D_z
#print axioms ricciTensor4D_diag
#print axioms ricciTensor4D_offDiag
#print axioms ricciTensor4D_formula
#print axioms scalarCurvature4D_eq
#print axioms chronologicalCurvatureLimit4D_eq
#print axioms einsteinTensor4D_diag
#print axioms einsteinTensor4D_offDiag
#print axioms einsteinTensor4D_formula
#print axioms einsteinTensor4D_time
#print axioms einsteinTensor4D_x
#print axioms einsteinTensor4D_y
#print axioms einsteinTensor4D_z
#print axioms einsteinTrace4D_eq
#print axioms fullCoordinateWaveOperator4D_finset_sum
#print axioms scalarCurvature4D_finset_sum
#print axioms chronologicalCurvatureLimit4D_finset_sum
#print axioms ricciTensor4D_finset_sum
#print axioms einsteinTensor4D_finset_sum
#print axioms einsteinTrace4D_finset_sum
#print axioms curvature_operators_four_axis_basis_decomposition
#print axioms scaleOperator_finset_sum
#print axioms actual4DOperator_finset_sum_tendsto
#print axioms scaleOperator_finset_sum_tendsto
#print axioms probeTemporalDifferenceQuotient_finset_sum
#print axioms probeTemporalDifferenceQuotient_finset_sum_tendsto
#print axioms anisotropic_wave_vanishing_scalar_and_trace
#print axioms anisotropic_spatial_defect_detection
#print axioms anisotropicWaveQuadrupole_properties

end
end UnifiedTheory.Audit.KFCausalConformal4DAnisotropicSpatialProbeSynthesis
