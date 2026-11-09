import UnifiedTheory.Audit.KFCausalConformal4DCoupledWaveVariationSynthesis
import UnifiedTheory.Audit.KFCausalConformal4DOffDiagonalShearCurvatureSynthesis

/-! Master synthesis of the 4D curved conformal causal-diamond continuum limit:
full 10-component symmetric Hessian reconstruction from the Einstein tensor and
polarization/chronological probes, coupled matter-curvature Euler-Lagrange
stationarity equivalences, contracted Bianchi and on-shell stress-energy
conservation, and finite-sum linearity across all curvature and probe operators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DCurvedDiamondMasterSynthesis
noncomputable section

open Set MeasureTheory Filter Topology
open scoped Real BigOperators
open KFCausalConformal4DDiamondBenchmark (Point sign eta)
open KFCausalConformal4DCovariantWaveTest (covariantWave scalarCurvature)
open KFCausalBDG4DCompactPhysicalTest (field)
open KFCausalConformal4DFullCoordinateOperator (pastPatch actual_integrable)
open KFCausalConformal4DLinearSuperpositionLimit (probeIntegrand actual4DOperator
  scaleOperator continuumWaveCurvature linearCombo
  two_probe_wave_separation_tendsto two_probe_curvature_extraction_tendsto)
open KFCausalConformal4DCoupledWaveVariationSynthesis (continuumWaveCurvatureValue
  continuumTemporalVariationValue temporalVariationDerivative
  temporalVariationDifferenceQuotient discreteJetFromDerivative
  coupledWaveCurvatureAffineJet scalarCurvatureAffineJet
  joint_operator_and_derivative_tendsto
  joint_operator_and_difference_quotient_tendsto
  discreteJetFromDerivative_tendsto)
open KFCausalConformal4DLorentzianBianchiTraceSynthesis (temporalEinsteinTrace
  temporalEinsteinTrace_eq bdg_temporal_variation_tendsto_half_einsteinTrace_deriv)
open KFCausalConformal4DAnisotropicSpatialProbeSynthesis (TransformedJet4D
  fullCoordinateWaveOperator4D ricciTensor4D scalarCurvature4D einsteinTensor4D
  einsteinTrace4D chronologicalCurvatureLimit4D probeTemporalDifferenceQuotient
  actual4DOperator_finset_sum_tendsto scaleOperator_finset_sum_tendsto
  anisotropic_wave_vanishing_scalar_and_trace anisotropic_spatial_defect_detection)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsPureOffDiagonalShear4D IsSymmetricThirdJet4D
  minkMetric4D box4D dBox4D fullRicciTensor4D fullScalarCurvature4D
  fullEinsteinTensor4D fullEinsteinTrace4D fullChronologicalCurvatureLimit4D
  fullDRicci4D fullDScalar4D fullDEinstein4D
  bianchiDiagonalChannel4D bianchiOffDiagonalChannel4D
  plusPolarization4D minusPolarization4D bilinearEval4D
  minkMetric4D_diag minkMetric4D_offDiag
  fullRicciTensor4D_master_formula fullScalarCurvature4D_master_formula
  fullEinsteinTensor4D_master_formula fullEinsteinTrace4D_master_formula
  offDiagonal_einstein_eq_ricci_eq_neg_two_hessian
  offDiagonal_polarization_probe_extraction
  pure_offDiagonal_shear_curvature_synthesis
  bianchi_diagonal_offDiagonal_channel_decomposition)

/-- Reconstruction of all 10 independent components (4 diagonal + 6 off-diagonal
pairs) of a symmetric 4×4 Hessian `H_{μν}` directly from the 4D conformal
Einstein tensor `G_{μν}`:
`H_{μν} = -(1/2) G_{μν} + (1/6) Tr_η(G) η_{μν}`. -/
def reconstructHessianFromEinstein4D (G : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  -(1 / 2) * G μ ν + (1 / 6) * (∑ a : Fin 4, sign a * G a a) * minkMetric4D μ ν

/-- Reconstruction of a symmetric 4×4 Hessian `H_{μν}` from the 4D conformal
Ricci tensor `R_{μν}` and the causal-diamond scalar curvature `R`:
`H_{μν} = -(1/2) R_{μν} + (1/12) R η_{μν}`. -/
def reconstructHessianFromRicciAndScalar4D
    (Ric : Fin 4 → Fin 4 → ℝ) (R : ℝ) (μ ν : Fin 4) : ℝ :=
  -(1 / 2) * Ric μ ν + (1 / 12) * R * minkMetric4D μ ν

/-- Reconstruction of all 10 components of a symmetric 4×4 Hessian `H_{μν}` from
the 4 diagonal Einstein components `G_{μμ}` (for `μ = ν`) and the 6 off-diagonal
polarization probe differences `G((e_μ+e_ν)/2, (e_μ+e_ν)/2) - G((e_μ-e_ν)/2, (e_μ-e_ν)/2)`
(for `μ ≠ ν`). -/
def reconstructHessianFromProbes4D (G : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ = ν then
    -(1 / 2) * G μ μ + (1 / 6) * (∑ a : Fin 4, sign a * G a a) * sign μ
  else
    -(1 / 2) * (bilinearEval4D G (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D G (minusPolarization4D μ ν) (minusPolarization4D μ ν))

/-- Lorentzian divergence `∑ e, sign e * dT e ν e` of a differentiated rank-2
stress-energy tensor jet `dT`. -/
def lorentzianStressEnergyDivergence4D
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : ℝ :=
  ∑ e : Fin 4, sign e * dT e ν e

/-- Exact wave-curvature identity: `-(1/6) R(H) = box4D H = (1/6) Tr_η(G(H))`
and `-(1/3) fullChronologicalCurvatureLimit4D H = box4D H`. -/
theorem wave_from_scalar_and_einstein_trace (H : Hessian4D) :
    -(1 / 6) * fullScalarCurvature4D H = box4D H ∧
    (1 / 6) * fullEinsteinTrace4D H = box4D H ∧
    (1 / 3) * fullChronologicalCurvatureLimit4D H = box4D H := by
  have hS := (fullScalarCurvature4D_master_formula H).1
  have hE := (fullEinsteinTrace4D_master_formula H).2
  unfold fullChronologicalCurvatureLimit4D
  rw [hS, hE]
  refine ⟨by ring, by ring, by ring⟩

/-- Exact 10-component inverse theorem: for any symmetric 4×4 Hessian `H`,
`reconstructHessianFromEinstein4D (fullEinsteinTensor4D H) μ ν = H μ ν` for all
4 diagonal indices `μ = ν` and all 6 off-diagonal pairs `μ ≠ ν`. -/
theorem reconstructHessianFromEinstein4D_exact (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    reconstructHessianFromEinstein4D (fullEinsteinTensor4D H) μ ν = H μ ν := by
  unfold reconstructHessianFromEinstein4D
  have htr : (∑ a : Fin 4, sign a * fullEinsteinTensor4D H a a) = 6 * box4D H :=
    (fullEinsteinTrace4D_master_formula H).2
  rw [htr, fullEinsteinTensor4D_master_formula H hH μ ν]
  ring

/-- Exact 10-component reconstruction from the Ricci tensor and scalar curvature:
`reconstructHessianFromRicciAndScalar4D (fullRicciTensor4D H) (fullScalarCurvature4D H) μ ν = H μ ν`. -/
theorem reconstructHessianFromRicciAndScalar4D_exact (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    reconstructHessianFromRicciAndScalar4D
      (fullRicciTensor4D H) (fullScalarCurvature4D H) μ ν = H μ ν := by
  unfold reconstructHessianFromRicciAndScalar4D
  rw [fullRicciTensor4D_master_formula H hH μ ν,
    (fullScalarCurvature4D_master_formula H).1]
  ring

/-- Exact 10-component reconstruction from the 4 diagonal Einstein components
and the 6 off-diagonal polarization probe differences. -/
theorem reconstructHessianFromProbes4D_exact (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    reconstructHessianFromProbes4D (fullEinsteinTensor4D H) μ ν = H μ ν := by
  unfold reconstructHessianFromProbes4D
  by_cases h : μ = ν
  · subst ν
    rw [if_pos rfl]
    have h1 := reconstructHessianFromEinstein4D_exact H hH μ μ
    unfold reconstructHessianFromEinstein4D at h1
    rwa [minkMetric4D_diag] at h1
  · rw [if_neg h]
    have hp := (offDiagonal_polarization_probe_extraction H hH μ ν h).2.2.1
    rw [hp]
    ring

/-- The 4D conformal Einstein tensor map `H ↦ fullEinsteinTensor4D H` is
injective on the 10-dimensional space of symmetric 4×4 Hessians. -/
theorem fullEinsteinTensor4D_injective_on_symmetric (H₁ H₂ : Hessian4D)
    (h₁ : IsSymmetricHessian4D H₁) (h₂ : IsSymmetricHessian4D H₂)
    (heq : fullEinsteinTensor4D H₁ = fullEinsteinTensor4D H₂) :
    H₁ = H₂ := by
  funext μ ν
  rw [← reconstructHessianFromEinstein4D_exact H₁ h₁ μ ν,
    ← reconstructHessianFromEinstein4D_exact H₂ h₂ μ ν, heq]

/-- Coupled matter-curvature Euler-Lagrange stationarity equivalences:
`box4D H = κ * J_matter` is equivalent to each of:
1. `fullScalarCurvature4D H = -6 * (κ * J_matter)`,
2. `fullEinsteinTrace4D H = 6 * (κ * J_matter)`,
3. `-(1 / 6) * fullScalarCurvature4D H = κ * J_matter`,
4. `fullChronologicalCurvatureLimit4D H = 3 * (κ * J_matter)`. -/
theorem coupled_matter_curvature_stationarity_iff (H : Hessian4D)
    (κ J_matter : ℝ) :
    (box4D H = κ * J_matter ↔
      fullScalarCurvature4D H = -6 * (κ * J_matter)) ∧
    (box4D H = κ * J_matter ↔
      fullEinsteinTrace4D H = 6 * (κ * J_matter)) ∧
    (box4D H = κ * J_matter ↔
      -(1 / 6) * fullScalarCurvature4D H = κ * J_matter) ∧
    (box4D H = κ * J_matter ↔
      fullChronologicalCurvatureLimit4D H = 3 * (κ * J_matter)) := by
  have hS := (fullScalarCurvature4D_master_formula H).1
  have hE := (fullEinsteinTrace4D_master_formula H).2
  unfold fullChronologicalCurvatureLimit4D
  rw [hS, hE]
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- On-shell stress-energy conservation from the 4D Lorentzian contracted
Bianchi identity: if the differentiated Einstein tensor satisfies the coupled
field equation `∂_e G_{ab}(K) = κ * dT e a b` with `κ ≠ 0`, then the Lorentzian
divergence `∑ e, sign e * dT e ν e` vanishes identically for all `ν : Fin 4`. -/
theorem onShell_stressEnergy_conservation (H : Hessian4D) (K : ThirdJet4D)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (heq : ∀ e a b : Fin 4, fullDEinstein4D H K e a b = κ * dT e a b)
    (ν : Fin 4) :
    lorentzianStressEnergyDivergence4D dT ν = 0 := by
  have hdiv : (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) = 0 :=
    KFCausalLorentzianContractedBianchi.lorentzian_metric_divergence
      (KFCausalConformal4DOffDiagonalShearCurvatureSynthesis.fullConformalMetricDerivs H K) ν
  have hrel : (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) =
      κ * lorentzianStressEnergyDivergence4D dT ν := by
    unfold lorentzianStressEnergyDivergence4D
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [heq e ν e]
    ring
  rw [hrel] at hdiv
  exact (mul_eq_zero.mp hdiv).resolve_left hκ

/-- Finite-sum linearity for the full 4×4 conformal curvature operators
`box4D`, `fullScalarCurvature4D`, `fullRicciTensor4D`, `fullEinsteinTensor4D`,
and `fullEinsteinTrace4D`. -/
theorem fullCurvatureOperators4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Φ : ι → Hessian4D)
    (hΦ : ∀ i ∈ s, IsSymmetricHessian4D (Φ i)) (μ ν : Fin 4) :
    let Hsum : Hessian4D := fun a b => ∑ i ∈ s, c i * Φ i a b
    IsSymmetricHessian4D Hsum ∧
    box4D Hsum = ∑ i ∈ s, c i * box4D (Φ i) ∧
    fullScalarCurvature4D Hsum = ∑ i ∈ s, c i * fullScalarCurvature4D (Φ i) ∧
    fullRicciTensor4D Hsum μ ν = ∑ i ∈ s, c i * fullRicciTensor4D (Φ i) μ ν ∧
    fullEinsteinTensor4D Hsum μ ν = ∑ i ∈ s, c i * fullEinsteinTensor4D (Φ i) μ ν ∧
    fullEinsteinTrace4D Hsum = ∑ i ∈ s, c i * fullEinsteinTrace4D (Φ i) := by
  intro Hsum
  have hsym : IsSymmetricHessian4D Hsum := by
    intro a b
    dsimp [Hsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hΦ i hi a b]
  have hbox : box4D Hsum = ∑ i ∈ s, c i * box4D (Φ i) := by
    unfold box4D
    dsimp [Hsum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hS : fullScalarCurvature4D Hsum =
      ∑ i ∈ s, c i * fullScalarCurvature4D (Φ i) := by
    rw [(fullScalarCurvature4D_master_formula Hsum).1, hbox, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(fullScalarCurvature4D_master_formula (Φ i)).1]
    ring
  have hR : fullRicciTensor4D Hsum μ ν =
      ∑ i ∈ s, c i * fullRicciTensor4D (Φ i) μ ν := by
    rw [fullRicciTensor4D_master_formula Hsum hsym μ ν, hbox]
    dsimp [Hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [fullRicciTensor4D_master_formula (Φ i) (hΦ i hi) μ ν]
    ring
  have hG : fullEinsteinTensor4D Hsum μ ν =
      ∑ i ∈ s, c i * fullEinsteinTensor4D (Φ i) μ ν := by
    rw [fullEinsteinTensor4D_master_formula Hsum hsym μ ν, hbox]
    dsimp [Hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [fullEinsteinTensor4D_master_formula (Φ i) (hΦ i hi) μ ν]
    ring
  have hTr : fullEinsteinTrace4D Hsum =
      ∑ i ∈ s, c i * fullEinsteinTrace4D (Φ i) := by
    rw [(fullEinsteinTrace4D_master_formula Hsum).2, hbox, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(fullEinsteinTrace4D_master_formula (Φ i)).2]
    ring
  exact ⟨hsym, hbox, hS, hR, hG, hTr⟩

/-- Finite-sum linearity of the 10-component Hessian reconstruction operator
`reconstructHessianFromEinstein4D`. -/
theorem reconstructHessianFromEinstein4D_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (G : ι → Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    reconstructHessianFromEinstein4D (fun a b => ∑ i ∈ s, c i * G i a b) μ ν =
      ∑ i ∈ s, c i * reconstructHessianFromEinstein4D (G i) μ ν := by
  unfold reconstructHessianFromEinstein4D
  have htr : (∑ a : Fin 4, sign a * ∑ i ∈ s, c i * G i a a) =
      ∑ i ∈ s, c i * (∑ a : Fin 4, sign a * G i a a) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [htr, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add]
  ring

/-- Master synthesis theorem of the 4D curved conformal causal-diamond continuum
limit: simultaneously packages
1. Full 10-component Hessian reconstruction from `G_{μν}(H)` and polarization probes,
2. Causal-diamond continuum convergence of the zeroth-order operator, two-probe
   wave/curvature separation, and first-order temporal curvature variation,
3. Coupled matter-curvature Euler-Lagrange stationarity equivalences,
4. Exact contracted Bianchi conservation (`div G_ν = 0`), its diagonal/off-diagonal
   third-derivative channel cancellation, and on-shell stress-energy conservation
   (`div T_ν = 0`). -/
theorem curved_4D_conformal_diamond_master_synthesis
    (c : ℝ) (hc : |c| ≤ 1 / 54)
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (κ J_matter : ℝ) (hκ : κ ≠ 0)
    (hEFE : ∀ e a b : Fin 4, fullDEinstein4D H K e a b = κ * dT e a b) :
    -- (1) Full 10-component symmetric Hessian reconstruction
    (∀ μ ν : Fin 4,
      reconstructHessianFromEinstein4D (fullEinsteinTensor4D H) μ ν = H μ ν ∧
      reconstructHessianFromRicciAndScalar4D
        (fullRicciTensor4D H) (fullScalarCurvature4D H) μ ν = H μ ν ∧
      reconstructHessianFromProbes4D (fullEinsteinTensor4D H) μ ν = H μ ν) ∧
    -- (2) Wave-scalar-trace identity -(1/6) R(H) = box4D(H) = (1/6) Tr_η(G(H))
    (-(1 / 6) * fullScalarCurvature4D H = box4D H ∧
      (1 / 6) * fullEinsteinTrace4D H = box4D H) ∧
    -- (3) Joint causal-diamond continuum limit of operator and temporal curvature derivative
    (Tendsto (fun rho => (KFCausalConformal4DCoupledWaveVariationSynthesis.actual4DOperator rho c,
        temporalVariationDerivative rho)) atTop
      (𝓝 (8 - 6 * c, -6)) ∧
      Tendsto (fun rho => deriv (KFCausalBDG4DActualTemporalVariation.operator rho) 0) atTop
        (𝓝 ((1 / 2) * deriv temporalEinsteinTrace 0))) ∧
    -- (4) Coupled matter-curvature Euler-Lagrange stationarity equivalences
    ((box4D H = κ * J_matter ↔ fullScalarCurvature4D H = -6 * (κ * J_matter)) ∧
      (box4D H = κ * J_matter ↔ fullEinsteinTrace4D H = 6 * (κ * J_matter))) ∧
    -- (5) Contracted Bianchi channel cancellation and on-shell stress-energy conservation
    (∀ ν : Fin 4,
      bianchiDiagonalChannel4D H K ν + bianchiOffDiagonalChannel4D H K ν = 0 ∧
      (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) = 0 ∧
      lorentzianStressEnergyDivergence4D dT ν = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ ν
    exact ⟨reconstructHessianFromEinstein4D_exact H hH μ ν,
      reconstructHessianFromRicciAndScalar4D_exact H hH μ ν,
      reconstructHessianFromProbes4D_exact H hH μ ν⟩
  · have hw := wave_from_scalar_and_einstein_trace H
    exact ⟨hw.1, hw.2.1⟩
  · exact ⟨(joint_operator_and_derivative_tendsto c hc).2,
      bdg_temporal_variation_tendsto_half_einsteinTrace_deriv⟩
  · have hm := coupled_matter_curvature_stationarity_iff H κ J_matter
    exact ⟨hm.1, hm.2.1⟩
  · intro ν
    have hb := bianchi_diagonal_offDiagonal_channel_decomposition H K hK ν
    exact ⟨hb.2.2.2.1, hb.2.2.2.2,
      onShell_stressEnergy_conservation H K dT κ hκ hEFE ν⟩

#print axioms wave_from_scalar_and_einstein_trace
#print axioms reconstructHessianFromEinstein4D_exact
#print axioms reconstructHessianFromRicciAndScalar4D_exact
#print axioms reconstructHessianFromProbes4D_exact
#print axioms fullEinsteinTensor4D_injective_on_symmetric
#print axioms coupled_matter_curvature_stationarity_iff
#print axioms onShell_stressEnergy_conservation
#print axioms fullCurvatureOperators4D_finset_sum
#print axioms reconstructHessianFromEinstein4D_finset_sum
#print axioms curved_4D_conformal_diamond_master_synthesis

end
end UnifiedTheory.Audit.KFCausalConformal4DCurvedDiamondMasterSynthesis
