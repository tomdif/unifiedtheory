/-
Copyright (c) 2026 UnifiedTheory Audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Curved 4D Plebanski BF Source/Dressing Split, Metric-Gauge Coupling, Causal Action Coefficient, Minimal Coupling & Riemann Action Bridge

This module forms the first curved-4D gravitational synthesis of **Checkpoint 12 (Front 5)**.
It bridges seven foundational `LayerA` and `LayerB` modules directly into the audited
curved 4D Weyl–Ricci–Lovelock–Yang–Mills–Schwarzschild–Hawking–Penrose–Christodoulou–Bekenstein
framework:

1. **Plebanski BF Source/Dressing Split & Operator-Derived Reduction (`LayerA.BFSourceDressing`, `LayerA.DerivedBFSplit`, `LayerA.SourceFromMetric`)**:
   - Idempotent projection decomposition `v = d.πK v + d.πP v`, mutual orthogonality
     `d.πK (d.πP v) = 0` and `d.πP (d.πK v) = 0`, and `d.sourceFunc v = d.sourceFunc (d.πK v)`.
   - Canonical derivation of `sourceProj sf` and `dressingProj sf` from a single non-zero
     functional `sf : SourceFunctional V`, with `sf.φ (sourceProj sf v) = sf.φ v` and
     `sf.φ (dressingProj sf v) = 0` (`functional_derives_decomposition`).
   - Primitive reduction `3 → 2` (`reduction_3_to_2`): any linear operator `L : V →ₗ[ℝ] W`
     (such as the linearized Einstein operator) composed with a target functional `ψ`
     induces `sourceFromOperator L ψ = ψ ∘ₗ L` whose kernel contains `ker L` (`gauge_is_dressing`).
2. **4D Metric-Gauge Coupling & Unique 4D Yang-Mills Tracelessness (`LayerA.MetricGaugeCoupling`)**:
   - Explicit Yang-Mills stress-energy trace identity
     `stressEnergyTrace sc conn = (1 - n / 4) * fieldStrengthNorm sc conn`.
   - Exact vanishing in four spacetime dimensions (`stressEnergyTrace sc₄ conn₄ = 0`,
     `gauge_traceless_4d`) and uniqueness of `n = 4` (`four_is_unique_traceless`).
   - Non-trivial gravitational sourcing of traceless 4D gauge fields (`traceless_but_sourceful`),
     bridged to 4D Weyl conformal invariance (`weylTensor4D (conformalPartMetricDerivs4D md) = 0`),
     Einstein-Sorkin-Yang-Mills stationarity, and Raychaudhuri null focusing (`NEC`).
3. **Benincasa-Dowker 4D Causal Action Coefficient `c = 1 / 2` & Reduced Planck Scale (`LayerA.CausalActionCoefficient`)**:
   - `causalCoefficient = 1 / 2`, fixing `discretenessLength causalCoefficient G_N = √(8π) * planckLength G_N`,
     `(discretenessLength causalCoefficient G_N)^2 = 8 * π * G_N`, and the reduced Planck mass
     ratio `planckLength G_N / discretenessLength causalCoefficient G_N = 1 / √(8π)`.
4. **Matter-Gauge Minimal Coupling & Aharonov-Bohm Interference (`LayerB.MinimalCoupling`)**:
   - `coupledAmplitude k φ qA = expAmplitude 1 (k * φ + qA)`, path multiplicativity,
     unit modulus `Complex.normSq (coupledAmplitude k φ qA) = 1`, gauge invariance of observables,
     Aharonov-Bohm two-path interference `2 + 2 * cos ((k * φ₁ + qA₁) - (k * φ₂ + qA₂))`,
     and invariance of the matter propagation phase under BF dressing shifts `dressingProj sf w`.
5. **Kretschner-Riemann Curvature Action & History Path Dependence (`LayerB.RiemannAction`)**:
   - `0 ≤ kretschnerAction md`, quadratic scaling `kretschnerAction (scaleMetricDerivs φ md) = φ^2 * kretschnerAction md`,
     quadrupling under doubling `kretschnerAction (addMetricDerivs md md) = 4 * kretschnerAction md`,
     `riemannDressing (scaleMetricDerivs φ md) = |φ| * riemannDressing md`, non-zero curvature
     witness, history path dependence (`path_dependence_exists`), and synthesis with the
     20-component 4D Riemann decomposition and Schwarzschild horizon Kretschmann-Bekenstein invariant.
-/

import UnifiedTheory.Audit.KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
import UnifiedTheory.Audit.KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge
import UnifiedTheory.LayerA.BFSourceDressing
import UnifiedTheory.LayerA.DerivedBFSplit
import UnifiedTheory.LayerA.MetricGaugeCoupling
import UnifiedTheory.LayerA.SourceFromMetric
import UnifiedTheory.LayerA.CausalActionCoefficient
import UnifiedTheory.LayerB.MinimalCoupling
import UnifiedTheory.LayerB.RiemannAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge

open UnifiedTheory.LayerA
open UnifiedTheory.LayerA.MetricConstruction
open UnifiedTheory.LayerA.GaugeConnection
open UnifiedTheory.LayerA.GravitonTTModes
open UnifiedTheory.LayerA.GaussBonnet4D
open UnifiedTheory.LayerA.CosmologicalConstant
open UnifiedTheory.LayerA.EinsteinHilbertScaleFixing
open UnifiedTheory.LayerA.MetricGaugeCoupling
open UnifiedTheory.LayerA.SourceReduction
open UnifiedTheory.LayerA.CausalActionCoefficient
open UnifiedTheory.LayerB.PropagationRule
open UnifiedTheory.LayerB.MinimalCoupling
open UnifiedTheory.LayerB.RiemannAction
open UnifiedTheory.LayerB.BekensteinHawking
open UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
open UnifiedTheory.LayerB.BekensteinBound
open UnifiedTheory.LayerC.HawkingPenroseSingularity

open KFCausalConformal4DDiamondBenchmark (sign)
open KFCausalLorentzianContractedBianchi (scalar einstein)
open KFCausalCurved4DLinearizedMetricDecomposition
  (conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (weylTensor4D)
open KFCausalCurved4DWeylElectricMagneticDecomposition (weylElectric4D weylMagnetic4D)
open KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
  (reconstructRiemannFromEinsteinAndWeyl4D
   reconstructRiemannFromEinsteinAndWeyl4D_exact)
open KFCausalCurved4DLovelockCosmologicalConstantSynthesis
  (SatisfiesEinsteinSorkinYangMills4D)
open KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
  (schwarzschildKretschmann)
open KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
  (schwarzschildInteriorTrappedSurface
   yangMills_positive_null_energy_implies_raychaudhuri_focusing
   malament_causal_sorkin_volume_and_variational_4D_bridge)
open KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge
  (kerrBekensteinHawkingEntropy
   kerr_entropy_satisfies_schwarzschild_bekenstein_bound
   kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants)

/-! ### 1. Plebanski BF Source/Dressing Split & Operator-Derived Reduction (`BFSourceDressing`, `DerivedBFSplit`, `SourceFromMetric`) -/

/-- **Plebanski BF Source/Dressing Decomposition & Idempotence**:
For any `d : SourceDressingDecomp V` and vector `v : V`, `v = d.πK v + d.πP v`,
`d.πK (d.πK v) = d.πK v`, and `d.πK v = 0 → d.sourceFunc v = 0`. -/
theorem bf_source_dressing_decomp_and_idempotence
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : SourceDressingDecomp V) (v : V) :
    v = d.πK v + d.πP v ∧
    d.πK (d.πK v) = d.πK v ∧
    (d.πK v = 0 → d.sourceFunc v = 0) := by
  have hidem : d.πK (d.πK v) = d.πK v := by
    have hcomp := LinearMap.congr_fun d.πK_idem v
    simpa [LinearMap.comp_apply] using hcomp
  exact ⟨d.decompose v, hidem, d.source_vanishes_on_P v⟩

/-- **Mutual Orthogonality and Idempotence of the Dressing Channel `πP = 1 - πK`**:
For any `d : SourceDressingDecomp V` and `v : V`, `d.πK (d.πP v) = 0`, `d.πP (d.πK v) = 0`,
`d.πP (d.πP v) = d.πP v`, and `d.sourceFunc (d.πP v) = 0`. -/
theorem bf_source_dressing_p_idempotent_and_orthogonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : SourceDressingDecomp V) (v : V) :
    d.πK (d.πP v) = 0 ∧
    d.πP (d.πK v) = 0 ∧
    d.πP (d.πP v) = d.πP v ∧
    d.sourceFunc (d.πP v) = 0 := by
  have hidem : ∀ u : V, d.πK (d.πK u) = d.πK u := fun u => by
    have hcomp := LinearMap.congr_fun d.πK_idem u
    simpa [LinearMap.comp_apply] using hcomp
  have hKP : d.πK (d.πP v) = 0 := by
    simp [SourceDressingDecomp.πP, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hidem v]
  have hPK : d.πP (d.πK v) = 0 := by
    simp [SourceDressingDecomp.πP, LinearMap.sub_apply, LinearMap.id_apply, hidem v]
  have hPP : d.πP (d.πP v) = d.πP v := by
    simp [SourceDressingDecomp.πP, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hidem v]
  exact ⟨hKP, hPK, hPP, d.source_vanishes_on_P (d.πP v) hKP⟩

/-- **Exact K-Channel Capture of the Gravitational Source Functional**:
For any `d : SourceDressingDecomp V` and `v : V`, `d.sourceFunc v = d.sourceFunc (d.πK v)`. -/
theorem bf_source_functional_solely_from_k_channel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : SourceDressingDecomp V) (v : V) :
    d.sourceFunc v = d.sourceFunc (d.πK v) := by
  have hdec := d.decompose v
  have hP0 := (bf_source_dressing_p_idempotent_and_orthogonal d v).2.2.2
  calc
    d.sourceFunc v = d.sourceFunc (d.πK v + d.πP v) := by rw [← hdec]
    _ = d.sourceFunc (d.πK v) + d.sourceFunc (d.πP v) := map_add d.sourceFunc _ _
    _ = d.sourceFunc (d.πK v) := by rw [hP0, add_zero]

/-- **Derived BF Projections from a Single Non-Zero Source Functional (`LayerA.DerivedBFSplit`)**:
Combines `sourceProj_idem`, `source_dressing_decomp`, `source_on_K`, and `source_vanishes_on_dressing`. -/
theorem derived_bf_split_sourceProj_idem_and_decomp
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sf : SourceFunctional V) (v : V) :
    (sourceProj sf) ∘ₗ (sourceProj sf) = sourceProj sf ∧
    v = sourceProj sf v + dressingProj sf v ∧
    sf.φ (sourceProj sf v) = sf.φ v ∧
    sf.φ (dressingProj sf v) = 0 :=
  ⟨sourceProj_idem sf,
   source_dressing_decomp sf v,
   source_on_K sf v,
   source_vanishes_on_dressing sf v⟩

/-- Complete derived K/P decomposition package from `LayerA.DerivedBFSplit`. -/
theorem derived_bf_split_functional_derives_decomposition_bridge
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sf : SourceFunctional V) :
    (∀ v : V, v = (decompFromFunctional sf).πK v + (decompFromFunctional sf).πP v) ∧
    (∀ v : V, (decompFromFunctional sf).πK v = 0 → sf.φ v = 0) ∧
    (∀ v : V, sf.φ (sourceProj sf v) = sf.φ v) :=
  functional_derives_decomposition sf

/-- **Operator-Induced Source Functional Non-Degeneracy & Universal Kernel Invisibility (`LayerA.SourceFromMetric`)**:
Combines `sourceFromOperator_ne_zero` and `source_vanishes_on_kernel`. -/
theorem source_from_operator_ne_zero_and_kernel_invisibility
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) (v₀ v : V)
    (h : ψ (L v₀) ≠ 0) (hv : v ∈ LinearMap.ker L) :
    sourceFromOperator L ψ ≠ 0 ∧
    (∀ ψ' : W →ₗ[ℝ] ℝ, v ∈ LinearMap.ker (sourceFromOperator L ψ')) :=
  ⟨sourceFromOperator_ne_zero L ψ v₀ h,
   source_vanishes_on_kernel L v hv⟩

/-- **Exact Preimage Kernel Characterization (`ker (ψ ∘ L) = comap L (ker ψ)`)**:
Combines `source_ker_eq_comap` and `source_ker_contains_operator_ker`. -/
theorem source_from_operator_ker_eq_comap_and_contains_ker
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) :
    LinearMap.ker (sourceFromOperator L ψ) = (LinearMap.ker ψ).comap L ∧
    LinearMap.ker L ≤ LinearMap.ker (sourceFromOperator L ψ) :=
  ⟨source_ker_eq_comap L ψ,
   source_ker_contains_operator_ker L ψ⟩

/-- **Operator-Derived K/P Split & Gauge-Mode Dressing Theorem**:
Combines `operator_decomposition_properties` and `gauge_is_dressing`. -/
theorem source_from_operator_decomposition_and_gauge_is_dressing
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) (v₀ v : V)
    (h : ψ (L v₀) ≠ 0) (hv : L v = 0) :
    (let sf := sourceFunctionalFromOperator L ψ v₀ h
     (∀ u : V, u = (decompFromFunctional sf).πK u + (decompFromFunctional sf).πP u) ∧
     (∀ u : V, (decompFromFunctional sf).πK u = 0 → sf.φ u = 0) ∧
     (∀ u : V, sf.φ (sourceProj sf u) = sf.φ u)) ∧
    (sourceFunctionalFromOperator L ψ v₀ h).φ v = 0 :=
  ⟨operator_decomposition_properties L ψ v₀ h,
   gauge_is_dressing L ψ v₀ h v hv⟩

/-- **Primitive Reduction `3 → 2` Master Bridge**:
Combines `reduction_3_to_2` with `decompositionFromOperator` idempotence and K-channel capture. -/
theorem primitive_reduction_3_to_2_and_bf_master
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    (∃ sd : SourceDressingDecomp V,
      (∀ v, v = sd.πK v + sd.πP v) ∧
      (∀ v, sd.πK v = 0 → (sourceFromOperator L ψ) v = 0)) ∧
    (∀ v : V,
      (decompositionFromOperator L ψ v₀ h).sourceFunc v =
        (decompositionFromOperator L ψ v₀ h).sourceFunc
          ((decompositionFromOperator L ψ v₀ h).πK v)) :=
  ⟨reduction_3_to_2 L ψ v₀ h,
   bf_source_functional_solely_from_k_channel (decompositionFromOperator L ψ v₀ h)⟩

/-! ### 2. 4D Yang-Mills Metric-Gauge Coupling & Unique 4D Tracelessness (`LayerA.MetricGaugeCoupling`) -/

/-- **Yang-Mills Field-Strength Norm Non-Negativity & Derived Stress-Energy Trace Formula**:
Combines `fieldStrengthNorm_nonneg`, `stressEnergyTrace_eq`, and `stressEnergyTrace_eq_legacy`. -/
theorem metric_gauge_fieldStrengthNorm_nonneg_and_trace_formula
    {n g_dim : ℕ} (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim) :
    0 ≤ fieldStrengthNorm sc conn ∧
    stressEnergyTrace sc conn = (1 - (n : ℝ) / 4) * fieldStrengthNorm sc conn ∧
    stressEnergyTrace sc conn = gaugeStressEnergyTrace n (fieldStrengthNorm sc conn) :=
  ⟨fieldStrengthNorm_nonneg sc conn,
   stressEnergyTrace_eq sc conn,
   stressEnergyTrace_eq_legacy sc conn⟩

/-- **Exact 4D Yang-Mills Stress-Energy Tracelessness & Dimensional Uniqueness (`d = 4`)**:
Combines `gauge_traceless_4d`, `four_is_unique_traceless`, and `stressEnergyTrace_zero_4d`. -/
theorem metric_gauge_4d_traceless_and_unique_dimension
    {g_dim : ℕ} (sc₄ : StructureConstants g_dim) (conn₄ : ConnectionData 4 g_dim)
    (norm_sq : ℝ) :
    gaugeStressEnergyTrace 4 norm_sq = 0 ∧
    (∀ n : ℕ, (∀ sq : ℝ, gaugeStressEnergyTrace n sq = 0) ↔ n = 4) ∧
    stressEnergyTrace sc₄ conn₄ = 0 :=
  ⟨gauge_traceless_4d norm_sq,
   four_is_unique_traceless,
   stressEnergyTrace_zero_4d sc₄ conn₄⟩

/-- **Non-Zero Gauge Trace in `d ≠ 4` & Gravity/Gauge K/P Separation Package**:
Combines `gauge_trace_nonzero_general` and `gauge_trace_separation`. -/
theorem metric_gauge_non4d_nonzero_trace_and_separation
    {n g_dim : ℕ} (hn : n ≠ 4) (norm_sq : ℝ) (hF : norm_sq ≠ 0) :
    gaugeStressEnergyTrace n norm_sq ≠ 0 ∧
    (∀ sq : ℝ, gaugeStressEnergyTrace 4 sq = 0) ∧
    (∀ d : ℕ, (∀ sq : ℝ, gaugeStressEnergyTrace d sq = 0) ↔ d = 4) ∧
    (∀ (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim),
      0 ≤ fieldStrengthNorm sc conn) :=
  ⟨gauge_trace_nonzero_general n hn norm_sq hF,
   gauge_trace_separation⟩

/-- **4D Traceless-but-Sourceful Gauge Field Theorem**:
When `fieldStrengthNorm sc₄ conn₄ ≠ 0` in 4D, `0 < fieldStrengthNorm sc₄ conn₄` while both
`gaugeStressEnergyTrace 4 (fieldStrengthNorm sc₄ conn₄) = 0` and `stressEnergyTrace sc₄ conn₄ = 0`. -/
theorem metric_gauge_traceless_but_sourceful_4d_bridge
    {g_dim : ℕ} (sc₄ : StructureConstants g_dim) (conn₄ : ConnectionData 4 g_dim)
    (hF : fieldStrengthNorm sc₄ conn₄ ≠ 0) :
    0 < fieldStrengthNorm sc₄ conn₄ ∧
    gaugeStressEnergyTrace 4 (fieldStrengthNorm sc₄ conn₄) = 0 ∧
    stressEnergyTrace sc₄ conn₄ = 0 :=
  ⟨(traceless_but_sourceful sc₄ conn₄ hF).1,
   (traceless_but_sourceful sc₄ conn₄ hF).2,
   stressEnergyTrace_zero_4d sc₄ conn₄⟩

/-- **4D `SU(3)` Gauge Stress-Energy Tracelessness ↔ 4D Weyl Conformal/Traceless Split**:
In `d = 4`, the `SU(3)` (`g_dim = 8`) Yang-Mills stress-energy tensor is traceless
(`stressEnergyTrace sc₃ conn₃ = 0`), and on the gravity side the 4D Weyl tensor vanishes
on `conformalPartMetricDerivs4D md` and depends solely on `tracelessPartMetricDerivs4D md`. -/
theorem metric_gauge_su3_4d_traceless_and_weyl_conformal_split
    (md : MetricDerivs 4) (a b c d : Fin 4)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8) :
    stressEnergyTrace sc₃ conn₃ = 0 ∧
    0 ≤ fieldStrengthNorm sc₃ conn₃ ∧
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
    weylTensor4D md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d :=
  ⟨stressEnergyTrace_zero_4d sc₃ conn₃,
   fieldStrengthNorm_nonneg sc₃ conn₃,
   KFCausalCurved4DLinearizedWeylRicciSplit.weylTensor4D_conformalPart_eq_zero md a b c d,
   KFCausalCurved4DLinearizedWeylRicciSplit.weylTensor4D_eq_tracelessPart md a b c d⟩

/-- **4D `SU(3)` Tracelessness & Einstein-Sorkin-Yang-Mills Scalar Locking**:
Because `stressEnergyTrace sc₃ conn₃ = 0` in 4D, the trace of the 4D Einstein-Sorkin-Yang-Mills
equation locks the scalar curvature directly to the Sorkin cosmological constant:
`scalar md sign = 4 * sorkinLambda ρ V > 0` and `(scalar md sign)^2 * (ρ * V) = 16`. -/
theorem metric_gauge_su3_4d_einstein_sorkin_yang_mills_compatibility
    (md : MetricDerivs 4) (ρ V κ : ℝ) (hρ : 0 < ρ) (hV : 0 < V)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8) :
    stressEnergyTrace sc₃ conn₃ = 0 ∧
    0 ≤ fieldStrengthNorm sc₃ conn₃ ∧
    (SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc₃ conn₃ →
      scalar md sign = 4 * sorkinLambda ρ V ∧
      0 < scalar md sign ∧
      (scalar md sign) ^ 2 * (ρ * V) = 16) := by
  have hvar := malament_causal_sorkin_volume_and_variational_4D_bridge
    md ρ V κ hρ hV sc₃ conn₃
  exact ⟨stressEnergyTrace_zero_4d sc₃ conn₃,
    fieldStrengthNorm_nonneg sc₃ conn₃,
    fun hsat => hvar.2.2.2.2 (hvar.2.2.2.1.mp hsat)⟩

/-- **Four-Dimensional Coincidence Bridge (Yang-Mills Tracelessness + Graviton TT Modes + Gauss-Bonnet)**:
Unites `four_is_unique_traceless` with `gravitonTotalComponents 4 = 10 ∧ gravitonTTModes 3 = 0`,
`gravitonTTModes 4 = 2`, and 4D Gauss-Bonnet tensor vanishing `gaussBonnetTensor R_curv a b = 0`. -/
theorem metric_gauge_4d_triple_coincidence_and_gauss_bonnet_bridge
    (R_curv : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    (∀ n : ℕ, (∀ sq : ℝ, gaugeStressEnergyTrace n sq = 0) ↔ n = 4) ∧
    (gravitonTotalComponents 4 = 10 ∧ gravitonTTModes 3 = 0) ∧
    gravitonTTModes 4 = 2 ∧
    gravitonTotalComponents 4 + 5 * gravitonTTModes 4 = 20 ∧
    gaussBonnetTensor R_curv a b = 0 :=
  ⟨four_is_unique_traceless,
   ⟨by decide, by decide⟩,
   by decide,
   by decide,
   gaussBonnet_vanishes_4d R_curv a b⟩

/-- **4D Yang-Mills Non-Negative Field-Strength Norm Implies Raychaudhuri Null Focusing**:
For any gravitational coupling `0 ≤ κ`, `0 ≤ fieldStrengthNorm sc₃ conn₃` implies
`NEC (κ * fieldStrengthNorm sc₃ conn₃)` and
`raychaudhuri_rhs θ σ_sq (κ * fieldStrengthNorm sc₃ conn₃) ≤ -(1 / 2) * θ ^ 2`. -/
theorem metric_gauge_positive_null_energy_raychaudhuri_focusing
    (θ σ_sq κ : ℝ) (hShear : ShearNonneg σ_sq) (hκ : 0 ≤ κ)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8) :
    0 ≤ fieldStrengthNorm sc₃ conn₃ ∧
    stressEnergyTrace sc₃ conn₃ = 0 ∧
    NEC (κ * fieldStrengthNorm sc₃ conn₃) ∧
    raychaudhuri_rhs θ σ_sq (κ * fieldStrengthNorm sc₃ conn₃) ≤ -(1 / 2) * θ ^ 2 := by
  have hF := fieldStrengthNorm_nonneg sc₃ conn₃
  have hfocus := yangMills_positive_null_energy_implies_raychaudhuri_focusing
    θ σ_sq κ (fieldStrengthNorm sc₃ conn₃) hShear hκ hF
  exact ⟨hF, stressEnergyTrace_zero_4d sc₃ conn₃, hfocus.1, hfocus.2⟩

/-! ### 3. Benincasa-Dowker 4D Causal Action Coefficient `c = 1 / 2` & Reduced Planck Scale (`LayerA.CausalActionCoefficient`) -/

/-- **4D Causal Action Coefficient `c = 1 / 2` & Discreteness Length Formula**:
Combines `causalCoefficient = 1 / 2`, `0 < causalCoefficient`, and `discreteness_length_c_half`. -/
theorem causal_action_coefficient_value_and_discreteness_length
    (G_N : ℝ) (hG : 0 ≤ G_N) :
    causalCoefficient = 1 / 2 ∧
    0 < causalCoefficient ∧
    discretenessLength causalCoefficient G_N = Real.sqrt (8 * Real.pi) * planckLength G_N :=
  ⟨rfl, by unfold causalCoefficient; norm_num, discreteness_length_c_half G_N hG⟩

/-- **Squared Discreteness Length at the Benincasa-Dowker Coefficient `c = 1 / 2`**:
At `c = causalCoefficient = 1 / 2`, `(discretenessLength causalCoefficient G_N)^2 = 8 * π * G_N`. -/
theorem causal_action_coefficient_discreteness_length_sq_eq_8piG
    (G_N : ℝ) (hG : 0 ≤ G_N) :
    discretenessLength causalCoefficient G_N ^ 2 = 8 * Real.pi * G_N := by
  rw [discreteness_matching causalCoefficient G_N (by unfold causalCoefficient; norm_num) hG,
      causalCoefficient]
  ring

/-- **Reduced Planck Mass Ratio (`ℓ_P / ℓ_disc = 1 / √(8π)`) and Reciprocal**:
For `0 < G_N`, `planckLength G_N / discretenessLength causalCoefficient G_N = 1 / √(8π)` and
`discretenessLength causalCoefficient G_N / planckLength G_N = √(8π)`. -/
theorem causal_action_coefficient_reduced_planck_mass_ratio
    (G_N : ℝ) (hG : 0 < G_N) :
    planckLength G_N / discretenessLength causalCoefficient G_N =
      1 / Real.sqrt (8 * Real.pi) ∧
    discretenessLength causalCoefficient G_N / planckLength G_N =
      Real.sqrt (8 * Real.pi) := by
  refine ⟨discreteness_mass_ratio G_N hG, ?_⟩
  rw [discreteness_length_c_half G_N hG.le]
  have hP : planckLength G_N ≠ 0 := by
    rw [planckLength]; exact ne_of_gt (Real.sqrt_pos.mpr hG)
  exact mul_div_cancel_right₀ (Real.sqrt (8 * Real.pi)) hP

/-- **Comparison of Reduced (`c = 1/2`) vs Unreduced (`c = 1/(16π)`) Einstein-Hilbert Scales**:
At `c = 1 / (16 * π)`, `discretenessLength (1 / (16 * π)) G_N = planckLength G_N`, whereas at the
derived 4D Benincasa-Dowker coefficient `causalCoefficient = 1 / 2`,
`discretenessLength causalCoefficient G_N ^ 2 = 8 * π * discretenessLength (1 / (16 * π)) G_N ^ 2`. -/
theorem causal_action_coefficient_vs_unreduced_einstein_hilbert_scale
    (G_N : ℝ) (hG : 0 ≤ G_N) :
    discretenessLength (1 / (16 * Real.pi)) G_N = planckLength G_N ∧
    discretenessLength causalCoefficient G_N =
      Real.sqrt (8 * Real.pi) * discretenessLength (1 / (16 * Real.pi)) G_N ∧
    discretenessLength causalCoefficient G_N ^ 2 =
      8 * Real.pi * discretenessLength (1 / (16 * Real.pi)) G_N ^ 2 := by
  have hunred := discreteness_eq_planck_iff G_N hG
  have hhalf := discreteness_length_c_half G_N hG
  have hsq_half := causal_action_coefficient_discreteness_length_sq_eq_8piG G_N hG
  have hsq_planck : planckLength G_N ^ 2 = G_N := by
    unfold planckLength
    exact Real.sq_sqrt hG
  refine ⟨hunred, ?_, ?_⟩
  · rw [hunred]; exact hhalf
  · rw [hunred, hsq_planck]; exact hsq_half

/-- **Benincasa-Dowker `c = 1 / 2` Bridge to Bekenstein Bound & Sorkin Causal-Set Cosmology**:
Links `8 * π * causalCoefficient = 4 * π` to Schwarzschild Bekenstein saturation
`bekensteinBound (2 * M) M = (8 * π * causalCoefficient) * M^2` and Sorkin's causal-set
cosmological constant `0 < sorkinLambda ρ V ∧ sorkinLambda ρ V ^ 2 * (ρ * V) = 1`. -/
theorem causal_action_coefficient_bekenstein_hawking_and_sorkin_bridge
    (G_N M ρ V : ℝ) (hG : 0 ≤ G_N) (hρ : 0 < ρ) (hV : 0 < V) :
    discretenessLength causalCoefficient G_N ^ 2 = 8 * Real.pi * G_N ∧
    bekensteinBound (2 * M) M = bekensteinHawkingEntropy M ∧
    bekensteinBound (2 * M) M = (8 * Real.pi * causalCoefficient) * M ^ 2 ∧
    0 < sorkinLambda ρ V ∧
    sorkinLambda ρ V ^ 2 * (ρ * V) = 1 := by
  refine ⟨causal_action_coefficient_discreteness_length_sq_eq_8piG G_N hG,
    schwarzschild_saturates_bound M, ?_,
    sorkinLambda_pos ρ V hρ hV,
    lambda_squared_times_N ρ V hρ hV⟩
  rw [schwarzschild_bound_eq, causalCoefficient]
  ring

/-! ### 4. Minimal Matter-Gauge Covariant Coupling & Aharonov-Bohm Interference (`LayerB.MinimalCoupling`) -/

/-- **Minimal Coupling Phase Shift & Path-Composition Multiplicativity**:
Combines `coupled_eq_shifted` and `coupled_multiplicative`. -/
theorem minimal_coupling_shifted_phase_and_multiplicativity
    (k φ φ₁ φ₂ qA qA₁ qA₂ : ℝ) :
    coupledAmplitude k φ qA = expAmplitude 1 (k * φ + qA) ∧
    coupledAmplitude k (φ₁ + φ₂) (qA₁ + qA₂) =
      coupledAmplitude k φ₁ qA₁ * coupledAmplitude k φ₂ qA₂ :=
  ⟨coupled_eq_shifted k φ qA,
   coupled_multiplicative k φ₁ φ₂ qA₁ qA₂⟩

/-- **Minimal Coupling Probability Conservation (`|z|^2 = 1`) & Gauge Invariance**:
Combines `coupled_unit_modulus` and `coupled_observable_gauge_invariant`. -/
theorem minimal_coupling_unit_modulus_and_gauge_invariance
    (k φ qA α : ℝ) :
    Complex.normSq (coupledAmplitude k φ qA) = 1 ∧
    Complex.normSq (coupledAmplitude k φ (qA + α)) =
      Complex.normSq (coupledAmplitude k φ qA) ∧
    Complex.normSq (coupledAmplitude k φ (qA + α)) = 1 :=
  ⟨coupled_unit_modulus k φ qA,
   coupled_observable_gauge_invariant k φ qA α,
   coupled_unit_modulus k φ (qA + α)⟩

/-- **Aharonov-Bohm Two-Path Interference & Constructive/Destructive Fringe Extrema**:
Proves `|z₁ + z₂|^2 = 2 + 2 * cos ((k * φ₁ + qA₁) - (k * φ₂ + qA₂))`, with constructive
maximum `4` when the total phases agree and destructive minimum `0` when they differ by `π`. -/
theorem minimal_coupling_aharonov_bohm_two_path_interference
    (k φ₁ φ₂ qA₁ qA₂ : ℝ) :
    Complex.normSq (coupledAmplitude k φ₁ qA₁ + coupledAmplitude k φ₂ qA₂) =
      2 + 2 * Real.cos ((k * φ₁ + qA₁) - (k * φ₂ + qA₂)) ∧
    (k * φ₁ + qA₁ = k * φ₂ + qA₂ →
      Complex.normSq (coupledAmplitude k φ₁ qA₁ + coupledAmplitude k φ₂ qA₂) = 4) ∧
    ((k * φ₁ + qA₁) - (k * φ₂ + qA₂) = Real.pi →
      Complex.normSq (coupledAmplitude k φ₁ qA₁ + coupledAmplitude k φ₂ qA₂) = 0) := by
  refine ⟨coupled_interference k φ₁ φ₂ qA₁ qA₂, ?_, ?_⟩
  · intro heq
    rw [coupled_interference, heq, sub_self, Real.cos_zero]
    ring
  · intro hpi
    rw [coupled_interference, hpi, Real.cos_pi]
    ring

/-- **Minimal Coupling + Derived BF Source/Dressing Split Bridge**:
Adding any BF dressing perturbation `dressingProj sf w` to a field configuration `v` leaves
the source functional `sf.φ` invariant (`sf.φ (v + dressingProj sf w) = sf.φ v`), so the
matter propagation phase `k * sf.φ` is unchanged while the gauge holonomy `qA` shifts the
coupled amplitude `coupledAmplitude k (sf.φ v) qA`. -/
theorem minimal_coupling_derived_and_bf_dressing_invariance
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sf : SourceFunctional V) (v w : V) (k qA : ℝ) :
    sf.φ (v + dressingProj sf w) = sf.φ v ∧
    coupledAmplitude k (sf.φ (v + dressingProj sf w)) qA =
      coupledAmplitude k (sf.φ v) qA ∧
    coupledAmplitude k (sf.φ (sourceProj sf v)) qA =
      coupledAmplitude k (sf.φ v) qA ∧
    Complex.normSq (coupledAmplitude k (sf.φ v) qA) = 1 := by
  have hdress : sf.φ (v + dressingProj sf w) = sf.φ v := by
    rw [map_add, source_vanishes_on_dressing sf w, add_zero]
  exact ⟨hdress,
    by rw [hdress],
    by rw [source_on_K sf v],
    coupled_unit_modulus k (sf.φ v) qA⟩

/-- **Minimal Coupling + 4D Traceless Yang-Mills Bridge**:
Unites the 5-part `minimal_coupling_derived` package with 4D Yang-Mills stress-energy
tracelessness `stressEnergyTrace sc₄ conn₄ = 0`. -/
theorem minimal_coupling_4d_traceless_gauge_and_aharonov_bohm_bridge
    {g_dim : ℕ} (sc₄ : StructureConstants g_dim) (conn₄ : ConnectionData 4 g_dim) :
    ((∀ k φ qA : ℝ, coupledAmplitude k φ qA = expAmplitude 1 (k * φ + qA)) ∧
     (∀ k φ₁ φ₂ qA₁ qA₂ : ℝ,
       coupledAmplitude k (φ₁ + φ₂) (qA₁ + qA₂) =
         coupledAmplitude k φ₁ qA₁ * coupledAmplitude k φ₂ qA₂) ∧
     (∀ k φ qA : ℝ, Complex.normSq (coupledAmplitude k φ qA) = 1) ∧
     (∀ k φ qA α : ℝ,
       Complex.normSq (coupledAmplitude k φ (qA + α)) =
         Complex.normSq (coupledAmplitude k φ qA)) ∧
     (∀ k φ₁ φ₂ qA₁ qA₂ : ℝ,
       Complex.normSq (coupledAmplitude k φ₁ qA₁ + coupledAmplitude k φ₂ qA₂) =
         2 + 2 * Real.cos ((k * φ₁ + qA₁) - (k * φ₂ + qA₂)))) ∧
    stressEnergyTrace sc₄ conn₄ = 0 ∧
    0 ≤ fieldStrengthNorm sc₄ conn₄ :=
  ⟨minimal_coupling_derived,
   stressEnergyTrace_zero_4d sc₄ conn₄,
   fieldStrengthNorm_nonneg sc₄ conn₄⟩

/-! ### 5. Kretschner-Riemann Curvature Action, Path Dependence & 4D Curved Gravity Synthesis (`LayerB.RiemannAction`) -/

/-- **Kretschner-Riemann Action Non-Negativity & Quadratic Scaling (`LayerB.RiemannAction`)**:
Combines `kretschnerAction_nonneg`, `R_metric_scale`, and `kretschnerAction_scale`. -/
theorem riemann_kretschner_action_nonneg_and_quadratic_scaling
    {n : ℕ} (φ : ℝ) (md : MetricDerivs n) (a b c d : Fin n) :
    0 ≤ kretschnerAction md ∧
    R_metric (scaleMetricDerivs φ md) a b c d = φ * R_metric md a b c d ∧
    kretschnerAction (scaleMetricDerivs φ md) = φ ^ 2 * kretschnerAction md :=
  ⟨kretschnerAction_nonneg md,
   R_metric_scale φ md a b c d,
   kretschnerAction_scale φ md⟩

/-- **Riemann Tensor Additivity & Quadrupling of Kretschner Action under Doubling**:
For any `md₁, md₂ : MetricDerivs n`, `R_metric (addMetricDerivs md₁ md₂) = R_metric md₁ + R_metric md₂`
and `kretschnerAction (addMetricDerivs md₁ md₁) = 4 * kretschnerAction md₁`. -/
theorem riemann_kretschner_action_additivity_and_quadruple_under_doubling
    {n : ℕ} (md₁ md₂ : MetricDerivs n) (a b c d : Fin n) :
    R_metric (UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₂) a b c d =
      R_metric md₁ a b c d + R_metric md₂ a b c d ∧
    kretschnerAction (UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₁) =
      4 * kretschnerAction md₁ := by
  refine ⟨R_metric_add md₁ md₂ a b c d, ?_⟩
  have h2 : UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₁ =
      scaleMetricDerivs 2 md₁ := by
    cases md₁
    simp only [UnifiedTheory.LayerB.RiemannAction.addMetricDerivs, scaleMetricDerivs]
    congr <;> funext _ _ _ _ <;> ring
  rw [h2, kretschnerAction_scale]
  ring

/-- **Riemann Dressing Non-Negativity, Homogeneous Scaling & Non-Zero Curvature Witness**:
Proves `0 ≤ riemannDressing md`, `riemannDressing (scaleMetricDerivs φ md) = |φ| * riemannDressing md`,
and exhibits the non-zero curvature witness on `MetricDerivs 2`. -/
theorem riemann_dressing_nonneg_scaling_and_nonzero_witness
    {n : ℕ} (φ : ℝ) (md : MetricDerivs n) :
    0 ≤ riemannDressing md ∧
    riemannDressing (scaleMetricDerivs φ md) = |φ| * riemannDressing md ∧
    (∃ md₂ : MetricDerivs 2, 0 < kretschnerAction md₂) ∧
    (∃ md₂ : MetricDerivs 2, 0 < riemannDressing md₂) := by
  refine ⟨riemannDressing_nonneg md, ?_,
    kretschnerAction_nonzero_exists, riemannDressing_nonzero_exists⟩
  unfold riemannDressing
  rw [kretschnerAction_scale, Real.sqrt_mul (sq_nonneg φ), Real.sqrt_sq_eq_abs]

/-- **Accumulated Curvature Action Path Dependence & Riemann Action Capstone**:
Combines `path_dependence_exists` and `riemann_action_capstone`. -/
theorem riemann_action_history_path_dependence_and_capstone :
    (∃ (md₁ md₂ : MetricDerivs 2),
      accumulatedAction [md₁, md₂] ≠
        accumulatedAction [UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₂]) ∧
    ((∀ md : MetricDerivs 2, 0 ≤ kretschnerAction md) ∧
     (∃ md : MetricDerivs 2, 0 < kretschnerAction md) ∧
     (∀ (φ : ℝ) (md : MetricDerivs 2),
       kretschnerAction (scaleMetricDerivs φ md) = φ ^ 2 * kretschnerAction md) ∧
     (∃ (md₁ md₂ : MetricDerivs 2),
       accumulatedAction [md₁, md₂] ≠
         accumulatedAction [UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₂])) :=
  ⟨path_dependence_exists, riemann_action_capstone⟩

/-- **4D Linearized Kretschner Action + 20-Component Riemann Reconstruction + Schwarzschild Horizon Invariant**:
Unites `kretschnerAction md ≥ 0` and quadratic scaling on `MetricDerivs 4` with the exact
20-component Einstein + Weyl reconstruction of `R_metric md` and the non-linear Schwarzschild
horizon Kretschmann-Bekenstein identity `schwarzschildKretschmann M (2M) * (bekensteinBound (2M) M)^2 = 12 * π^2`. -/
theorem riemann_action_4D_conformal_traceless_and_schwarzschild_kretschmann_bridge
    (φ M : ℝ) (hM : 0 < M) (md : MetricDerivs 4) (a b c d : Fin 4) :
    0 ≤ kretschnerAction md ∧
    kretschnerAction (scaleMetricDerivs φ md) = φ ^ 2 * kretschnerAction md ∧
    reconstructRiemannFromEinsteinAndWeyl4D
      (einstein md sign) (weylElectric4D md) (weylMagnetic4D md) a b c d =
      R_metric md a b c d ∧
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
    schwarzschildKretschmann M (schwarzschildRadius M) *
      (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2 :=
  ⟨kretschnerAction_nonneg md,
   kretschnerAction_scale φ md,
   reconstructRiemannFromEinsteinAndWeyl4D_exact md a b c d,
   KFCausalCurved4DLinearizedWeylRicciSplit.weylTensor4D_conformalPart_eq_zero md a b c d,
   (kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants M (ne_of_gt hM)).2.2.2⟩

/-- **MASTER SYNTHESIS — Curved 4D Plebanski BF Source/Dressing, Metric-Gauge Coupling, Causal Action Coefficient, Minimal Coupling & Riemann Action**:
Unites all seven `LayerA`/`LayerB` modules (`BFSourceDressing`, `DerivedBFSplit`,
`SourceFromMetric`, `MetricGaugeCoupling`, `CausalActionCoefficient`, `MinimalCoupling`,
`RiemannAction`) with the curved 4D Weyl-Ricci-Lovelock-Schwarzschild-Hawking-Penrose-Christodoulou-Bekenstein
framework into a single machine-checked capstone theorem. -/
theorem curved_4D_bf_source_dressing_metric_gauge_minimal_riemann_master_synthesis
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) (v₀ : V) (hL : ψ (L v₀) ≠ 0)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (G_N : ℝ) (hG_pos : 0 < G_N)
    (k_mc φ₁ φ₂ qA₁ qA₂ : ℝ)
    (md : MetricDerivs 4) (a b c d : Fin 4)
    (M J : ℝ) (hsub : kerrSubextremal M J) (hM : 0 < M) :
    -- (1) Operator-derived Plebanski BF K/P decomposition & 3 → 2 primitive reduction
    ((∃ sd : SourceDressingDecomp V,
        (∀ v, v = sd.πK v + sd.πP v) ∧
        (∀ v, sd.πK v = 0 → (sourceFromOperator L ψ) v = 0)) ∧
     LinearMap.ker (sourceFromOperator L ψ) = (LinearMap.ker ψ).comap L) ∧
    -- (2) 4D Yang-Mills stress-energy tracelessness & dimensional uniqueness
    (stressEnergyTrace sc₃ conn₃ = 0 ∧
     0 ≤ fieldStrengthNorm sc₃ conn₃ ∧
     (∀ n : ℕ, (∀ sq : ℝ, gaugeStressEnergyTrace n sq = 0) ↔ n = 4)) ∧
    -- (3) Benincasa-Dowker 4D causal action coefficient c = 1/2 & reduced Planck scale
    (causalCoefficient = 1 / 2 ∧
     discretenessLength causalCoefficient G_N = Real.sqrt (8 * Real.pi) * planckLength G_N ∧
     discretenessLength causalCoefficient G_N ^ 2 = 8 * Real.pi * G_N ∧
     planckLength G_N / discretenessLength causalCoefficient G_N =
       1 / Real.sqrt (8 * Real.pi)) ∧
    -- (4) Minimal matter-gauge coupling, unit modulus & Aharonov-Bohm interference
    (coupledAmplitude k_mc (φ₁ + φ₂) (qA₁ + qA₂) =
       coupledAmplitude k_mc φ₁ qA₁ * coupledAmplitude k_mc φ₂ qA₂ ∧
     Complex.normSq (coupledAmplitude k_mc φ₁ qA₁) = 1 ∧
     Complex.normSq (coupledAmplitude k_mc φ₁ qA₁ + coupledAmplitude k_mc φ₂ qA₂) =
       2 + 2 * Real.cos ((k_mc * φ₁ + qA₁) - (k_mc * φ₂ + qA₂))) ∧
    -- (5) Kretschner-Riemann action, history path dependence & 4D curved black-hole invariants
    (0 ≤ kretschnerAction md ∧
     (∃ (md₁ md₂ : MetricDerivs 2),
       accumulatedAction [md₁, md₂] ≠
         accumulatedAction [UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₂]) ∧
     weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
     M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) ∧
     IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M ∧
     schwarzschildKretschmann M (schwarzschildRadius M) *
       (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2) := by
  have hkerr :=
    kerr_entropy_satisfies_schwarzschild_bekenstein_bound M J
  exact ⟨⟨reduction_3_to_2 L ψ v₀ hL, source_ker_eq_comap L ψ⟩,
    ⟨stressEnergyTrace_zero_4d sc₃ conn₃,
      fieldStrengthNorm_nonneg sc₃ conn₃,
      four_is_unique_traceless⟩,
    ⟨rfl,
      discreteness_length_c_half G_N hG_pos.le,
      causal_action_coefficient_discreteness_length_sq_eq_8piG G_N hG_pos.le,
      discreteness_mass_ratio G_N hG_pos⟩,
    ⟨coupled_multiplicative k_mc φ₁ φ₂ qA₁ qA₂,
      coupled_unit_modulus k_mc φ₁ qA₁,
      coupled_interference k_mc φ₁ φ₂ qA₁ qA₂⟩,
    ⟨kretschnerAction_nonneg md,
      path_dependence_exists,
      KFCausalCurved4DLinearizedWeylRicciSplit.weylTensor4D_conformalPart_eq_zero md a b c d,
      mass_energy_decomposition hsub (ne_of_gt hM),
      hkerr.1,
      (kerr_schwarzschild_limit_kretschmann_area_and_entropy_invariants M (ne_of_gt hM)).2.2.2⟩⟩

#print axioms bf_source_dressing_decomp_and_idempotence
#print axioms bf_source_dressing_p_idempotent_and_orthogonal
#print axioms bf_source_functional_solely_from_k_channel
#print axioms derived_bf_split_sourceProj_idem_and_decomp
#print axioms derived_bf_split_functional_derives_decomposition_bridge
#print axioms source_from_operator_ne_zero_and_kernel_invisibility
#print axioms source_from_operator_ker_eq_comap_and_contains_ker
#print axioms source_from_operator_decomposition_and_gauge_is_dressing
#print axioms primitive_reduction_3_to_2_and_bf_master
#print axioms metric_gauge_fieldStrengthNorm_nonneg_and_trace_formula
#print axioms metric_gauge_4d_traceless_and_unique_dimension
#print axioms metric_gauge_non4d_nonzero_trace_and_separation
#print axioms metric_gauge_traceless_but_sourceful_4d_bridge
#print axioms metric_gauge_su3_4d_traceless_and_weyl_conformal_split
#print axioms metric_gauge_su3_4d_einstein_sorkin_yang_mills_compatibility
#print axioms metric_gauge_4d_triple_coincidence_and_gauss_bonnet_bridge
#print axioms metric_gauge_positive_null_energy_raychaudhuri_focusing
#print axioms causal_action_coefficient_value_and_discreteness_length
#print axioms causal_action_coefficient_discreteness_length_sq_eq_8piG
#print axioms causal_action_coefficient_reduced_planck_mass_ratio
#print axioms causal_action_coefficient_vs_unreduced_einstein_hilbert_scale
#print axioms causal_action_coefficient_bekenstein_hawking_and_sorkin_bridge
#print axioms minimal_coupling_shifted_phase_and_multiplicativity
#print axioms minimal_coupling_unit_modulus_and_gauge_invariance
#print axioms minimal_coupling_aharonov_bohm_two_path_interference
#print axioms minimal_coupling_derived_and_bf_dressing_invariance
#print axioms minimal_coupling_4d_traceless_gauge_and_aharonov_bohm_bridge
#print axioms riemann_kretschner_action_nonneg_and_quadratic_scaling
#print axioms riemann_kretschner_action_additivity_and_quadruple_under_doubling
#print axioms riemann_dressing_nonneg_scaling_and_nonzero_witness
#print axioms riemann_action_history_path_dependence_and_capstone
#print axioms riemann_action_4D_conformal_traceless_and_schwarzschild_kretschmann_bridge
#print axioms curved_4D_bf_source_dressing_metric_gauge_minimal_riemann_master_synthesis

end UnifiedTheory.Audit.KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge
