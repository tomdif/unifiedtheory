/- Contracted Bianchi Identity, 4D Trace-Reversal Linearized Einstein Operator,
Linearized Curvature Superposition (`mdAdd`/`mdNeg`), Lovelock Endpoint Decomposition,
`1 + 1` Null-Cone Bilinear Determination, Cosmological-Constant Substrate Count
(`Λ² N(Λ) = 1`, `N(10⁻¹²²) = 10²⁴⁴`), 24-Permutation Gauss–Bonnet Kronecker Expansion,
Graviton TT Polarization & P-Sector Source Invisibility, and Raychaudhuri Null Focusing
Bridged with Curved 4D Plane-Wave / Malament / Hauptvermutung / Kretschmann Gravity:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerA.BianchiIdentity`,
   `UnifiedTheory.LayerA.LinearizedEinstein`, and `UnifiedTheory.LayerA.LinearizedFieldEqs`,
   certifying the once-contracted and twice-contracted Bianchi identities (`2 * divRic = dScalar`,
   `divRic - dScalar / 2 = 0`), the 4D involutive trace-reversal operator
   `traceReversal 4 (traceReversal 4 h) = h` (`tr(L(h)) = (1 - n / 2) * tr(h)`),
   and exact linear superposition (`mdAdd`, `mdNeg`) of `R_metric`, `dR_metric`, `divRic`,
   `dScalar`, and `div(G) = 0`.
2. Bridges `UnifiedTheory.LayerA.LovelockEinstein`, `UnifiedTheory.LayerA.NullConeTensor`,
   `UnifiedTheory.LayerA.CosmologicalConstantN`, `UnifiedTheory.LayerA.GaussBonnetExpansion`,
   `UnifiedTheory.LayerA.Graviton`, `UnifiedTheory.LayerB.FocusingBridge`, and
   `UnifiedTheory.LayerB.FocusingCoupling`, certifying:
   - Lovelock Bianchi constraint `d = -c / 2` and decomposition `naturalOf cd c (-c / 2) e = c • G + e • g`,
   - `1 + 1` Minkowski null-cone quadratic and bilinear determination (`b = 0 ∧ c = -a`),
   - Sorkin cosmological substrate count `Λ² * Nsub Λ = 1`, `Nsub (10⁻¹²²) = 10²⁴⁴`,
     agreement with de Sitter 4-volume `deSitterVolume Λ = Nsub Λ` and observer age 4-volume
     `ageVolume (10⁶¹) = 10²⁴⁴`, and Bekenstein–Hawking horizon-area square law `Nsub = BHArea²`,
   - Rank-2 Kronecker antisymmetrizer contraction `delta2_contract`, 24-permutation Gauss–Bonnet
     scalar identity `4 * gbStandard = 4 * kretschner - 16 * ricciNorm + 4 * scalarR²`, and 4D tensor vanishing,
   - Graviton DOF counting (`symmetricComponents 4 = 10`, `gravitonPolarizations 3 = 2`),
     P-sector source invisibility (`φ h = 0 → φ (K h) = 0`), and 4-fold `d = 3` spatial selection,
   - Raychaudhuri null focusing linearity (`nullFocusing_add`, `nullFocusing_neg`), conformal
     focusing proportionality `nullFocusing (conformalMD n φ) k = φ * nullFocusing (conformalMD n 1) k`,
     and GR coupling `κ = 8π > 0` signed-source focusing (`gr_signed_focusing`).
3. Unites all ten gravitational packages with the curved 4D gravitational plane waves,
   `3 + 1` Malament null-cone conformal uniqueness, causal-set Hauptvermutung, 4-branch derived
   unification, and Kretschmann–Bekenstein invariants from
   `KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge`. -/
import UnifiedTheory.LayerA.BianchiIdentity
import UnifiedTheory.LayerA.LinearizedEinstein
import UnifiedTheory.LayerA.LinearizedFieldEqs
import UnifiedTheory.LayerA.LovelockEinstein
import UnifiedTheory.LayerA.NullConeTensor
import UnifiedTheory.LayerA.CosmologicalConstantN
import UnifiedTheory.LayerA.GaussBonnetExpansion
import UnifiedTheory.LayerA.Graviton
import UnifiedTheory.LayerB.FocusingBridge
import UnifiedTheory.LayerB.FocusingCoupling
import UnifiedTheory.Audit.KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCurved4DBianchiLinearizedEinsteinLovelockWeylAntiGravityBridge

noncomputable section

open Matrix Finset
open scoped BigOperators
open UnifiedTheory.LayerA
open UnifiedTheory.LayerA.Bianchi
open UnifiedTheory.LayerA.Reduction
open UnifiedTheory.LayerA.SinglePrimitive
open UnifiedTheory.LayerA.MetricConstruction
open UnifiedTheory.LayerA.LinearizedEinstein
open UnifiedTheory.LayerA.LinearizedFieldEqs
open UnifiedTheory.LayerA.CosmologicalConstant
open UnifiedTheory.LayerA.CosmologicalConstantN
open UnifiedTheory.LayerA.GaussBonnetExpansion
open UnifiedTheory.LayerA.Graviton
open UnifiedTheory.LayerA.GravitationalPlaneWaves
open UnifiedTheory.LayerA.NullConeConformal
open UnifiedTheory.LayerA.NullConeGeneral
open UnifiedTheory.LayerA.Hauptvermutung
open UnifiedTheory.LayerA.Derived
open UnifiedTheory.LayerA.GaugeConnection
open UnifiedTheory.LayerA.MetricGaugeCoupling
open UnifiedTheory.LayerA.EinsteinHilbertScaleFixing (discretenessLength)
open UnifiedTheory.LayerA.CausalActionCoefficient
open UnifiedTheory.LayerB.SignedSource
open UnifiedTheory.LayerB.MetricDefects
open UnifiedTheory.LayerB.SourceFocusing
open UnifiedTheory.LayerB.FocusingBridge
open UnifiedTheory.LayerB.FocusingCoupling
open UnifiedTheory.LayerB.RiemannAction
open UnifiedTheory.LayerB.BekensteinHawking
open UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
open UnifiedTheory.LayerB.BekensteinBound
open KFCausalCurved4DLinearizedMetricDecomposition (conformalPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (weylTensor4D)
open KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge (schwarzschildKretschmann)
open KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge (kerrBekensteinHawkingEntropy)
open KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge
  (curved_4d_gravitational_plane_waves_null_cone_hauptvermutung_master_synthesis)

/-! ### 1. Contracted Bianchi Identity, 4D Trace-Reversal Operator, and Linearized Curvature Superposition -/

/-- Contracted Bianchi identity, 4D involutive trace-reversal linearized Einstein operator,
and linearized metric-derivative superposition package (`UnifiedTheory.LayerA.BianchiIdentity`,
`UnifiedTheory.LayerA.LinearizedEinstein`, `UnifiedTheory.LayerA.LinearizedFieldEqs`). -/
theorem bianchi_trace_reversal_and_linearized_superposition_package
    {n : ℕ} (hn : 3 ≤ n) (rd : RiemannData n) (a b c d : Fin n)
    (h_mat : Matrix (Fin n) (Fin n) ℝ) (h4 : Matrix (Fin 4) (Fin 4) ℝ)
    (md₁ md₂ : MetricDerivs n) :
    ((∑ idx : Fin n, rd.dR idx a b idx d) - dRic rd a b d + dRic rd b a d = 0 ∧
     2 * divRic rd b = dScalar rd b ∧
     divRic rd b - dScalar rd b / 2 = 0) ∧
    (Matrix.trace (traceReversal n h_mat) = (1 - (n : ℝ) / 2) * Matrix.trace h_mat ∧
     traceReversal n ≠ 0 ∧
     traceReversal 4 (traceReversal 4 h4) = h4 ∧
     (traceLinearMap (Fin n) ℝ ℝ) ∘ₗ (traceReversal n) ≠ 0) ∧
    (R_metric (mdAdd md₁ md₂) a b c d = R_metric md₁ a b c d + R_metric md₂ a b c d ∧
     R_metric (mdNeg md₁) a b c d = -(R_metric md₁ a b c d) ∧
     divRic (riemannFromMetric (mdAdd md₁ md₂)) b =
       divRic (riemannFromMetric md₁) b + divRic (riemannFromMetric md₂) b ∧
     dScalar (riemannFromMetric (mdAdd md₁ md₂)) b =
       dScalar (riemannFromMetric md₁) b + dScalar (riemannFromMetric md₂) b) :=
  ⟨⟨once_contracted rd a b d,
    contracted_bianchi rd b,
    einstein_div_free rd b⟩,
   ⟨trace_of_traceReversal n h_mat,
    trace_reversal_nontrivial n hn,
    traceReversal_involutive_4d h4,
    traceReversal_source_nontrivial n hn⟩,
   ⟨LinearizedFieldEqs.R_metric_add md₁ md₂ a b c d,
    R_metric_neg md₁ a b c d,
    divRic_add md₁ md₂ b,
    dScalar_add md₁ md₂ b⟩⟩

/-! ### 2. Lovelock Endpoint Decomposition and `1 + 1` Null-Cone Bilinear Determination -/

/-- Lovelock Bianchi constraint and endpoint decomposition combined with `1 + 1`-dimensional
Minkowski null-cone quadratic and bilinear determination (`UnifiedTheory.LayerA.LovelockEinstein`,
`UnifiedTheory.LayerA.NullConeTensor`). -/
theorem lovelock_endpoint_and_null_cone_1plus1_package
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (cd : CurvatureData T) (c d e : ℝ)
    (h_div : ∀ gradR : Ω, (c / 2 + d) • gradR = 0)
    (h_nondeg : ∃ ω : Ω, ω ≠ 0)
    (a_nc b_nc c_nc : ℝ)
    (h_nc : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a_nc b_nc c_nc v = 0) :
    (d = -c / 2 ∧
     naturalOf cd c (-c / 2) e = c • einsteinOf cd + e • cd.g_metric ∧
     (∃ a₀ b₀ : ℝ, naturalOf cd c d e = a₀ • einsteinOf cd + b₀ • cd.g_metric)) ∧
    ((b_nc = 0 ∧ c_nc = -a_nc) ∧
     (∀ v, genQuad a_nc b_nc c_nc v = (-a_nc) * minkQuad v) ∧
     (∀ v w, genBilin a_nc b_nc c_nc v w = (-a_nc) * minkBilin v w) ∧
     (∃ c₀ : ℝ, ∀ v w, genBilin a_nc b_nc c_nc v w = c₀ * minkBilin v w)) :=
  ⟨⟨lovelock_bianchi_constraint c d h_div h_nondeg,
    lovelock_decomposition cd c e,
    lovelock_endpoint cd c d e h_div h_nondeg⟩,
   ⟨null_cone_coeffs a_nc b_nc c_nc h_nc,
    null_cone_quad_1plus1 a_nc b_nc c_nc h_nc,
    null_cone_bilin_1plus1 a_nc b_nc c_nc h_nc,
    null_determines_up_to_trace_1plus1 a_nc b_nc c_nc h_nc⟩⟩

/-! ### 3. Sorkin Cosmological Constant Substrate Count `N = 1 / Λ²` and 24-Permutation Gauss–Bonnet Expansion -/

/-- Sorkin cosmological constant substrate count `Nsub Λ = 1 / Λ²` and 24-permutation
Gauss–Bonnet Kronecker expansion package (`UnifiedTheory.LayerA.CosmologicalConstantN`,
`UnifiedTheory.LayerA.GaussBonnetExpansion`). -/
theorem cosmological_constant_N_and_gauss_bonnet_expansion_package
    {n : ℕ} (Λ ε₁ ε₂ ρ V : ℝ)
    (hε₁ : 0 < ε₁) (h₁ : ε₁ ≤ Λ) (h₂ : Λ ≤ ε₂)
    (hρ : 0 < ρ) (hV : 0 < V)
    (rd : RiemannData n) (f : Fin n → Fin n → ℝ)
    (hf : ∀ a b, f a b = -(f b a)) (b₁ b₂ : Fin n) :
    (0 < Nsub Λ ∧
     Λ ^ 2 * Nsub Λ = 1 ∧
     Nsub (sorkinLambda ρ V) = ρ * V ∧
     (1 / ε₂ ^ 2 ≤ Nsub Λ ∧ Nsub Λ ≤ 1 / ε₁ ^ 2) ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) ∧
     deSitterVolume Λ = Nsub Λ ∧
     ageVolume ((10 : ℝ) ^ (61 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
       (BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))) ^ 2) ∧
    (delta2 b₂ b₁ b₁ b₂ = -(delta2 b₁ b₂ b₁ b₂) ∧
     (∑ a₁ : Fin n, ∑ a₂ : Fin n, delta2 a₁ a₂ b₁ b₂ * f a₁ a₂ = 2 * f b₁ b₂) ∧
     4 * gbStandard rd = 4 * kretschner rd - 16 * ricciNorm rd + 4 * scalarR rd ^ 2 ∧
     (∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
       ∀ a b : Fin 4, GaussBonnet4D.gaussBonnetTensor R a b = 0)) := by
  have hΛ_pos : 0 < Λ := lt_of_lt_of_le hε₁ h₁
  have hsum := cosmological_constant_N_summary
  exact ⟨⟨Nsub_pos Λ (ne_of_gt hΛ_pos),
          lambda_sq_times_Nsub Λ (ne_of_gt hΛ_pos),
          Nsub_eq_rho_V ρ V hρ hV,
          Nsub_bracket Λ ε₁ ε₂ hε₁ h₁ h₂,
          hsum.2.1,
          deSitter_eq_Nsub Λ,
          ageVolume_at_observed_age,
          Nsub_is_BHArea_squared⟩,
         ⟨delta2_antisym b₁ b₂ b₁ b₂,
          delta2_contract_antisym f hf b₁ b₂,
          gb_scalar_identity rd,
          gb_bridge_4d.1⟩⟩

/-! ### 4. Graviton Polarization DOF, P-Sector Invisibility, and Raychaudhuri Null Focusing -/

/-- Graviton DOF counting, P-sector source invisibility, Raychaudhuri null focusing linearity,
conformal focusing proportionality, and GR signed focusing (`UnifiedTheory.LayerA.Graviton`,
`UnifiedTheory.LayerB.FocusingBridge`, `UnifiedTheory.LayerB.FocusingCoupling`). -/
theorem graviton_polarizations_and_raychaudhuri_focusing_package
    {n m : ℕ} {V_space : Type*} [AddCommGroup V_space] [Module ℝ V_space]
    (φ_src : V_space →ₗ[ℝ] ℝ) (K_proj : V_space →ₗ[ℝ] V_space)
    (h_bridge : ∀ v, φ_src (K_proj v) = φ_src v)
    (h_vec : V_space) (h_traceless : φ_src h_vec = 0)
    (md₁ md₂ : MetricDerivs n) (k : Fin n → ℝ) (φ_conf : ℝ)
    (h_pos h_neg h_zero : Perturbation (m + 2))
    (hq_pos : 0 < Q h_pos) (hq_neg : Q h_neg < 0) (hq_zero : Q h_zero = 0) :
    (symmetricComponents 4 = 10 ∧
     (gravitonPolarizations 1 = 0 ∧ gravitonPolarizations 2 = 0 ∧ gravitonPolarizations 3 = 2) ∧
     gravitonPolarizations 4 = 5 ∧
     φ_src (K_proj h_vec) = 0) ∧
    (nullFocusing (mdAdd md₁ md₂) k = nullFocusing md₁ k + nullFocusing md₂ k ∧
     nullFocusing (mdNeg md₁) k = -(nullFocusing md₁ k) ∧
     nullFocusing (conformalMD n φ_conf) k = φ_conf * nullFocusing (conformalMD n 1) k) ∧
    ((0 : ℝ) < 8 * Real.pi ∧
     0 < focusing grFocusingHypothesis h_pos ∧
     focusing grFocusingHypothesis h_neg < 0 ∧
     focusing grFocusingHypothesis h_zero = 0 ∧
     focusing grFocusingHypothesis (h_pos + (-h_pos)) = 0) :=
  ⟨⟨symmetric_4d,
    gravitational_waves_require_d3,
    graviton_5_in_4d,
    graviton_invisible_to_source φ_src K_proj h_bridge h_vec h_traceless⟩,
   ⟨nullFocusing_add md₁ md₂ k,
    nullFocusing_neg md₁ k,
    conformal_focusing_proportional φ_conf k⟩,
   ⟨gr_focusing_positive,
    gr_signed_focusing.1 h_pos hq_pos,
    gr_signed_focusing.2.1 h_neg hq_neg,
    gr_signed_focusing.2.2.1 h_zero hq_zero,
    gr_signed_focusing.2.2.2 h_pos⟩⟩

/-! ### 5. Master Curved 4D Bianchi, Trace-Reversal, Lovelock, `Λ² N = 1`, Gauss–Bonnet, Graviton, and Focusing Synthesis -/

/-- Master Curved 4D Bianchi Identity, 4D Trace-Reversal Involution, Lovelock Endpoint,
`1 + 1` & `3 + 1` Null-Cone Determination, `Λ² N = 1` Substrate Count (`N(10⁻¹²²) = 10²⁴⁴`),
24-Permutation Gauss–Bonnet Expansion, Graviton Polarization, Raychaudhuri Null Focusing,
and Plane-Wave / Hauptvermutung / Kretschmann Synthesis. -/
theorem curved_4d_bianchi_linearized_einstein_lovelock_focusing_master_synthesis
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {Ω_mod : Type*} [AddCommGroup Ω_mod] [Module ℝ Ω_mod]
    (cd : CurvatureData T) (c_lov d_lov e_lov : ℝ)
    (h_div : ∀ gradR : Ω_mod, (c_lov / 2 + d_lov) • gradR = 0)
    (h_nondeg : ∃ ω : Ω_mod, ω ≠ 0)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ)
    (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) (k_null : Fin 4 → ℝ) (φ_conf : ℝ)
    (h_pos : Perturbation 4) (hq_pos : 0 < Q h_pos)
    (k₀ k₁ : ℝ) (hnull : IsNull k₀ k₁) (ε_pol : Matrix (Fin 2) (Fin 2) ℝ)
    (g₁ g₂ : Fin 4 → Fin 4 → ℝ)
    (hSym₁ : ∀ i j, g₁ i j = g₁ j i) (hSym₂ : ∀ i j, g₂ i j = g₂ j i)
    (h_null₁ : ∀ v : Fin 4 → ℝ,
      minkQuadGen v = 0 → (∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0))
    (h_null₂ : ∀ v : Fin 4 → ℝ,
      minkQuadGen v = 0 → (∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0))
    (hg₁ : g₁ 0 0 ≠ 0)
    (P_proc : SymmetricProcess) (ρ V Ω : ℝ)
    (hρ : 0 < ρ) (hV : 0 < V) (hΩ : 0 < Ω) (hΩ4 : Ω ^ 4 = 1)
    (L_met : LorentzianMetric 2) (c_rg α_rg : ℝ) (hc_rg : c_rg ≠ 0)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (G_N M J : ℝ) (hG_pos : 0 < G_N) (hM : 0 < M) (hsub : kerrSubextremal M J) :
    (traceReversal 4 (traceReversal 4 h4) = h4 ∧
     Matrix.trace (traceReversal 4 h4) = (1 - (4 : ℝ) / 2) * Matrix.trace h4 ∧
     R_metric (mdAdd md₁ md₂) a b c d = R_metric md₁ a b c d + R_metric md₂ a b c d ∧
     divRic (riemannFromMetric md₁) b - dScalar (riemannFromMetric md₁) b / 2 = 0) ∧
    (d_lov = -c_lov / 2 ∧
     naturalOf cd c_lov (-c_lov / 2) e_lov = c_lov • einsteinOf cd + e_lov • cd.g_metric ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
       (BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))) ^ 2 ∧
     4 * gbStandard (riemannFromMetric md₁) =
       4 * kretschner (riemannFromMetric md₁) -
         16 * ricciNorm (riemannFromMetric md₁) +
         4 * scalarR (riemannFromMetric md₁) ^ 2) ∧
    (symmetricComponents 4 = 10 ∧
     gravitonPolarizations 3 = 2 ∧
     nullFocusing (conformalMD 4 φ_conf) k_null =
       φ_conf * nullFocusing (conformalMD 4 1) k_null ∧
     0 < focusing grFocusingHypothesis h_pos ∧
     focusing grFocusingHypothesis (h_pos + (-h_pos)) = 0) ∧
    (((∀ t x : ℝ, ∀ i j : Fin 2,
          -(-(k₀ ^ 2) * planeWaveTensor k₀ k₁ ε_pol t x i j) +
            (-(k₁ ^ 2) * planeWaveTensor k₀ k₁ ε_pol t x i j) = 0) ∧
       ttModeCount 4 = 2 ∧ ttModeCount 3 = 0 ∧ ttModeCount 2 = 0) ∧
     ((∃ mu : ℝ, ∀ i j : Fin 4, g₂ i j = mu * g₁ i j) ∧
       0 < lambdaSq ρ V ∧
       P_proc.variance ρ V = ρ * V ∧
       P_proc.variance ρ V / (ρ * V) ^ 2 = lambdaSq ρ V ∧
       Ω = 1) ∧
     ((∀ b_idx : Fin 4, divRic L_met.riemann b_idx - dScalar L_met.riemann b_idx / 2 = 0) ∧
       ((∀ ℓ > 0, ∀ r > 0,
          renormOp_d 3 ℓ (powerLaw c_rg α_rg) r = powerLaw c_rg α_rg r) ↔ α_rg = 2) ∧
       Module.finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) = 16) ∧
     (stressEnergyTrace sc₃ conn₃ = 0 ∧
       causalCoefficient = 1 / 2 ∧
       discretenessLength causalCoefficient G_N ^ 2 = 8 * Real.pi * G_N ∧
       0 ≤ kretschnerAction md₁ ∧
       weylTensor4D (conformalPartMetricDerivs4D md₁) a b c d = 0 ∧
       M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) ∧
       IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M ∧
       schwarzschildKretschmann M (schwarzschildRadius M) *
         (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2)) :=
  ⟨⟨traceReversal_involutive_4d h4,
    trace_of_traceReversal 4 h4,
    LinearizedFieldEqs.R_metric_add md₁ md₂ a b c d,
    einstein_div_free (riemannFromMetric md₁) b⟩,
   ⟨lovelock_bianchi_constraint c_lov d_lov h_div h_nondeg,
    lovelock_decomposition cd c_lov e_lov,
    cosmological_constant_N_summary.2.1,
    Nsub_is_BHArea_squared,
    gb_scalar_identity (riemannFromMetric md₁)⟩,
   ⟨symmetric_4d,
    graviton_2_polarizations,
    conformal_focusing_proportional φ_conf k_null,
    gr_signed_focusing.1 h_pos hq_pos,
    gr_signed_focusing.2.2.2 h_pos⟩,
   curved_4d_gravitational_plane_waves_null_cone_hauptvermutung_master_synthesis
     k₀ k₁ hnull ε_pol g₁ g₂ hSym₁ hSym₂ h_null₁ h_null₂ hg₁
     P_proc ρ V Ω hρ hV hΩ hΩ4 L_met c_rg α_rg hc_rg sc₃ conn₃
     G_N M J hG_pos hM hsub md₁ a b c d⟩

#print axioms bianchi_trace_reversal_and_linearized_superposition_package
#print axioms lovelock_endpoint_and_null_cone_1plus1_package
#print axioms cosmological_constant_N_and_gauss_bonnet_expansion_package
#print axioms graviton_polarizations_and_raychaudhuri_focusing_package
#print axioms curved_4d_bianchi_linearized_einstein_lovelock_focusing_master_synthesis

end

end UnifiedTheory.Audit.KFCausalCurved4DBianchiLinearizedEinsteinLovelockWeylAntiGravityBridge
