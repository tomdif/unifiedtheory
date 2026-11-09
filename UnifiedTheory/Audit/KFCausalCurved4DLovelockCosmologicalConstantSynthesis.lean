import UnifiedTheory.LayerA.LovelockComplete
import UnifiedTheory.LayerA.CosmologicalConstant
import UnifiedTheory.Audit.KFCausalCurved4DDifferentialBianchiIdentity
import UnifiedTheory.Audit.KFCausalCurved4DSMEinsteinWeylYangMillsMasterSynthesis

/-! 4D Lovelock Completeness, Sorkin Cosmological Constant (`Λ = 1 / √(ρV)`),
and Curved 4D Einstein-Lovelock-Yang-Mills Curvature Synthesis:
1. Connects `LayerA.LovelockComplete` (`leviCivita`, `genKronecker`,
   `epsilon_product_eq_genKronecker`, `orientation_parity`, `gaussBonnet_vanishes_4d`,
   `higher_lovelock_rank_exceeds_4d`, `complete_lovelock_4d`) and
   `LayerA.CosmologicalConstant` (`sorkinLambda`, `sorkin_scaling`,
   `lambda_squared_times_N`, `self_consistency`, `fluctuation_scales_as_lambda`,
   `refined_prediction`) to the 4D Lorentzian linearized curvature framework.
2. Defines the 4D Lovelock-Einstein tensor
   `einsteinLovelock4D md a Λ μ ν = a * einstein md sign μ ν + Λ * lorentzInvMetric4D μ ν`
   and its Sorkin specialization `einsteinSorkin4D md ρ V = einsteinLovelock4D md 1 (sorkinLambda ρ V)`,
   proving symmetry, off-diagonal shear/flux reduction, linearity, and the exact
   4D Lorentzian trace formula `Tr_η(a G + Λ η) = -a R + 4 Λ`.
3. Proves that on any 4D Einstein-Lovelock-Yang-Mills background
   `einsteinLovelock4D md 1 Λ μ ν = κ * ymStressEnergy4D sc conn μ ν`, the 4D
   conformal tracelessness of `ymStressEnergy4D` forces:
   - `scalar md sign = 4 * Λ`,
   - for `Λ = sorkinLambda ρ V` (`ρ > 0, V > 0`), `0 < scalar md sign` and
     `(scalar md sign) ^ 2 * (ρ * V) = 16`,
   - `ricci md sign μ ν = κ * ymStressEnergy4D sc conn μ ν + Λ * lorentzInvMetric4D μ ν`,
   - the exact 20-component de Sitter + Yang-Mills + Weyl Riemann decomposition
     `R_{abcd} = C_{abcd}(h^{TT}) + (κ/2)(η ⋏ T^{YM})_{abcd} + (Λ/3)(η_{ac} η_{bd} - η_{ad} η_{bc})`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DLovelockCosmologicalConstantSynthesis
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open UnifiedTheory.LayerA.GaussBonnet4D (genKronecker genKronecker_vanishes
  gaussBonnetTensor gaussBonnet_vanishes_4d higher_lovelock_rank_exceeds_4d)
open UnifiedTheory.LayerA.LovelockComplete (leviCivita leviCivita_zero_of_repeat
  epsilon_product_eq_genKronecker orientation_parity complete_lovelock_4d)
open UnifiedTheory.LayerA.CosmologicalConstant (sorkinLambda sorkinLambda_pos
  sorkin_scaling lambda_squared_times_N lambda_small_for_large_N
  cosmological_constant_prediction causalPastVolume self_consistency
  relativeLambdaFluctuation fluctuation_scales_as_lambda lambda_fluctuates
  refined_prediction)
open UnifiedTheory.LayerA.GaugeConnection (StructureConstants ConnectionData)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic dScalar dEinstein
  ricci_symmetric)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D minkMetric4D box4D
  fullScalarCurvature4D fullEinsteinTensor4D
  fullScalarCurvature4D_master_formula fullEinsteinTensor4D_master_formula)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  einstein_zero einstein_add tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (ricciCurvaturePart4D
  scalarCurvaturePart4D ricciScalarRiemannPart4D weylTensor4D
  riemann_eq_weyl_add_ricciScalar weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DGeneralProbeCurvatureExtraction (lorentzianTensorTrace4D
  lorentzianEinsteinTrace4D lorentzianEinsteinTrace4D_eq_neg_scalar)
open KFCausalCurved4DTidalWeylProbeExtraction (basisVec4D weylTidalProbe)
open KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
  (conformalPlusGravitationalWaveMetricDerivs4D
   conformalPlusGravitationalWave_ricci_scalar_einstein
   conformalPlusGravitationalWave_joint_reconstruction)
open KFCausalCurved4DDifferentialBianchiIdentity (dR_metric_second_bianchi
  dEinstein_lorentzian_divergence_zero)
open KFCausalCurved4DYangMillsStressEnergyCoupling (lorentzInvMetric4D
  lorentzInvMetric4D_eq_minkMetric4D lorentzInvMetric4D_symm
  lorentzInvMetric4D_diag lorentzInvMetric4D_offDiag
  lorentzInvMetric4D_lorentzian_trace ymStressEnergy4D
  ymStressEnergy4D_lorentzian_trace_zero)

variable {g_dim : ℕ}

/-! ### 1. 4D Lovelock Completeness & Gauss-Bonnet Vanishing Bridge (`LayerA.LovelockComplete`) -/

/-- The Levi-Civita symbol `leviCivita a` vanishes whenever two indices coincide (`i ≠ j`, `a i = a j`). -/
theorem leviCivita_zero_of_repeated_index {n : ℕ} (a : Fin n → Fin n)
    (i j : Fin n) (hij : i ≠ j) (haij : a i = a j) :
    leviCivita a = 0 :=
  leviCivita_zero_of_repeat a i j hij haij

/-- Fundamental Levi-Civita product identity: `ε(a) * ε(b) = genKronecker a b`. -/
theorem leviCivita_product_eq_genKronecker {n : ℕ} (a b : Fin n → Fin n) :
    leviCivita a * leviCivita b = genKronecker a b :=
  epsilon_product_eq_genKronecker a b

/-- Orientation parity for Levi-Civita tensor contractions: `(-1)^k = 1 ↔ Even k`. -/
theorem orientation_parity_even (k : ℕ) :
    (-1 : ℝ) ^ k = 1 ↔ Even k :=
  orientation_parity k

/-- In spacetime dimension `4`, any generalized Kronecker delta of rank `k > 4`
vanishes identically by pigeonhole. -/
theorem genKronecker_vanishes_above_dim4 {k : ℕ} (hk : 4 < k)
    (a b : Fin k → Fin 4) :
    genKronecker a b = 0 :=
  genKronecker_vanishes hk a b

/-- The quadratic Gauss-Bonnet (Lanczos-Lovelock) field-equation tensor `gaussBonnetTensor`
vanishes identically in dimension `4`. -/
theorem gaussBonnetTensor_vanishes_4D
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    gaussBonnetTensor R a b = 0 :=
  gaussBonnet_vanishes_4d R a b

/-- Every Lovelock curvature order `p ≥ 2` requires a generalized Kronecker delta of
rank `2 * p + 1 > 4`, and therefore vanishes in 4D spacetime. -/
theorem higher_lovelock_rank_exceeds_4D (p : ℕ) (hp : 2 ≤ p) :
    4 < 2 * p + 1 :=
  higher_lovelock_rank_exceeds_4d p hp

/-- Complete 4D Lovelock classification bridge bundling single-Riemann contractions,
4D Gauss-Bonnet vanishing, higher-order Lovelock exclusion, `ε · ε = δ`, and
orientation parity. -/
theorem lovelock_4D_complete_bridge :
    (∀ (rd : RiemannData 4),
      (∀ c d, ∑ a : Fin 4, rd.R a a c d = 0) ∧
      (∀ a b, ∑ c : Fin 4, rd.R a b c c = 0) ∧
      (∀ a d, ∑ b : Fin 4, rd.R a b d b = ∑ b, rd.R b a b d)) ∧
    (∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∀ a b : Fin 4, gaussBonnetTensor R a b = 0) ∧
    (∀ p : ℕ, 2 ≤ p → 4 < 2 * p + 1) ∧
    (∀ a b : Fin 4 → Fin 4, leviCivita a * leviCivita b = genKronecker a b) ∧
    (∀ k : ℕ, (-1 : ℝ) ^ k = 1 ↔ Even k) :=
  complete_lovelock_4d

/-! ### 2. Sorkin Cosmological Constant `Λ = 1 / √(ρV)` Bridge (`LayerA.CosmologicalConstant`) -/

/-- Strict positivity of the Sorkin cosmological constant `sorkinLambda ρ V = 1 / √(ρ * V)`
for positive sprinkling density `ρ > 0` and causal 4-volume `V > 0`. -/
theorem sorkinLambda_strict_pos (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    0 < sorkinLambda ρ V :=
  sorkinLambda_pos ρ V hρ hV

/-- Sorkin inverse-number scaling law: `sorkinLambda ρ V ^ 2 = 1 / (ρ * V)`. -/
theorem sorkinLambda_sq_eq_inv_N (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    sorkinLambda ρ V ^ 2 = 1 / (ρ * V) :=
  sorkin_scaling ρ V hρ hV

/-- Fundamental Sorkin Poisson-counting identity: `sorkinLambda ρ V ^ 2 * (ρ * V) = 1`. -/
theorem sorkinLambda_sq_mul_N_eq_one (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    sorkinLambda ρ V ^ 2 * (ρ * V) = 1 :=
  lambda_squared_times_N ρ V hρ hV

/-- Large-volume suppression of `sorkinLambda`: if `1 / ε ^ 2 < ρ * V`, then
`sorkinLambda ρ V ^ 2 < ε ^ 2`. -/
theorem sorkinLambda_small_for_large_N (ρ V ε : ℝ)
    (hρ : 0 < ρ) (hV : 0 < V) (hε : 0 < ε) (hN : 1 / ε ^ 2 < ρ * V) :
    sorkinLambda ρ V ^ 2 < ε ^ 2 :=
  lambda_small_for_large_N ρ V ε hρ hV hε hN

/-- De Sitter causal-past volume self-consistency: if `V = c_vol / Λ ^ 2` and
`Λ ^ 2 = 1 / (ρ * V)`, then `ρ * c_vol = 1`. -/
theorem sorkin_self_consistency_relation (ρ c_vol Λ : ℝ)
    (hρ : 0 < ρ) (hΛ : 0 < Λ) (hc : 0 < c_vol)
    (h_sorkin : Λ ^ 2 = 1 / (ρ * causalPastVolume c_vol Λ)) :
    ρ * c_vol = 1 :=
  self_consistency ρ c_vol Λ hρ hΛ hc h_sorkin

/-- Relative Poisson fluctuation of `sorkinLambda`:
`relativeLambdaFluctuation (ρ * V) = sorkinLambda ρ V / 2 > 0`. -/
theorem sorkin_relative_fluctuation_eq_half_lambda (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    relativeLambdaFluctuation (ρ * V) = sorkinLambda ρ V / 2 ∧
    0 < relativeLambdaFluctuation (ρ * V) :=
  lambda_fluctuates ρ V hρ hV

/-- Bundled Sorkin refined cosmological constant prediction. -/
theorem sorkin_refined_cosmological_prediction :
    (∀ ρ V : ℝ, 0 < ρ → 0 < V → sorkinLambda ρ V ^ 2 * (ρ * V) = 1) ∧
    (∀ ρ c Λ : ℝ, 0 < ρ → 0 < Λ → 0 < c →
      Λ ^ 2 = 1 / (ρ * causalPastVolume c Λ) → ρ * c = 1) ∧
    (∀ ρ V : ℝ, 0 < ρ → 0 < V →
      relativeLambdaFluctuation (ρ * V) = sorkinLambda ρ V / 2) :=
  refined_prediction

/-! ### 3. 4D Lovelock-Einstein Tensor `einsteinLovelock4D` and Sorkin Specialization `einsteinSorkin4D` -/

/-- **4D Linearized Lovelock-Einstein Tensor**:
`E_{μν}(md; a, Λ) = a * G_{μν}(md) + Λ * η_{μν}`. -/
def einsteinLovelock4D (md : MetricDerivs 4) (a Λ : ℝ) (μ ν : Fin 4) : ℝ :=
  a * einstein md sign μ ν + Λ * lorentzInvMetric4D μ ν

/-- **4D Sorkin-Dressed Linearized Einstein Tensor**:
`G_{μν}(md) + sorkinLambda ρ V * η_{μν}` (`a = 1`, `Λ = 1 / √(ρV)`). -/
def einsteinSorkin4D (md : MetricDerivs 4) (ρ V : ℝ) (μ ν : Fin 4) : ℝ :=
  einsteinLovelock4D md 1 (sorkinLambda ρ V) μ ν

/-- Symmetry of the 4D Lovelock-Einstein tensor:
`einsteinLovelock4D md a Λ μ ν = einsteinLovelock4D md a Λ ν μ`. -/
theorem einsteinLovelock4D_symm (md : MetricDerivs 4) (a Λ : ℝ) (μ ν : Fin 4) :
    einsteinLovelock4D md a Λ μ ν = einsteinLovelock4D md a Λ ν μ := by
  have hein_symm : einstein md sign μ ν = einstein md sign ν μ := by
    unfold einstein
    rw [ricci_symmetric md sign μ ν]
    by_cases h : μ = ν
    · subst ν; rfl
    · simp only [if_neg h, if_neg (Ne.symm h)]
  unfold einsteinLovelock4D
  rw [hein_symm, lorentzInvMetric4D_symm μ ν]

/-- Symmetry of the 4D Sorkin-Einstein tensor `einsteinSorkin4D`. -/
theorem einsteinSorkin4D_symm (md : MetricDerivs 4) (ρ V : ℝ) (μ ν : Fin 4) :
    einsteinSorkin4D md ρ V μ ν = einsteinSorkin4D md ρ V ν μ :=
  einsteinLovelock4D_symm md 1 (sorkinLambda ρ V) μ ν

/-- On all 6 off-diagonal shear and momentum-flux channels (`μ ≠ ν`), the
cosmological constant term vanishes identically (`lorentzInvMetric4D μ ν = 0`),
so `einsteinLovelock4D md a Λ μ ν = a * einstein md sign μ ν`. -/
theorem einsteinLovelock4D_offDiag (md : MetricDerivs 4) (a Λ : ℝ)
    (μ ν : Fin 4) (hμν : μ ≠ ν) :
    einsteinLovelock4D md a Λ μ ν = a * einstein md sign μ ν := by
  unfold einsteinLovelock4D
  rw [lorentzInvMetric4D_offDiag μ ν hμν]
  ring

/-- Diagonal formula for `einsteinLovelock4D`:
`einsteinLovelock4D md a Λ μ μ = a * einstein md sign μ μ + Λ * sign μ`. -/
theorem einsteinLovelock4D_diag (md : MetricDerivs 4) (a Λ : ℝ) (μ : Fin 4) :
    einsteinLovelock4D md a Λ μ μ = a * einstein md sign μ μ + Λ * sign μ := by
  unfold einsteinLovelock4D
  rw [lorentzInvMetric4D_diag μ]

/-- For `a = 1` and `Λ = 0`, `einsteinLovelock4D md 1 0` reduces to `einstein md sign`. -/
theorem einsteinLovelock4D_zero_lambda (md : MetricDerivs 4) (μ ν : Fin 4) :
    einsteinLovelock4D md 1 0 μ ν = einstein md sign μ ν := by
  unfold einsteinLovelock4D
  ring

/-- On `zeroMetricDerivs 4`, `einsteinLovelock4D` reduces to the pure cosmological
term `Λ * lorentzInvMetric4D μ ν`. -/
theorem einsteinLovelock4D_zeroMetricDerivs (a Λ : ℝ) (μ ν : Fin 4) :
    einsteinLovelock4D (zeroMetricDerivs 4) a Λ μ ν = Λ * lorentzInvMetric4D μ ν := by
  unfold einsteinLovelock4D
  rw [einstein_zero]
  ring

/-- Joint additivity of `einsteinLovelock4D` in the metric perturbation jet `md`
and cosmological constant `Λ`. -/
theorem einsteinLovelock4D_add_md (md₁ md₂ : MetricDerivs 4)
    (a Λ₁ Λ₂ : ℝ) (μ ν : Fin 4) :
    einsteinLovelock4D (addMetricDerivs md₁ md₂) a (Λ₁ + Λ₂) μ ν =
      einsteinLovelock4D md₁ a Λ₁ μ ν + einsteinLovelock4D md₂ a Λ₂ μ ν := by
  unfold einsteinLovelock4D
  rw [einstein_add]
  ring

/-- **Exact 4D Lorentzian Trace of `einsteinLovelock4D`**:
Because `Tr_η(G) = -R` and `Tr_η(η) = 4` in 4D Lorentzian signature,
`∑ μ : Fin 4, sign μ * einsteinLovelock4D md a Λ μ μ = -a * scalar md sign + 4 * Λ`. -/
theorem einsteinLovelock4D_lorentzian_trace (md : MetricDerivs 4) (a Λ : ℝ) :
    (∑ μ : Fin 4, sign μ * einsteinLovelock4D md a Λ μ μ) =
      -a * scalar md sign + 4 * Λ := by
  unfold einsteinLovelock4D
  have hterm : ∀ μ : Fin 4,
      sign μ * (a * einstein md sign μ μ + Λ * lorentzInvMetric4D μ μ) =
      a * (sign μ * einstein md sign μ μ) + Λ * (sign μ * lorentzInvMetric4D μ μ) := by
    intro μ; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hG : (∑ μ : Fin 4, sign μ * einstein md sign μ μ) = -scalar md sign :=
    (lorentzianEinsteinTrace4D_eq_neg_scalar md).1
  rw [hG, lorentzInvMetric4D_lorentzian_trace]
  ring

/-- Exact 4D Lorentzian trace of the Sorkin-Einstein tensor `einsteinSorkin4D`:
`∑ μ : Fin 4, sign μ * einsteinSorkin4D md ρ V μ μ = -scalar md sign + 4 * sorkinLambda ρ V`. -/
theorem einsteinSorkin4D_lorentzian_trace (md : MetricDerivs 4) (ρ V : ℝ) :
    (∑ μ : Fin 4, sign μ * einsteinSorkin4D md ρ V μ μ) =
      -scalar md sign + 4 * sorkinLambda ρ V := by
  unfold einsteinSorkin4D
  rw [einsteinLovelock4D_lorentzian_trace]
  ring

/-! ### 4. Coupled 4D Einstein-Lovelock-Yang-Mills & Einstein-Sorkin-Yang-Mills Field Equations -/

/-- Predicate that a 4D metric perturbation `md : MetricDerivs 4` satisfies the
cosmological 4D Einstein-Yang-Mills field equation
`G_{μν}(md) + Λ η_{μν} = κ T^{YM}_{μν}(sc, conn)`. -/
def SatisfiesEinsteinLovelockYangMills4D (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim) : Prop :=
  ∀ μ ν : Fin 4, einsteinLovelock4D md 1 Λ μ ν = κ * ymStressEnergy4D sc conn μ ν

/-- Predicate that `md : MetricDerivs 4` satisfies the Sorkin-cosmological 4D
Einstein-Yang-Mills field equation `G_{μν}(md) + sorkinLambda ρ V * η_{μν} = κ T^{YM}_{μν}`. -/
def SatisfiesEinsteinSorkinYangMills4D (md : MetricDerivs 4) (ρ V κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim) : Prop :=
  SatisfiesEinsteinLovelockYangMills4D md (sorkinLambda ρ V) κ sc conn

/-- Because the 4D Yang-Mills stress-energy tensor is conformally traceless
(`∑ μ, sign μ * T^{YM}_{μμ} = 0`), the 4D Lorentzian trace of `einsteinLovelock4D md 1 Λ`
vanishes identically on any solution to `SatisfiesEinsteinLovelockYangMills4D`. -/
theorem einsteinLovelockYangMills4D_trace_zero (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn) :
    (∑ μ : Fin 4, sign μ * einsteinLovelock4D md 1 Λ μ μ) = 0 := by
  have hsum : (∑ μ : Fin 4, sign μ * einsteinLovelock4D md 1 Λ μ μ) =
      κ * (∑ μ : Fin 4, sign μ * ymStressEnergy4D sc conn μ μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    rw [hELYM μ μ]
    ring
  rw [hsum, ymStressEnergy4D_lorentzian_trace_zero, mul_zero]

/-- **Cosmological Scalar Curvature Identity (`R = 4 Λ`)**: on any 4D metric
perturbation `md` coupled to a 4D Yang-Mills field with cosmological constant `Λ`,
the 4D scalar curvature is independent of the Yang-Mills field and equals `4 * Λ`
(`scalar md sign = 4 * Λ`, `lorentzianEinsteinTrace4D md = -4 * Λ`). -/
theorem einsteinLovelockYangMills4D_scalar_eq_four_lambda (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn) :
    scalar md sign = 4 * Λ ∧
    lorentzianEinsteinTrace4D md = -4 * Λ := by
  have htr0 := einsteinLovelockYangMills4D_trace_zero md Λ κ sc conn hELYM
  rw [einsteinLovelock4D_lorentzian_trace] at htr0
  have hR : scalar md sign = 4 * Λ := by linarith
  have hG : lorentzianEinsteinTrace4D md = -4 * Λ := by
    rw [(lorentzianEinsteinTrace4D_eq_neg_scalar md).1, hR]
    ring
  exact ⟨hR, hG⟩

/-- **Strict Positivity and Poisson-Volume Scaling of 4D Scalar Curvature on
Einstein-Sorkin-Yang-Mills Backgrounds**: for any `ρ > 0` and `V > 0`, any
solution to `SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc conn` satisfies:
1. `scalar md sign = 4 * sorkinLambda ρ V`,
2. `0 < scalar md sign` (strictly positive de Sitter scalar curvature!),
3. `(scalar md sign) ^ 2 = 16 / (ρ * V)`,
4. `(scalar md sign) ^ 2 * (ρ * V) = 16`. -/
theorem einsteinSorkinYangMills4D_scalar_pos_and_scaling (md : MetricDerivs 4)
    (ρ V κ : ℝ) (hρ : 0 < ρ) (hV : 0 < V)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hESYM : SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc conn) :
    scalar md sign = 4 * sorkinLambda ρ V ∧
    0 < scalar md sign ∧
    (scalar md sign) ^ 2 = 16 / (ρ * V) ∧
    (scalar md sign) ^ 2 * (ρ * V) = 16 := by
  have hR := (einsteinLovelockYangMills4D_scalar_eq_four_lambda
    md (sorkinLambda ρ V) κ sc conn hESYM).1
  have hpos : 0 < scalar md sign := by
    rw [hR]
    exact mul_pos (by norm_num) (sorkinLambda_pos ρ V hρ hV)
  have hsq : (scalar md sign) ^ 2 = 16 / (ρ * V) := by
    rw [hR]
    calc (4 * sorkinLambda ρ V) ^ 2
        = 16 * sorkinLambda ρ V ^ 2 := by ring
      _ = 16 * (1 / (ρ * V)) := by rw [sorkin_scaling ρ V hρ hV]
      _ = 16 / (ρ * V) := by ring
  have hN : (scalar md sign) ^ 2 * (ρ * V) = 16 := by
    rw [hR]
    calc (4 * sorkinLambda ρ V) ^ 2 * (ρ * V)
        = 16 * (sorkinLambda ρ V ^ 2 * (ρ * V)) := by ring
      _ = 16 * 1 := by rw [lambda_squared_times_N ρ V hρ hV]
      _ = 16 := by ring
  exact ⟨hR, hpos, hsq, hN⟩

/-- **Exact 4D Ricci Tensor Formula on Einstein-Lovelock-Yang-Mills Backgrounds**:
When `G_{μν} + Λ η_{μν} = κ T^{YM}_{μν}`, substituting `R = 4 Λ` into
`G_{μν} = R_{μν} - (R / 2) η_{μν}` yields
`ricci md sign μ ν = κ * ymStressEnergy4D sc conn μ ν + Λ * lorentzInvMetric4D μ ν`. -/
theorem einsteinLovelockYangMills4D_ricci_formula (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn) (μ ν : Fin 4) :
    einstein md sign μ ν =
      κ * ymStressEnergy4D sc conn μ ν - Λ * lorentzInvMetric4D μ ν ∧
    ricci md sign μ ν =
      κ * ymStressEnergy4D sc conn μ ν + Λ * lorentzInvMetric4D μ ν := by
  have hEYM_μν := hELYM μ ν
  unfold einsteinLovelock4D at hEYM_μν
  have hG : einstein md sign μ ν =
      κ * ymStressEnergy4D sc conn μ ν - Λ * lorentzInvMetric4D μ ν := by
    linarith
  have hR := (einsteinLovelockYangMills4D_scalar_eq_four_lambda md Λ κ sc conn hELYM).1
  have hein_def : einstein md sign μ ν =
      ricci md sign μ ν - scalar md sign / 2 * lorentzInvMetric4D μ ν := rfl
  rw [hR] at hein_def
  have hRic : ricci md sign μ ν =
      κ * ymStressEnergy4D sc conn μ ν + Λ * lorentzInvMetric4D μ ν := by
    linarith
  exact ⟨hG, hRic⟩

/-- Exact formula for `scalarCurvaturePart4D` on any solution to
`SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn`:
`scalarCurvaturePart4D md a b c d = -(2 / 3) * Λ * (η_{ac} η_{bd} - η_{ad} η_{bc})`. -/
theorem einsteinLovelockYangMills4D_scalarCurvaturePart4D_formula
    (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn)
    (a b c d : Fin 4) :
    scalarCurvaturePart4D md a b c d =
      -(2 / 3 : ℝ) * Λ *
        (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c) := by
  unfold scalarCurvaturePart4D
  rw [(einsteinLovelockYangMills4D_scalar_eq_four_lambda md Λ κ sc conn hELYM).1]
  ring

/-- **Exact 20-Component 4D Riemann Decomposition on an Einstein-Lovelock-Yang-Mills
Background**: for any `md : MetricDerivs 4` satisfying
`SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn`, its Riemann tensor splits into:
1. the trace-free Weyl tensor `weylTensor4D (tracelessPartMetricDerivs4D md) a b c d`,
2. the Yang-Mills Kulkarni-Nomizu curvature `(κ / 2) * (η ⋏ T^{YM})_{abcd}`, and
3. the constant-curvature de Sitter term `(1 / 3) * Λ * (η_{ac} η_{bd} - η_{ad} η_{bc})`. -/
theorem einsteinLovelockYangMills4D_riemann_weyl_decomposition
    (md : MetricDerivs 4) (Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn)
    (a b c d : Fin 4) :
    R_metric md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d +
        (κ / 2) *
          (minkMetric4D a c * ymStressEnergy4D sc conn b d -
            minkMetric4D a d * ymStressEnergy4D sc conn b c -
            minkMetric4D b c * ymStressEnergy4D sc conn a d +
            minkMetric4D b d * ymStressEnergy4D sc conn a c) +
        (1 / 3 : ℝ) * Λ *
          (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c) := by
  rw [(riemann_eq_weyl_add_ricciScalar md a b c d).2,
    weylTensor4D_eq_tracelessPart md a b c d,
    einsteinLovelockYangMills4D_scalarCurvaturePart4D_formula md Λ κ sc conn hELYM a b c d]
  unfold ricciCurvaturePart4D
  rw [(einsteinLovelockYangMills4D_ricci_formula md Λ κ sc conn hELYM b d).2,
    (einsteinLovelockYangMills4D_ricci_formula md Λ κ sc conn hELYM b c).2,
    (einsteinLovelockYangMills4D_ricci_formula md Λ κ sc conn hELYM a d).2,
    (einsteinLovelockYangMills4D_ricci_formula md Λ κ sc conn hELYM a c).2]
  simp only [lorentzInvMetric4D_eq_minkMetric4D]
  ring

/-- Solution structure of `SatisfiesEinsteinLovelockYangMills4D` on the combined
conformal-plus-gravitational-wave family `conformalPlusGravitationalWaveMetricDerivs4D H K A B`:
`box4D H = -(2 / 3) * Λ`, `H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν - (1 / 6) * Λ * lorentzInvMetric4D μ ν`,
and both gravitational-wave polarizations `(A, B)` propagate freely in `weylTidalProbe`. -/
theorem einsteinLovelockYangMills4D_conformalPlusGravitationalWave_solution
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B Λ κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hELYM : SatisfiesEinsteinLovelockYangMills4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) Λ κ sc conn) :
    let md := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    scalar md sign = 4 * Λ ∧
    fullScalarCurvature4D H = 4 * Λ ∧
    box4D H = -(2 / 3 : ℝ) * Λ ∧
    (∀ μ ν : Fin 4,
      H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν -
        (1 / 6 : ℝ) * Λ * lorentzInvMetric4D μ ν) ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 1) md = A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 2) md = B := by
  intro md
  have hR := (einsteinLovelockYangMills4D_scalar_eq_four_lambda md Λ κ sc conn hELYM).1
  have hcomb := conformalPlusGravitationalWave_ricci_scalar_einstein H K A B
  have hFH : fullScalarCurvature4D H = 4 * Λ := by
    rw [← hcomb.2.1, hR]
  have hbox : box4D H = -(2 / 3 : ℝ) * Λ := by
    have h1 := (fullScalarCurvature4D_master_formula H).1
    linarith
  have hH_eq : ∀ μ ν : Fin 4,
      H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν -
        (1 / 6 : ℝ) * Λ * lorentzInvMetric4D μ ν := by
    intro μ ν
    have hG_formula : einstein md sign μ ν =
        -2 * H μ ν - (4 / 3 : ℝ) * Λ * lorentzInvMetric4D μ ν := by
      rw [hcomb.2.2 μ ν, fullEinsteinTensor4D_master_formula H hH μ ν, hbox,
        ← lorentzInvMetric4D_eq_minkMetric4D]
      ring
    have hG_EYM := (einsteinLovelockYangMills4D_ricci_formula md Λ κ sc conn hELYM μ ν).1
    linarith
  have hrec := conformalPlusGravitationalWave_joint_reconstruction H hH K A B
  exact ⟨hR, hFH, hbox, hH_eq, hrec.2.1, hrec.2.2.2.1⟩

/-- **Master 4D Lovelock-Sorkin-Yang-Mills Curvature Synthesis**:
Unites 4D Lovelock uniqueness (`gaussBonnetTensor = 0`, `complete_lovelock_4d`),
Sorkin cosmological constant scaling (`Λ = 1 / √(ρV) > 0`, `Λ^2 (ρV) = 1`,
`δΛ/Λ = Λ/2`), and the exact 4D curvature decomposition on any coupled
Einstein-Sorkin-Yang-Mills background (`R = 4 Λ > 0`, `R^2 (ρV) = 16`,
`Ric = κ T^{YM} + Λ η`, and `R_{abcd} = C(h^{TT}) + (κ/2)(η ⋏ T^{YM}) + (Λ/3)(η ⋏ η)`). -/
theorem lovelock_sorkin_yang_mills_4D_master_synthesis
    (md : MetricDerivs 4) (ρ V κ : ℝ) (hρ : 0 < ρ) (hV : 0 < V)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hESYM : SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc conn) :
    -- (1) 4D Gauss-Bonnet vanishing & Levi-Civita product identity
    ((∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ, ∀ a b : Fin 4, gaussBonnetTensor R a b = 0) ∧
      (∀ a b : Fin 4 → Fin 4, leviCivita a * leviCivita b = genKronecker a b)) ∧
    -- (2) Sorkin cosmological constant scaling & fluctuation
    (0 < sorkinLambda ρ V ∧
      sorkinLambda ρ V ^ 2 * (ρ * V) = 1 ∧
      relativeLambdaFluctuation (ρ * V) = sorkinLambda ρ V / 2) ∧
    -- (3) Positive de Sitter scalar curvature & Poisson scaling R^2 * N = 16
    (scalar md sign = 4 * sorkinLambda ρ V ∧
      0 < scalar md sign ∧
      (scalar md sign) ^ 2 * (ρ * V) = 16) ∧
    -- (4) Exact Ricci tensor & 20-component Riemann decomposition
    ((∀ μ ν : Fin 4,
        ricci md sign μ ν =
          κ * ymStressEnergy4D sc conn μ ν +
            sorkinLambda ρ V * lorentzInvMetric4D μ ν) ∧
      (∀ a b c d : Fin 4,
        R_metric md a b c d =
          weylTensor4D (tracelessPartMetricDerivs4D md) a b c d +
            (κ / 2) *
              (minkMetric4D a c * ymStressEnergy4D sc conn b d -
                minkMetric4D a d * ymStressEnergy4D sc conn b c -
                minkMetric4D b c * ymStressEnergy4D sc conn a d +
                minkMetric4D b d * ymStressEnergy4D sc conn a c) +
            (1 / 3 : ℝ) * sorkinLambda ρ V *
              (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c))) ∧
    -- (5) Differential Bianchi conservation
    ((∀ e a b c d : Fin 4,
        dR_metric md e a b c d + dR_metric md a b e c d + dR_metric md b e a c d = 0) ∧
      (∀ b : Fin 4,
        (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e b e) = 0)) := by
  have hsc := einsteinSorkinYangMills4D_scalar_pos_and_scaling md ρ V κ hρ hV sc conn hESYM
  refine ⟨⟨gaussBonnet_vanishes_4d, fun a b => epsilon_product_eq_genKronecker a b⟩,
    ⟨sorkinLambda_pos ρ V hρ hV, lambda_squared_times_N ρ V hρ hV,
      fluctuation_scales_as_lambda ρ V hρ hV⟩,
    ⟨hsc.1, hsc.2.1, hsc.2.2.2⟩,
    ⟨fun μ ν =>
        (einsteinLovelockYangMills4D_ricci_formula md (sorkinLambda ρ V) κ sc conn hESYM μ ν).2,
      fun a b c d =>
        einsteinLovelockYangMills4D_riemann_weyl_decomposition
          md (sorkinLambda ρ V) κ sc conn hESYM a b c d⟩,
    ⟨fun e a b c d => dR_metric_second_bianchi md e a b c d,
      fun b => (dEinstein_lorentzian_divergence_zero md b).1⟩⟩

#print axioms leviCivita_zero_of_repeated_index
#print axioms leviCivita_product_eq_genKronecker
#print axioms orientation_parity_even
#print axioms genKronecker_vanishes_above_dim4
#print axioms gaussBonnetTensor_vanishes_4D
#print axioms higher_lovelock_rank_exceeds_4D
#print axioms lovelock_4D_complete_bridge
#print axioms sorkinLambda_strict_pos
#print axioms sorkinLambda_sq_eq_inv_N
#print axioms sorkinLambda_sq_mul_N_eq_one
#print axioms sorkinLambda_small_for_large_N
#print axioms sorkin_self_consistency_relation
#print axioms sorkin_relative_fluctuation_eq_half_lambda
#print axioms sorkin_refined_cosmological_prediction
#print axioms einsteinLovelock4D_symm
#print axioms einsteinSorkin4D_symm
#print axioms einsteinLovelock4D_offDiag
#print axioms einsteinLovelock4D_diag
#print axioms einsteinLovelock4D_zero_lambda
#print axioms einsteinLovelock4D_zeroMetricDerivs
#print axioms einsteinLovelock4D_add_md
#print axioms einsteinLovelock4D_lorentzian_trace
#print axioms einsteinSorkin4D_lorentzian_trace
#print axioms einsteinLovelockYangMills4D_trace_zero
#print axioms einsteinLovelockYangMills4D_scalar_eq_four_lambda
#print axioms einsteinSorkinYangMills4D_scalar_pos_and_scaling
#print axioms einsteinLovelockYangMills4D_ricci_formula
#print axioms einsteinLovelockYangMills4D_scalarCurvaturePart4D_formula
#print axioms einsteinLovelockYangMills4D_riemann_weyl_decomposition
#print axioms einsteinLovelockYangMills4D_conformalPlusGravitationalWave_solution
#print axioms lovelock_sorkin_yang_mills_4D_master_synthesis

end
end UnifiedTheory.Audit.KFCausalCurved4DLovelockCosmologicalConstantSynthesis
