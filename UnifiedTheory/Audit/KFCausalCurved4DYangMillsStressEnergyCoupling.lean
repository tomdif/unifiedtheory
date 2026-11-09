import UnifiedTheory.Audit.KFCausalCurved4DDifferentialBianchiIdentity
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.NonabelianYangMills
import UnifiedTheory.LayerA.YangMillsVariational

/-! 4D Lorentzian Yang-Mills Action Density, Stress-Energy Tensor Conformal
Tracelessness (`T^μ_μ = 0`), and Linearized Einstein-Yang-Mills Curvature Coupling:
1. Instantiates `ymActionDensity` and `actionVariation` from `LayerA.YangMillsVariational`
   in 4D Lorentzian signature (`sign μ = -1` for `μ = 0`, `+1` for `μ = 1, 2, 3`).
2. Defines the 4D nonabelian Yang-Mills field-strength contraction `ymFieldStrengthSq4D`
   and the 4D Yang-Mills stress-energy tensor
   `ymStressEnergy4D sc conn μ ν = ymFieldStrengthSq4D sc conn μ ν - (1/4) η_{μν} S_{YM}`,
   proving symmetry (`T_{μν} = T_{νμ}`), off-diagonal shear/momentum-flux reduction,
   and exact 4D conformal tracelessness `∑ μ : Fin 4, sign μ * ymStressEnergy4D sc conn μ μ = 0`
   (arising specifically from the 4D Lorentzian trace `∑ μ : Fin 4, sign μ * η_{μμ} = 4`).
3. Proves that for ANY 4D metric perturbation `md : MetricDerivs 4` satisfying the
   coupled 4D linearized Einstein-Yang-Mills equation `einstein md sign μ ν = κ * ymStressEnergy4D sc conn μ ν`:
   - `lorentzianEinsteinTrace4D md = 0`,
   - `scalar md sign = 0` (vanishing 4D Ricci scalar curvature!),
   - `ricci md sign μ ν = einstein md sign μ ν = κ * ymStressEnergy4D sc conn μ ν`,
   - `box4D (metricTraceHessian4D md) = (1 / 6) * scalar (tracelessPartMetricDerivs4D md) sign`.
4. Establishes the exact solution structure on the combined conformal-plus-gravitational-wave
   family `conformalPlusGravitationalWaveMetricDerivs4D H K A B`: the conformal factor is
   harmonic (`box4D H = 0`), `H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν`, while the
   transverse-traceless gravitational wave amplitudes `(A, B)` propagate freely in the Weyl tensor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DYangMillsStressEnergyCoupling
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open UnifiedTheory.LayerA.GaugeConnection (StructureConstants ConnectionData
  curvature curvature_antisym abelianSC abelian_curvature
  linearizedCurvature linearizedCurvature_antisym linearizedCurvature_add
  killingForm killingForm_symm abelian_bianchi)
open UnifiedTheory.LayerA.GaugeDerived (zeroConnection yangMillsDivergence)
open UnifiedTheory.LayerA.NonabelianYangMills (covariantDeriv covariantDerivF
  yangMillsDivNonabelian satisfiesNonabelianYM
  zero_satisfies_nonabelian_ym nonabelian_reduces_to_abelian nonabelian_bianchi)
open UnifiedTheory.LayerA.YangMillsVariational (ymActionDensity ymAction_killing_symmetric
  actionVariation actionVariation_linear)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic dScalar dEinstein)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D minkMetric4D box4D
  fullConformalMetricDerivs fullRicciTensor4D fullScalarCurvature4D
  fullEinsteinTensor4D minkMetric4D_diag minkMetric4D_offDiag
  fullRicciTensor4D_master_formula fullScalarCurvature4D_master_formula
  fullEinsteinTensor4D_master_formula)
open KFCausalConformal4DCurvedDiamondMasterSynthesis (reconstructHessianFromEinstein4D
  reconstructHessianFromProbes4D reconstructHessianFromEinstein4D_exact
  reconstructHessianFromProbes4D_exact)
open KFCausalCurved4DLinearizedMetricDecomposition (minkMetric4D_lorentzian_trace
  metricTraceHessian4D tracelessPartMetricDerivs4D curvature_conformal_traceless_split)
open KFCausalCurved4DLinearizedWeylRicciSplit (minkMetric4D_symm
  ricciCurvaturePart4D scalarCurvaturePart4D ricciScalarRiemannPart4D
  weylTensor4D riemann_eq_weyl_add_ricciScalar weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DGeneralProbeCurvatureExtraction (lorentzianTensorTrace4D
  lorentzianEinsteinTrace4D lorentzianEinsteinTrace4D_eq_neg_scalar
  vacuum_einstein_iff_riemann_eq_weyl)
open KFCausalCurved4DTidalWeylProbeExtraction (basisVec4D weylTidalProbe)
open KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
  (conformalPlusGravitationalWaveMetricDerivs4D
   conformalPlusGravitationalWave_ricci_scalar_einstein
   conformalPlusGravitationalWave_joint_reconstruction)

variable {g_dim : ℕ}

/-! ### 1. 4D Lorentzian Metric Weights for the Yang-Mills Action & Stress-Energy Tensor -/

/-- Flat 4D Lorentzian metric/inverse-metric tensor `η_{μν} = diag(-1, +1, +1, +1)`. -/
def lorentzInvMetric4D (μ ν : Fin 4) : ℝ :=
  if μ = ν then sign μ else 0

/-- 4D Lorentzian bivector contraction weight `η^{μμ} η^{νν} = sign μ * sign ν`
used in the 4D Lorentzian Yang-Mills action density `∑_{μ,ν} sign μ * sign ν * κ_{ab} F^a_{μν} F^b_{μν}`. -/
def lorentzBivectorMetric4D (μ ν : Fin 4) : ℝ :=
  sign μ * sign ν

/-- `lorentzInvMetric4D` coincides identically with `minkMetric4D`. -/
theorem lorentzInvMetric4D_eq_minkMetric4D (μ ν : Fin 4) :
    lorentzInvMetric4D μ ν = minkMetric4D μ ν := rfl

/-- Symmetry of `lorentzInvMetric4D`. -/
theorem lorentzInvMetric4D_symm (μ ν : Fin 4) :
    lorentzInvMetric4D μ ν = lorentzInvMetric4D ν μ :=
  minkMetric4D_symm μ ν

/-- Diagonal evaluation of `lorentzInvMetric4D`: `lorentzInvMetric4D μ μ = sign μ`. -/
theorem lorentzInvMetric4D_diag (μ : Fin 4) :
    lorentzInvMetric4D μ μ = sign μ :=
  minkMetric4D_diag μ

/-- Off-diagonal evaluation of `lorentzInvMetric4D`: `lorentzInvMetric4D μ ν = 0` for `μ ≠ ν`. -/
theorem lorentzInvMetric4D_offDiag (μ ν : Fin 4) (h : μ ≠ ν) :
    lorentzInvMetric4D μ ν = 0 :=
  minkMetric4D_offDiag μ ν h

/-- The 4D Lorentzian trace of `lorentzInvMetric4D` equals the spacetime dimension `4`. -/
theorem lorentzInvMetric4D_lorentzian_trace :
    (∑ μ : Fin 4, sign μ * lorentzInvMetric4D μ μ) = 4 :=
  minkMetric4D_lorentzian_trace

/-- Symmetry of `lorentzBivectorMetric4D`. -/
theorem lorentzBivectorMetric4D_symm (μ ν : Fin 4) :
    lorentzBivectorMetric4D μ ν = lorentzBivectorMetric4D ν μ := by
  unfold lorentzBivectorMetric4D
  ring

/-- Unit diagonal of `lorentzBivectorMetric4D`: `sign μ * sign μ = 1`. -/
theorem lorentzBivectorMetric4D_diag_eq_one (μ : Fin 4) :
    lorentzBivectorMetric4D μ μ = 1 := by
  unfold lorentzBivectorMetric4D
  simp only [sign]
  split_ifs <;> norm_num

/-! ### 2. 4D Lorentzian Yang-Mills Action Density, Variation, and Stress-Energy Tensor -/

/-- 4D Lorentzian Yang-Mills action density `κ_{ab} F^a_{μν} F^{b μν}`, instantiated from
`LayerA.YangMillsVariational.ymActionDensity` with `lorentzBivectorMetric4D`. -/
def lorentzYMActionDensity4D (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) : ℝ :=
  ymActionDensity sc conn lorentzBivectorMetric4D

/-- 4D Lorentzian linearized Yang-Mills action variation, instantiated from
`LayerA.YangMillsVariational.actionVariation` with `lorentzBivectorMetric4D`. -/
def lorentzYMVariation4D (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim)
    (δA : Fin 4 → Fin g_dim → ℝ)
    (dδA : Fin 4 → Fin 4 → Fin g_dim → ℝ) : ℝ :=
  actionVariation sc conn lorentzBivectorMetric4D δA dδA

/-- 4D Lorentzian Yang-Mills field-strength contraction
`(F^2)_{μν} = ∑_{α,a,b} sign α * κ_{ab} F^a_{μα} F^b_{να}`. -/
def ymFieldStrengthSq4D (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ a : Fin g_dim, ∑ b : Fin g_dim,
    sign α * killingForm sc a b * curvature sc conn μ α a * curvature sc conn ν α b

/-- **4D Lorentzian Yang-Mills Stress-Energy Tensor**:
`T^{YM}_{μν} = (F^2)_{μν} - (1/4) η_{μν} S_{YM}`. -/
def ymStressEnergy4D (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) : ℝ :=
  ymFieldStrengthSq4D sc conn μ ν -
    (1 / 4 : ℝ) * lorentzInvMetric4D μ ν * lorentzYMActionDensity4D sc conn

/-- Lie-algebra Killing-form symmetry of `lorentzYMActionDensity4D`. -/
theorem lorentzYMActionDensity4D_killing_symm (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) :
    lorentzYMActionDensity4D sc conn =
      ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ a : Fin g_dim, ∑ b : Fin g_dim,
        lorentzBivectorMetric4D μ ν * killingForm sc b a *
          curvature sc conn μ ν a * curvature sc conn μ ν b :=
  ymAction_killing_symmetric sc conn lorentzBivectorMetric4D

/-- Linearity of the 4D Lorentzian Yang-Mills action variation `lorentzYMVariation4D`
with respect to gauge perturbations `(δA, dδA)`. -/
theorem lorentzYMVariation4D_linear (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim)
    (δA₁ δA₂ : Fin 4 → Fin g_dim → ℝ)
    (dδA₁ dδA₂ : Fin 4 → Fin 4 → Fin g_dim → ℝ) :
    lorentzYMVariation4D sc conn (fun i j => δA₁ i j + δA₂ i j)
      (fun i j k => dδA₁ i j k + dδA₂ i j k) =
      lorentzYMVariation4D sc conn δA₁ dδA₁ +
        lorentzYMVariation4D sc conn δA₂ dδA₂ :=
  actionVariation_linear sc conn lorentzBivectorMetric4D δA₁ δA₂ dδA₁ dδA₂

/-- Diagonal spacetime components of the gauge curvature vanish identically (`F^a_{μμ} = 0`). -/
theorem curvature_diag_zero (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ : Fin 4) (a : Fin g_dim) :
    curvature sc conn μ μ a = 0 := by
  have h := curvature_antisym sc conn μ μ a
  linarith

/-- Symmetry of the 4D Yang-Mills field-strength contraction:
`ymFieldStrengthSq4D sc conn μ ν = ymFieldStrengthSq4D sc conn ν μ`. -/
theorem ymFieldStrengthSq4D_symm (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) :
    ymFieldStrengthSq4D sc conn μ ν = ymFieldStrengthSq4D sc conn ν μ := by
  unfold ymFieldStrengthSq4D
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [killingForm_symm sc b a]
  ring

/-- Symmetry of the 4D Yang-Mills stress-energy tensor:
`ymStressEnergy4D sc conn μ ν = ymStressEnergy4D sc conn ν μ`. -/
theorem ymStressEnergy4D_symm (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) :
    ymStressEnergy4D sc conn μ ν = ymStressEnergy4D sc conn ν μ := by
  unfold ymStressEnergy4D
  rw [ymFieldStrengthSq4D_symm sc conn μ ν, lorentzInvMetric4D_symm μ ν]

/-- For off-diagonal indices `μ ≠ ν` (momentum-flux / Poynting-flux and anisotropic
shear-stress channels), the metric trace term vanishes and `ymStressEnergy4D`
equals `ymFieldStrengthSq4D`. -/
theorem ymStressEnergy4D_offDiag_eq_fieldStrengthSq (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    ymStressEnergy4D sc conn μ ν = ymFieldStrengthSq4D sc conn μ ν := by
  unfold ymStressEnergy4D
  rw [lorentzInvMetric4D_offDiag μ ν hμν]
  ring

/-- Diagonal formula for `ymStressEnergy4D`:
`T^{YM}_{μμ} = (F^2)_{μμ} - (1/4) (sign μ) S_{YM}`. -/
theorem ymStressEnergy4D_diag_formula (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (μ : Fin 4) :
    ymStressEnergy4D sc conn μ μ =
      ymFieldStrengthSq4D sc conn μ μ -
        (1 / 4 : ℝ) * sign μ * lorentzYMActionDensity4D sc conn := by
  unfold ymStressEnergy4D
  rw [lorentzInvMetric4D_diag μ]

/-! ### 3. Exact 4D Conformal Tracelessness of the Yang-Mills Stress-Energy Tensor -/

/-- The 4D Lorentzian trace of `ymFieldStrengthSq4D` equals the 4D Lorentzian
Yang-Mills action density `lorentzYMActionDensity4D`. -/
theorem ymFieldStrengthSq4D_lorentzian_trace (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) :
    (∑ μ : Fin 4, sign μ * ymFieldStrengthSq4D sc conn μ μ) =
      lorentzYMActionDensity4D sc conn := by
  unfold ymFieldStrengthSq4D lorentzYMActionDensity4D ymActionDensity lorentzBivectorMetric4D
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Characteristic 4D conformal factor identity: `(1 / 4) * Tr_η(η) = (1 / 4) * 4 = 1`. -/
theorem ymStressEnergy4D_trace_factor_identity :
    (1 / 4 : ℝ) * (∑ μ : Fin 4, sign μ * lorentzInvMetric4D μ μ) = 1 := by
  rw [lorentzInvMetric4D_lorentzian_trace]
  norm_num

/-- **4D Yang-Mills Stress-Energy Conformal Tracelessness Theorem**:
For every Lie algebra `sc : StructureConstants g_dim` and every 4D gauge connection
`conn : ConnectionData 4 g_dim`, the Lorentzian trace of `ymStressEnergy4D`
vanishes identically:
`∑ μ : Fin 4, sign μ * ymStressEnergy4D sc conn μ μ = 0`. -/
theorem ymStressEnergy4D_lorentzian_trace_zero (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) :
    (∑ μ : Fin 4, sign μ * ymStressEnergy4D sc conn μ μ) = 0 := by
  unfold ymStressEnergy4D
  have hterm : ∀ μ : Fin 4,
      sign μ * (ymFieldStrengthSq4D sc conn μ μ -
        (1 / 4 : ℝ) * lorentzInvMetric4D μ μ * lorentzYMActionDensity4D sc conn) =
      sign μ * ymFieldStrengthSq4D sc conn μ μ -
        (1 / 4 : ℝ) * (sign μ * lorentzInvMetric4D μ μ) * lorentzYMActionDensity4D sc conn := by
    intro μ; ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [ymFieldStrengthSq4D_lorentzian_trace, lorentzInvMetric4D_lorentzian_trace]
  ring

/-! ### 4. Zero-Connection, Abelian, and 4D Nonabelian Bianchi Properties -/

/-- The curvature of `zeroConnection` vanishes identically in 4D. -/
theorem curvature_zeroConnection (sc : StructureConstants g_dim)
    (μ ν : Fin 4) (a : Fin g_dim) :
    curvature sc (zeroConnection (n := 4) (g_dim := g_dim)) μ ν a = 0 := by
  simp [curvature, zeroConnection]

/-- `ymFieldStrengthSq4D` vanishes identically at `zeroConnection`. -/
theorem ymFieldStrengthSq4D_zeroConnection (sc : StructureConstants g_dim)
    (μ ν : Fin 4) :
    ymFieldStrengthSq4D sc (zeroConnection (n := 4) (g_dim := g_dim)) μ ν = 0 := by
  unfold ymFieldStrengthSq4D
  apply Finset.sum_eq_zero; intro α _
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  rw [curvature_zeroConnection, mul_zero, zero_mul]

/-- `lorentzYMActionDensity4D` vanishes identically at `zeroConnection`. -/
theorem lorentzYMActionDensity4D_zeroConnection (sc : StructureConstants g_dim) :
    lorentzYMActionDensity4D sc (zeroConnection (n := 4) (g_dim := g_dim)) = 0 := by
  rw [← ymFieldStrengthSq4D_lorentzian_trace]
  apply Finset.sum_eq_zero; intro μ _
  rw [ymFieldStrengthSq4D_zeroConnection, mul_zero]

/-- `ymStressEnergy4D` vanishes identically at `zeroConnection`. -/
theorem ymStressEnergy4D_zeroConnection (sc : StructureConstants g_dim)
    (μ ν : Fin 4) :
    ymStressEnergy4D sc (zeroConnection (n := 4) (g_dim := g_dim)) μ ν = 0 := by
  unfold ymStressEnergy4D
  rw [ymFieldStrengthSq4D_zeroConnection, lorentzYMActionDensity4D_zeroConnection]
  ring

/-- The Killing form of the abelian Lie algebra `abelianSC` vanishes identically
(`κ_{ab} = 0`), reflecting that semisimple/nonabelian structure constants are required
for a non-degenerate Killing form. -/
theorem killingForm_abelianSC_zero (a b : Fin g_dim) :
    UnifiedTheory.LayerA.GaugeConnection.killingForm (abelianSC (g_dim := g_dim)) a b = 0 := by
  simp [UnifiedTheory.LayerA.GaugeConnection.killingForm, abelianSC]

/-- Because `killingForm abelianSC = 0`, the Killing-form stress-energy tensor
vanishes identically on `abelianSC`. -/
theorem ymStressEnergy4D_abelianSC_zero (conn : ConnectionData 4 g_dim) (μ ν : Fin 4) :
    ymStressEnergy4D (abelianSC (g_dim := g_dim)) conn μ ν = 0 := by
  have hsq : ∀ α β : Fin 4,
      ymFieldStrengthSq4D (abelianSC (g_dim := g_dim)) conn α β = 0 := by
    intro α β
    unfold ymFieldStrengthSq4D
    apply Finset.sum_eq_zero; intro γ _
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    rw [killingForm_abelianSC_zero, mul_zero, zero_mul, zero_mul]
  have hact : lorentzYMActionDensity4D (abelianSC (g_dim := g_dim)) conn = 0 := by
    rw [← ymFieldStrengthSq4D_lorentzian_trace]
    apply Finset.sum_eq_zero; intro α _
    rw [hsq, mul_zero]
  unfold ymStressEnergy4D
  rw [hsq, hact]
  ring

/-- 4D specialization of the nonabelian gauge Bianchi identity
`D_λ F_{μν} + D_μ F_{νλ} + D_ν F_{λμ} = 0`. -/
theorem nonabelian_bianchi_4D (sc : StructureConstants g_dim)
    (conn : ConnectionData 4 g_dim) (l_ μ ν : Fin 4) (a : Fin g_dim) :
    covariantDerivF sc conn l_ μ ν a +
      covariantDerivF sc conn μ ν l_ a +
      covariantDerivF sc conn ν l_ μ a = 0 :=
  nonabelian_bianchi sc conn l_ μ ν a

/-- 4D specialization of `zero_satisfies_nonabelian_ym` and `nonabelian_reduces_to_abelian`. -/
theorem nonabelian_ym_zero_and_abelian_reduction_4D (sc : StructureConstants g_dim) :
    satisfiesNonabelianYM sc (zeroConnection (n := 4) (g_dim := g_dim)) ∧
    (∀ (conn : ConnectionData 4 g_dim) (ν : Fin 4) (a : Fin g_dim),
      yangMillsDivNonabelian abelianSC conn ν a = yangMillsDivergence conn ν a) :=
  ⟨zero_satisfies_nonabelian_ym sc, nonabelian_reduces_to_abelian⟩

/-! ### 5. Coupled 4D Linearized Einstein-Yang-Mills Field Equation & Consequences -/

/-- Predicate that a 4D metric perturbation `md : MetricDerivs 4` satisfies the
linearized 4D Einstein-Yang-Mills field equation `G_{μν}(md) = κ T^{YM}_{μν}(sc, conn)`. -/
def SatisfiesEinsteinYangMills4D (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim) : Prop :=
  ∀ μ ν : Fin 4, einstein md sign μ ν = κ * ymStressEnergy4D sc conn μ ν

/-- **Vanishing Einstein Trace for 4D Einstein-Yang-Mills**: any 4D metric
perturbation `md` coupled to a 4D Yang-Mills field has `lorentzianEinsteinTrace4D md = 0`. -/
theorem einsteinYangMills4D_einstein_trace_zero (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) :
    lorentzianEinsteinTrace4D md = 0 := by
  unfold lorentzianEinsteinTrace4D lorentzianTensorTrace4D
  have hsum : (∑ b : Fin 4, sign b * einstein md sign b b) =
      κ * (∑ b : Fin 4, sign b * ymStressEnergy4D sc conn b b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [hEYM b b]
    ring
  rw [hsum, ymStressEnergy4D_lorentzian_trace_zero, mul_zero]

/-- **Vanishing Scalar Curvature for 4D Einstein-Yang-Mills**: because the 4D
Yang-Mills stress-energy tensor is traceless (`T^μ_μ = 0`) and `Tr_η(G) = -R` in 4D,
every solution to the 4D linearized Einstein-Yang-Mills equation has identically
zero scalar curvature (`scalar md sign = 0`). -/
theorem einsteinYangMills4D_scalar_curvature_zero (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) :
    scalar md sign = 0 := by
  rw [(lorentzianEinsteinTrace4D_eq_neg_scalar md).2,
    einsteinYangMills4D_einstein_trace_zero md κ sc conn hEYM, neg_zero]

/-- **Ricci-Einstein Coincidence for 4D Einstein-Yang-Mills**: for every solution
to `SatisfiesEinsteinYangMills4D md κ sc conn`, the scalar trace term in `G_{μν}`
vanishes identically, so `ricci md sign μ ν = einstein md sign μ ν = κ * ymStressEnergy4D sc conn μ ν`. -/
theorem einsteinYangMills4D_ricci_eq_einstein (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) (μ ν : Fin 4) :
    ricci md sign μ ν = einstein md sign μ ν ∧
    ricci md sign μ ν = κ * ymStressEnergy4D sc conn μ ν := by
  have hR0 := einsteinYangMills4D_scalar_curvature_zero md κ sc conn hEYM
  have hric : ricci md sign μ ν = einstein md sign μ ν := by
    unfold einstein
    rw [hR0]
    ring
  exact ⟨hric, hric.trans (hEYM μ ν)⟩

/-- **Conformal Wave-Operator Constraint for 4D Einstein-Yang-Mills**: for every
general 4D metric perturbation `md` satisfying `SatisfiesEinsteinYangMills4D md κ sc conn`,
the wave operator of its conformal trace Hessian satisfies
`box4D (metricTraceHessian4D md) = (1 / 6) * scalar (tracelessPartMetricDerivs4D md) sign`. -/
theorem einsteinYangMills4D_conformal_wave_equation (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) :
    box4D (metricTraceHessian4D md) =
      (1 / 6 : ℝ) * scalar (tracelessPartMetricDerivs4D md) sign := by
  have hR0 := einsteinYangMills4D_scalar_curvature_zero md κ sc conn hEYM
  have hsplit := (curvature_conformal_traceless_split md).2.2.1
  have hconf := (fullScalarCurvature4D_master_formula (metricTraceHessian4D md)).1
  linarith

/-- **Vanishing Scalar Kulkarni-Nomizu Part for 4D Einstein-Yang-Mills**: for every
solution to `SatisfiesEinsteinYangMills4D md κ sc conn`, the scalar curvature part
`scalarCurvaturePart4D md a b c d` of the 4D Riemann tensor vanishes identically. -/
theorem einsteinYangMills4D_scalarCurvaturePart4D_zero (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) (a b c d : Fin 4) :
    scalarCurvaturePart4D md a b c d = 0 := by
  unfold scalarCurvaturePart4D
  rw [einsteinYangMills4D_scalar_curvature_zero md κ sc conn hEYM]
  ring

/-- **Exact 4D Riemann Kulkarni-Nomizu Decomposition for Einstein-Yang-Mills**:
for every general 4D metric perturbation `md` satisfying
`SatisfiesEinsteinYangMills4D md κ sc conn`, its 20-component Riemann tensor
decomposes into the Weyl tensor of its traceless part plus the pure Kulkarni-Nomizu
product of `minkMetric4D` with `ymStressEnergy4D`:
`R_{abcd} = C_{abcd}(h^{TT}) + (κ / 2)(η_{ac} T^{YM}_{bd} - η_{ad} T^{YM}_{bc} - η_{bc} T^{YM}_{ad} + η_{bd} T^{YM}_{ac})`. -/
theorem einsteinYangMills4D_riemann_kulkarni_nomizu_formula (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D md κ sc conn) (a b c d : Fin 4) :
    R_metric md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d +
        (κ / 2) * (minkMetric4D a c * ymStressEnergy4D sc conn b d -
          minkMetric4D a d * ymStressEnergy4D sc conn b c -
          minkMetric4D b c * ymStressEnergy4D sc conn a d +
          minkMetric4D b d * ymStressEnergy4D sc conn a c) := by
  rw [(riemann_eq_weyl_add_ricciScalar md a b c d).2,
    weylTensor4D_eq_tracelessPart md a b c d,
    einsteinYangMills4D_scalarCurvaturePart4D_zero md κ sc conn hEYM a b c d]
  unfold ricciCurvaturePart4D
  rw [(einsteinYangMills4D_ricci_eq_einstein md κ sc conn hEYM b d).2,
    (einsteinYangMills4D_ricci_eq_einstein md κ sc conn hEYM b c).2,
    (einsteinYangMills4D_ricci_eq_einstein md κ sc conn hEYM a d).2,
    (einsteinYangMills4D_ricci_eq_einstein md κ sc conn hEYM a c).2]
  ring

/-- At `zeroConnection`, the 4D Einstein-Yang-Mills equation reduces to the vacuum
Einstein equation `einstein md sign μ ν = 0` (which in turn is equivalent to
`R_metric md = weylTensor4D md`). -/
theorem einsteinYangMills4D_zeroConnection_iff_vacuum (md : MetricDerivs 4) (κ : ℝ)
    (sc : StructureConstants g_dim) :
    (SatisfiesEinsteinYangMills4D md κ sc (zeroConnection (n := 4) (g_dim := g_dim)) ↔
      ∀ μ ν : Fin 4, einstein md sign μ ν = 0) ∧
    (SatisfiesEinsteinYangMills4D md κ sc (zeroConnection (n := 4) (g_dim := g_dim)) ↔
      ∀ a b c d : Fin 4, R_metric md a b c d = weylTensor4D md a b c d) := by
  have hvac : SatisfiesEinsteinYangMills4D md κ sc (zeroConnection (n := 4) (g_dim := g_dim)) ↔
      ∀ μ ν : Fin 4, einstein md sign μ ν = 0 := by
    unfold SatisfiesEinsteinYangMills4D
    simp_rw [ymStressEnergy4D_zeroConnection, mul_zero]
  exact ⟨hvac, hvac.trans (vacuum_einstein_iff_riemann_eq_weyl md)⟩

/-- **Master 4D Einstein-Yang-Mills Coupling Theorem on Conformal-Plus-Gravitational-Wave
Perturbations**: for any symmetric conformal Hessian `H : Hessian4D`, third jet `K : ThirdJet4D`,
and gravitational-wave amplitudes `A, B : ℝ`, if
`md = conformalPlusGravitationalWaveMetricDerivs4D H K A B` satisfies
`SatisfiesEinsteinYangMills4D md κ sc conn`, then:
1. `scalar md sign = 0` and `fullScalarCurvature4D H = 0`,
2. The conformal factor satisfies the massless 4D wave equation `box4D H = 0`,
3. Every component of `H` is directly determined by the Yang-Mills stress-energy tensor:
   `H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν`,
4. Both gravitational-wave polarizations `(A, B)` are extracted independently by
   the Weyl tidal probes `weylTidalProbe`. -/
theorem einsteinYangMills4D_conformalPlusGravitationalWave_master
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim)
    (hEYM : SatisfiesEinsteinYangMills4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) κ sc conn) :
    let md := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    scalar md sign = 0 ∧
    fullScalarCurvature4D H = 0 ∧
    box4D H = 0 ∧
    (∀ μ ν : Fin 4, H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν) ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 1) md = A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 2) md = B := by
  intro md
  have hR0 := einsteinYangMills4D_scalar_curvature_zero md κ sc conn hEYM
  have hcomb := conformalPlusGravitationalWave_ricci_scalar_einstein H K A B
  have hFH0 : fullScalarCurvature4D H = 0 := by
    rw [← hcomb.2.1, hR0]
  have hbox0 : box4D H = 0 := by
    have h1 := (fullScalarCurvature4D_master_formula H).1
    linarith
  have hH_eq : ∀ μ ν : Fin 4, H μ ν = -(κ / 2) * ymStressEnergy4D sc conn μ ν := by
    intro μ ν
    have hG : einstein md sign μ ν = -2 * H μ ν := by
      rw [hcomb.2.2 μ ν, fullEinsteinTensor4D_master_formula H hH μ ν, hbox0]
      ring
    have hEYM_μν := hEYM μ ν
    linarith
  have hrec := conformalPlusGravitationalWave_joint_reconstruction H hH K A B
  exact ⟨hR0, hFH0, hbox0, hH_eq, hrec.2.1, hrec.2.2.2.1⟩

#print axioms lorentzInvMetric4D_eq_minkMetric4D
#print axioms lorentzInvMetric4D_symm
#print axioms lorentzInvMetric4D_diag
#print axioms lorentzInvMetric4D_offDiag
#print axioms lorentzInvMetric4D_lorentzian_trace
#print axioms lorentzBivectorMetric4D_symm
#print axioms lorentzBivectorMetric4D_diag_eq_one
#print axioms lorentzYMActionDensity4D_killing_symm
#print axioms lorentzYMVariation4D_linear
#print axioms curvature_diag_zero
#print axioms ymFieldStrengthSq4D_symm
#print axioms ymStressEnergy4D_symm
#print axioms ymStressEnergy4D_offDiag_eq_fieldStrengthSq
#print axioms ymStressEnergy4D_diag_formula
#print axioms ymFieldStrengthSq4D_lorentzian_trace
#print axioms ymStressEnergy4D_trace_factor_identity
#print axioms ymStressEnergy4D_lorentzian_trace_zero
#print axioms curvature_zeroConnection
#print axioms ymFieldStrengthSq4D_zeroConnection
#print axioms lorentzYMActionDensity4D_zeroConnection
#print axioms ymStressEnergy4D_zeroConnection
#print axioms killingForm_abelianSC_zero
#print axioms ymStressEnergy4D_abelianSC_zero
#print axioms nonabelian_bianchi_4D
#print axioms nonabelian_ym_zero_and_abelian_reduction_4D
#print axioms einsteinYangMills4D_einstein_trace_zero
#print axioms einsteinYangMills4D_scalar_curvature_zero
#print axioms einsteinYangMills4D_ricci_eq_einstein
#print axioms einsteinYangMills4D_conformal_wave_equation
#print axioms einsteinYangMills4D_scalarCurvaturePart4D_zero
#print axioms einsteinYangMills4D_riemann_kulkarni_nomizu_formula
#print axioms einsteinYangMills4D_zeroConnection_iff_vacuum
#print axioms einsteinYangMills4D_conformalPlusGravitationalWave_master

end
end UnifiedTheory.Audit.KFCausalCurved4DYangMillsStressEnergyCoupling
