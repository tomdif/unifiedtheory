import UnifiedTheory.Audit.KFCausalCurved4DTwentyComponentRiemannMasterSynthesis

/-! 4D Linearized Differential (Second) Bianchi Identity on Weyl and Ricci
Channels, Third-Jet Curvature Linearity, and Conformal-Plus-Gravitational-Wave
Differential Conservation Synthesis:
1. Full linearity (`zero`, `add`, `smul`, `sub`) of the third-jet curvature
   derivatives `dR_metric`, `dRic`, `divRic`, `dScalar`, and `dEinstein`.
2. Algebraic symmetries (`dR_metric_antisym1`, `dR_metric_antisym2`,
   `dR_metric_pair_symm`, `dR_metric_first_bianchi`, `dRic_symm`, `dEinstein_symm`)
   and the exact differential (second) Bianchi identity
   `dR_metric md e a b c d + dR_metric md a b e c d + dR_metric md b e a c d = 0`,
   together with its once-contracted and twice-contracted (`2 * divRic = dScalar`,
   `∑ e, sign e * dEinstein = 0`) consequences.
3. Exact 4D differentiated Kulkarni-Nomizu / Weyl-Ricci-Scalar split
   `dR_metric = dWeylTensor4D + dRicciScalarRiemannPart4D`, trace-freeness of
   `dWeylTensor4D`, and identical vanishing of `dWeylTensor4D` on all 4D
   conformal third-jet perturbations (`dWeylTensor4D md = dWeylTensor4D (tracelessPartMetricDerivs4D md)`).
4. Exact differential conservation on the combined conformal-plus-gravitational-wave
   family `conformalPlusGravitationalWaveMetricDerivs4D H K A B`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DDifferentialBianchiIdentity
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric
  dR_antisym1 dR_antisym2 bianchi2)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein
  dRic divRic dScalar dEinstein once_contracted contracted_bianchi
  metric_dRic_symmetric lorentzian_metric_divergence lorentzian_metric_first_divergence)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D minkMetric4D dBox4D
  fullConformalMetricThird fullConformalMetricDerivs
  fullDRicci4D fullDScalar4D fullDEinstein4D
  symmetrizeThirdJet4D_eq_of_symm
  fullDRicci4D_master_formula fullDScalar4D_master_formula fullDEinstein4D_master_formula
  bianchiDiagonalChannel4D bianchiOffDiagonalChannel4D
  bianchi_diagonal_offDiagonal_channel_decomposition)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs subMetricDerivs
  dR_metric_zero dR_metric_add dR_metric_smul dR_metric_sub
  dRic_add dRic_smul dRic_sub
  dScalar_add dScalar_smul dScalar_sub
  dEinstein_add dEinstein_smul dEinstein_sub
  minkMetric4D_lorentzian_trace metricTraceHessian4D metricTraceThirdJet4D
  metricTraceHessian4D_symmetric metricTraceThirdJet4D_symmetric
  conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (minkMetric4D_symm
  lorentzian_minkMetric4D_contract_left lorentzian_minkMetric4D_contract_right)
open KFCausalCurved4DTidalWeylProbeExtraction (plusWaveMetricDerivs4D crossWaveMetricDerivs4D)
open KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
  (conformalPlusGravitationalWaveMetricDerivs4D)

variable {n : ℕ}

/-! ### 1. Linearity of Third-Jet Curvature Operators on `MetricDerivs n` -/

/-- The differentiated Ricci tensor `dRic` vanishes identically on `zeroMetricDerivs n`. -/
theorem dRic_zero (w : Fin n → ℝ) (e b d : Fin n) :
    dRic (riemannFromMetric (zeroMetricDerivs n)) w e b d = 0 := by
  unfold dRic riemannFromMetric
  dsimp
  apply Finset.sum_eq_zero
  intro a _
  rw [dR_metric_zero, mul_zero]

/-- The Ricci divergence `divRic` vanishes identically on `zeroMetricDerivs n`. -/
theorem divRic_zero (w : Fin n → ℝ) (b : Fin n) :
    divRic (riemannFromMetric (zeroMetricDerivs n)) w b = 0 := by
  unfold divRic
  apply Finset.sum_eq_zero
  intro e _
  rw [dRic_zero, mul_zero]

/-- Additivity of the Ricci divergence `divRic` under `addMetricDerivs`. -/
theorem divRic_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b : Fin n) :
    divRic (riemannFromMetric (addMetricDerivs md₁ md₂)) w b =
      divRic (riemannFromMetric md₁) w b + divRic (riemannFromMetric md₂) w b := by
  unfold divRic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [dRic_add]
  ring

/-- Scalar-multiplication linearity of `divRic` under `smulMetricDerivs`. -/
theorem divRic_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (b : Fin n) :
    divRic (riemannFromMetric (smulMetricDerivs r md)) w b =
      r * divRic (riemannFromMetric md) w b := by
  unfold divRic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [dRic_smul]
  ring

/-- Subtractivity of `divRic` under `subMetricDerivs`. -/
theorem divRic_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b : Fin n) :
    divRic (riemannFromMetric (subMetricDerivs md₁ md₂)) w b =
      divRic (riemannFromMetric md₁) w b - divRic (riemannFromMetric md₂) w b := by
  unfold divRic
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [dRic_sub]
  ring

/-- The differentiated scalar curvature `dScalar` vanishes identically on `zeroMetricDerivs n`. -/
theorem dScalar_zero (w : Fin n → ℝ) (e : Fin n) :
    dScalar (riemannFromMetric (zeroMetricDerivs n)) w e = 0 := by
  unfold dScalar
  apply Finset.sum_eq_zero
  intro b _
  rw [dRic_zero, mul_zero]

/-- The differentiated Einstein tensor `dEinstein` vanishes identically on `zeroMetricDerivs n`. -/
theorem dEinstein_zero (w : Fin n → ℝ) (e b d : Fin n) :
    dEinstein (riemannFromMetric (zeroMetricDerivs n)) w e b d = 0 := by
  unfold dEinstein
  rw [dRic_zero, dScalar_zero]
  ring

/-! ### 2. Algebraic Symmetries and Differential (Second) Bianchi Identity of `dR_metric` -/

/-- Antisymmetry of `dR_metric` in the first Riemann index pair `(a, b)`. -/
theorem dR_metric_antisym1 (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric md e a b c d = -dR_metric md e b a c d :=
  dR_antisym1 md e a b c d

/-- Antisymmetry of `dR_metric` in the second Riemann index pair `(c, d)`. -/
theorem dR_metric_antisym2 (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric md e a b c d = -dR_metric md e a b d c :=
  dR_antisym2 md e a b c d

/-- Pair exchange symmetry `∂_e R_{abcd} = ∂_e R_{cdab}` of `dR_metric`. -/
theorem dR_metric_pair_symm (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric md e a b c d = dR_metric md e c d a b := by
  simp only [dR_metric]
  have h1 : md.k e c b a d = md.k e b c d a := by rw [md.k_sym23, md.k_metric]
  have h2 : md.k e c a b d = md.k e a c d b := by rw [md.k_sym23, md.k_metric]
  have h3 : md.k e d b a c = md.k e b d c a := by rw [md.k_sym23, md.k_metric]
  have h4 : md.k e d a b c = md.k e a d c b := by rw [md.k_sym23, md.k_metric]
  linarith

/-- First (algebraic) Bianchi identity `∂_e R_{abcd} + ∂_e R_{bcad} + ∂_e R_{cabd} = 0`
at fixed differentiation index `e`. -/
theorem dR_metric_first_bianchi (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric md e a b c d + dR_metric md e b c a d + dR_metric md e c a b d = 0 := by
  simp only [dR_metric]
  have h1 : md.k e c b a d = md.k e b c a d := md.k_sym23 e c b a d
  have h2 : md.k e c a b d = md.k e a c b d := md.k_sym23 e c a b d
  have h3 : md.k e b a c d = md.k e a b c d := md.k_sym23 e b a c d
  have h4 : md.k e d b a c = md.k e d b c a := md.k_metric e d b a c
  have h5 : md.k e d a b c = md.k e d a c b := md.k_metric e d a b c
  have h6 : md.k e d c b a = md.k e d c a b := md.k_metric e d c b a
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- **Differential (Second) Bianchi Identity** for the linearized Riemann tensor:
`∂_e R_{abcd} + ∂_a R_{becd} + ∂_b R_{eacd} = 0` for every metric perturbation jet `md`. -/
theorem dR_metric_second_bianchi (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric md e a b c d + dR_metric md a b e c d + dR_metric md b e a c d = 0 :=
  bianchi2 md e a b c d

/-- Symmetry of the differentiated Ricci tensor `∂_e R_{bd} = ∂_e R_{db}`. -/
theorem dRic_symm (md : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dRic (riemannFromMetric md) w e b d = dRic (riemannFromMetric md) w e d b :=
  metric_dRic_symmetric md w e b d

/-- Symmetry of the differentiated Einstein tensor `∂_e G_{bd} = ∂_e G_{db}`. -/
theorem dEinstein_symm (md : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dEinstein (riemannFromMetric md) w e b d = dEinstein (riemannFromMetric md) w e d b := by
  simp only [dEinstein, dRic_symm md w e b d]
  by_cases h : b = d
  · subst d; rfl
  · simp only [if_neg h, if_neg (Ne.symm h)]

/-- Once-contracted differential Bianchi identity for any `md : MetricDerivs n`:
`(∑ c, w c * ∂_c R_{abcd}) - ∂_a R_{bd} + ∂_b R_{ad} = 0`. -/
theorem dR_metric_once_contracted (md : MetricDerivs n) (w : Fin n → ℝ) (a b d : Fin n) :
    (∑ c : Fin n, w c * dR_metric md c a b c d) -
      dRic (riemannFromMetric md) w a b d +
      dRic (riemannFromMetric md) w b a d = 0 :=
  once_contracted (riemannFromMetric md) w a b d

/-- Twice-contracted differential Bianchi identity for any `md : MetricDerivs n`:
`2 * divRic (riemannFromMetric md) w b = dScalar (riemannFromMetric md) w b`. -/
theorem dRic_contracted_bianchi (md : MetricDerivs n) (w : Fin n → ℝ) (b : Fin n) :
    2 * divRic (riemannFromMetric md) w b = dScalar (riemannFromMetric md) w b :=
  contracted_bianchi (riemannFromMetric md) w b

/-- Exact 4D Lorentzian divergence-freeness of the linearized Einstein tensor on both
indices for every metric perturbation jet `md : MetricDerivs 4`. -/
theorem dEinstein_lorentzian_divergence_zero (md : MetricDerivs 4) (b : Fin 4) :
    (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e b e) = 0 ∧
    (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e e b) = 0 :=
  ⟨lorentzian_metric_divergence md b, lorentzian_metric_first_divergence md b⟩

/-! ### 3. 4D Differentiated Weyl-Ricci-Scalar Split (`dWeylTensor4D` & `dRicciScalarRiemannPart4D`) -/

/-- Differentiated Ricci Kulkarni-Nomizu part
`(1/2)(η_{ac} ∂_e Ric_{bd} - η_{ad} ∂_e Ric_{bc} - η_{bc} ∂_e Ric_{ad} + η_{bd} ∂_e Ric_{ac})`
of the 4D Lorentzian Riemann derivative `∂_e R_{abcd}`. -/
def dRicciCurvaturePart4D (md : MetricDerivs 4) (e a b c d : Fin 4) : ℝ :=
  (1 / 2) * (minkMetric4D a c * dRic (riemannFromMetric md) sign e b d -
    minkMetric4D a d * dRic (riemannFromMetric md) sign e b c -
    minkMetric4D b c * dRic (riemannFromMetric md) sign e a d +
    minkMetric4D b d * dRic (riemannFromMetric md) sign e a c)

/-- Differentiated scalar Kulkarni-Nomizu part
`-(1/6) (∂_e R) (η_{ac} η_{bd} - η_{ad} η_{bc})` of `∂_e R_{abcd}`. -/
def dScalarCurvaturePart4D (md : MetricDerivs 4) (e a b c d : Fin 4) : ℝ :=
  -(1 / 6) * dScalar (riemannFromMetric md) sign e *
    (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c)

/-- Combined differentiated Ricci-plus-Scalar (Schouten / Kulkarni-Nomizu) part of `∂_e R_{abcd}`. -/
def dRicciScalarRiemannPart4D (md : MetricDerivs 4) (e a b c d : Fin 4) : ℝ :=
  dRicciCurvaturePart4D md e a b c d + dScalarCurvaturePart4D md e a b c d

/-- Differentiated 4D Weyl conformal curvature tensor `∂_e C_{abcd}`, defined as the
trace-free part of the differentiated Riemann tensor `∂_e R_{abcd}`. -/
def dWeylTensor4D (md : MetricDerivs 4) (e a b c d : Fin 4) : ℝ :=
  dR_metric md e a b c d - dRicciScalarRiemannPart4D md e a b c d

/-- Exact 4D differentiated Riemann-Weyl-Ricci-Scalar decomposition:
`∂_e R_{abcd} = ∂_e C_{abcd} + dRicciScalarRiemannPart4D_{eabcd}`. -/
theorem dR_metric_eq_dWeyl_add_dRicciScalar (md : MetricDerivs 4) (e a b c d : Fin 4) :
    dR_metric md e a b c d =
      dWeylTensor4D md e a b c d + dRicciScalarRiemannPart4D md e a b c d ∧
    dR_metric md e a b c d =
      dWeylTensor4D md e a b c d +
        dRicciCurvaturePart4D md e a b c d +
        dScalarCurvaturePart4D md e a b c d := by
  unfold dWeylTensor4D dRicciScalarRiemannPart4D
  exact ⟨by ring, by ring⟩

/-- Full linearity (`zero`, `add`, `smul`, `sub`) of `dRicciScalarRiemannPart4D`. -/
theorem dRicciScalarRiemannPart4D_linearity (e a b c d : Fin 4) :
    dRicciScalarRiemannPart4D (zeroMetricDerivs 4) e a b c d = 0 ∧
    (∀ md₁ md₂ : MetricDerivs 4,
      dRicciScalarRiemannPart4D (addMetricDerivs md₁ md₂) e a b c d =
        dRicciScalarRiemannPart4D md₁ e a b c d +
          dRicciScalarRiemannPart4D md₂ e a b c d) ∧
    (∀ (r : ℝ) (md : MetricDerivs 4),
      dRicciScalarRiemannPart4D (smulMetricDerivs r md) e a b c d =
        r * dRicciScalarRiemannPart4D md e a b c d) ∧
    (∀ md₁ md₂ : MetricDerivs 4,
      dRicciScalarRiemannPart4D (subMetricDerivs md₁ md₂) e a b c d =
        dRicciScalarRiemannPart4D md₁ e a b c d -
          dRicciScalarRiemannPart4D md₂ e a b c d) := by
  refine ⟨?_, fun md₁ md₂ => ?_, fun r md => ?_, fun md₁ md₂ => ?_⟩
  · unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [dRic_zero, dRic_zero, dRic_zero, dRic_zero, dScalar_zero]
    ring
  · unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [dRic_add, dRic_add, dRic_add, dRic_add, dScalar_add]
    ring
  · unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [dRic_smul, dRic_smul, dRic_smul, dRic_smul, dScalar_smul]
    ring
  · unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [dRic_sub, dRic_sub, dRic_sub, dRic_sub, dScalar_sub]
    ring

/-- Full linearity (`zero`, `add`, `smul`, `sub`) of `dWeylTensor4D`. -/
theorem dWeylTensor4D_linearity (e a b c d : Fin 4) :
    dWeylTensor4D (zeroMetricDerivs 4) e a b c d = 0 ∧
    (∀ md₁ md₂ : MetricDerivs 4,
      dWeylTensor4D (addMetricDerivs md₁ md₂) e a b c d =
        dWeylTensor4D md₁ e a b c d + dWeylTensor4D md₂ e a b c d) ∧
    (∀ (r : ℝ) (md : MetricDerivs 4),
      dWeylTensor4D (smulMetricDerivs r md) e a b c d =
        r * dWeylTensor4D md e a b c d) ∧
    (∀ md₁ md₂ : MetricDerivs 4,
      dWeylTensor4D (subMetricDerivs md₁ md₂) e a b c d =
        dWeylTensor4D md₁ e a b c d - dWeylTensor4D md₂ e a b c d) := by
  have hRS := dRicciScalarRiemannPart4D_linearity e a b c d
  refine ⟨?_, fun md₁ md₂ => ?_, fun r md => ?_, fun md₁ md₂ => ?_⟩
  · unfold dWeylTensor4D
    rw [dR_metric_zero, hRS.1]
    ring
  · unfold dWeylTensor4D
    rw [dR_metric_add, hRS.2.1 md₁ md₂]
    ring
  · unfold dWeylTensor4D
    rw [dR_metric_smul, hRS.2.2.1 r md]
    ring
  · unfold dWeylTensor4D
    rw [dR_metric_sub, hRS.2.2.2 md₁ md₂]
    ring

/-- Algebraic Riemann symmetries and first Bianchi identity of `dWeylTensor4D`
at fixed differentiation index `e`. -/
theorem dWeylTensor4D_algebraic_symmetries (md : MetricDerivs 4) (e a b c d : Fin 4) :
    dWeylTensor4D md e a b c d = -dWeylTensor4D md e b a c d ∧
    dWeylTensor4D md e a b c d = -dWeylTensor4D md e a b d c ∧
    dWeylTensor4D md e a b c d = dWeylTensor4D md e c d a b ∧
    dWeylTensor4D md e a b c d +
      dWeylTensor4D md e b c a d +
      dWeylTensor4D md e c a b d = 0 := by
  have hRS_a1 : dRicciScalarRiemannPart4D md e a b c d =
      -dRicciScalarRiemannPart4D md e b a c d := by
    unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    ring
  have hRS_a2 : dRicciScalarRiemannPart4D md e a b c d =
      -dRicciScalarRiemannPart4D md e a b d c := by
    unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    ring
  have hRS_pair : dRicciScalarRiemannPart4D md e a b c d =
      dRicciScalarRiemannPart4D md e c d a b := by
    unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [minkMetric4D_symm a c, minkMetric4D_symm a d,
      minkMetric4D_symm b c, minkMetric4D_symm b d,
      dRic_symm md sign e b d, dRic_symm md sign e b c,
      dRic_symm md sign e a d, dRic_symm md sign e a c]
    ring
  have hRS_b1 : dRicciScalarRiemannPart4D md e a b c d +
      dRicciScalarRiemannPart4D md e b c a d +
      dRicciScalarRiemannPart4D md e c a b d = 0 := by
    unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [minkMetric4D_symm b a, minkMetric4D_symm c a, minkMetric4D_symm c b,
      dRic_symm md sign e b a, dRic_symm md sign e c a, dRic_symm md sign e c b]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dWeylTensor4D
    rw [dR_metric_antisym1 md e a b c d, hRS_a1]
    ring
  · unfold dWeylTensor4D
    rw [dR_metric_antisym2 md e a b c d, hRS_a2]
    ring
  · unfold dWeylTensor4D
    rw [dR_metric_pair_symm md e a b c d, hRS_pair]
  · have hR := dR_metric_first_bianchi md e a b c d
    unfold dWeylTensor4D
    linarith

/-- The `(1,3)` Lorentzian contraction of `dRicciCurvaturePart4D` equals
`∂_e Ric_{bd} + (1/2) (∂_e R) η_{bd}`. -/
theorem dRicciCurvaturePart4D_trace_13 (md : MetricDerivs 4) (e b d : Fin 4) :
    (∑ a : Fin 4, sign a * dRicciCurvaturePart4D md e a b a d) =
      dRic (riemannFromMetric md) sign e b d +
        (1 / 2) * dScalar (riemannFromMetric md) sign e * minkMetric4D b d := by
  unfold dRicciCurvaturePart4D
  have hterm : ∀ a : Fin 4,
      sign a * ((1 / 2) * (minkMetric4D a a * dRic (riemannFromMetric md) sign e b d -
        minkMetric4D a d * dRic (riemannFromMetric md) sign e b a -
        minkMetric4D b a * dRic (riemannFromMetric md) sign e a d +
        minkMetric4D b d * dRic (riemannFromMetric md) sign e a a)) =
      (1 / 2) * ((sign a * minkMetric4D a a) * dRic (riemannFromMetric md) sign e b d -
        sign a * (minkMetric4D a d * dRic (riemannFromMetric md) sign e b a) -
        sign a * (minkMetric4D b a * dRic (riemannFromMetric md) sign e a d) +
        (sign a * dRic (riemannFromMetric md) sign e a a) * minkMetric4D b d) := by
    intro a; ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  rw [minkMetric4D_lorentzian_trace,
    lorentzian_minkMetric4D_contract_left (fun a => dRic (riemannFromMetric md) sign e b a) d,
    lorentzian_minkMetric4D_contract_right (fun a => dRic (riemannFromMetric md) sign e a d) b]
  change (1 / 2) * (4 * dRic (riemannFromMetric md) sign e b d -
      dRic (riemannFromMetric md) sign e b d -
      dRic (riemannFromMetric md) sign e b d +
      dScalar (riemannFromMetric md) sign e * minkMetric4D b d) =
    dRic (riemannFromMetric md) sign e b d +
      (1 / 2) * dScalar (riemannFromMetric md) sign e * minkMetric4D b d
  ring

/-- The `(1,3)` Lorentzian contraction of `dScalarCurvaturePart4D` equals
`-(1/2) (∂_e R) η_{bd}`. -/
theorem dScalarCurvaturePart4D_trace_13 (md : MetricDerivs 4) (e b d : Fin 4) :
    (∑ a : Fin 4, sign a * dScalarCurvaturePart4D md e a b a d) =
      -(1 / 2) * dScalar (riemannFromMetric md) sign e * minkMetric4D b d := by
  unfold dScalarCurvaturePart4D
  have hterm : ∀ a : Fin 4,
      sign a * (-(1 / 6) * dScalar (riemannFromMetric md) sign e *
        (minkMetric4D a a * minkMetric4D b d - minkMetric4D a d * minkMetric4D b a)) =
      -(1 / 6) * dScalar (riemannFromMetric md) sign e *
        ((sign a * minkMetric4D a a) * minkMetric4D b d -
          sign a * (minkMetric4D a d * minkMetric4D b a)) := by
    intro a; ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [minkMetric4D_lorentzian_trace,
    lorentzian_minkMetric4D_contract_left (fun a => minkMetric4D b a) d,
    minkMetric4D_symm b d]
  ring

/-- The `(1,3)` Lorentzian contraction of `dRicciScalarRiemannPart4D` equals `dRic`,
and the `(1,3)` Lorentzian contraction of `dWeylTensor4D` vanishes identically. -/
theorem dWeylTensor4D_trace_free_13 (md : MetricDerivs 4) (e b d : Fin 4) :
    (∑ a : Fin 4, sign a * dRicciScalarRiemannPart4D md e a b a d) =
      dRic (riemannFromMetric md) sign e b d ∧
    (∑ a : Fin 4, sign a * dWeylTensor4D md e a b a d) = 0 := by
  have hRS : (∑ a : Fin 4, sign a * dRicciScalarRiemannPart4D md e a b a d) =
      dRic (riemannFromMetric md) sign e b d := by
    unfold dRicciScalarRiemannPart4D
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [dRicciCurvaturePart4D_trace_13, dScalarCurvaturePart4D_trace_13]
    ring
  refine ⟨hRS, ?_⟩
  unfold dWeylTensor4D
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hRS]
  change dRic (riemannFromMetric md) sign e b d - dRic (riemannFromMetric md) sign e b d = 0
  ring

/-- **4D Differentiated Weyl Bianchi Identity**: the cyclic sum of `dWeylTensor4D`
over `(e, a, b)` equals the negative cyclic sum of `dRicciScalarRiemannPart4D`:
`∂_e C_{abcd} + ∂_a C_{becd} + ∂_b C_{eacd} + (dRicciScalar_{eabcd} + dRicciScalar_{abecd} + dRicciScalar_{beacd}) = 0`. -/
theorem dWeylTensor4D_second_bianchi_coupling (md : MetricDerivs 4) (e a b c d : Fin 4) :
    (dWeylTensor4D md e a b c d + dWeylTensor4D md a b e c d + dWeylTensor4D md b e a c d) +
      (dRicciScalarRiemannPart4D md e a b c d +
        dRicciScalarRiemannPart4D md a b e c d +
        dRicciScalarRiemannPart4D md b e a c d) = 0 ∧
    dWeylTensor4D md e a b c d + dWeylTensor4D md a b e c d + dWeylTensor4D md b e a c d =
      -(dRicciScalarRiemannPart4D md e a b c d +
        dRicciScalarRiemannPart4D md a b e c d +
        dRicciScalarRiemannPart4D md b e a c d) := by
  have hB := dR_metric_second_bianchi md e a b c d
  unfold dWeylTensor4D
  exact ⟨by linarith, by linarith⟩

/-! ### 4. Conformal Invariance of `dWeylTensor4D` and Vanishing on Conformal Third Jets -/

/-- Exact formula for `dR_metric` on any 4D conformal metric jet `fullConformalMetricDerivs H K`
with symmetric third jet `K`:
`∂_e R_{abcd}(K) = K_{ecb} η_{ad} - K_{eca} η_{bd} - K_{edb} η_{ac} + K_{eda} η_{bc}`. -/
theorem fullConformal_dR_metric_formula (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e a b c d : Fin 4) :
    dR_metric (fullConformalMetricDerivs H K) e a b c d =
      K e c b * minkMetric4D a d - K e c a * minkMetric4D b d -
        K e d b * minkMetric4D a c + K e d a * minkMetric4D b c := by
  simp only [dR_metric, fullConformalMetricDerivs, fullConformalMetricThird,
    minkMetric4D, symmetrizeThirdJet4D_eq_of_symm K hK]
  ring

/-- For any 4D conformal metric jet `fullConformalMetricDerivs H K` with symmetric
third jet `K`, `dRicciScalarRiemannPart4D` equals `dR_metric`, so `dWeylTensor4D`
vanishes identically (`∂_e C_{abcd} = 0`). -/
theorem dWeylTensor4D_fullConformal_eq_zero (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e a b c d : Fin 4) :
    dRicciScalarRiemannPart4D (fullConformalMetricDerivs H K) e a b c d =
      dR_metric (fullConformalMetricDerivs H K) e a b c d ∧
    dWeylTensor4D (fullConformalMetricDerivs H K) e a b c d = 0 := by
  have hdric : ∀ μ ν : Fin 4,
      dRic (riemannFromMetric (fullConformalMetricDerivs H K)) sign e μ ν =
        -2 * K e μ ν - dBox4D K e * minkMetric4D μ ν :=
    fun μ ν => fullDRicci4D_master_formula H K hK e μ ν
  have hdscal :
      dScalar (riemannFromMetric (fullConformalMetricDerivs H K)) sign e =
        -6 * dBox4D K e :=
    fullDScalar4D_master_formula H K hK e
  have hRS : dRicciScalarRiemannPart4D (fullConformalMetricDerivs H K) e a b c d =
      dR_metric (fullConformalMetricDerivs H K) e a b c d := by
    rw [fullConformal_dR_metric_formula H K hK e a b c d]
    unfold dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [hdric b d, hdric b c, hdric a d, hdric a c, hdscal,
      hK.2 e b d, hK.2 e b c, hK.2 e a d, hK.2 e a c]
    ring
  refine ⟨hRS, ?_⟩
  unfold dWeylTensor4D
  rw [hRS, sub_self]

/-- **Conformal Invariance of Differentiated 4D Weyl Curvature**: for every general
4D metric perturbation `md : MetricDerivs 4`, `dWeylTensor4D` vanishes on its
conformal trace part `conformalPartMetricDerivs4D md` and equals `dWeylTensor4D`
of its traceless part `tracelessPartMetricDerivs4D md`. -/
theorem dWeylTensor4D_conformal_invariance (md : MetricDerivs 4) (e a b c d : Fin 4) :
    dWeylTensor4D (conformalPartMetricDerivs4D md) e a b c d = 0 ∧
    dWeylTensor4D md e a b c d =
      dWeylTensor4D (tracelessPartMetricDerivs4D md) e a b c d := by
  have hzero : dWeylTensor4D (conformalPartMetricDerivs4D md) e a b c d = 0 :=
    (dWeylTensor4D_fullConformal_eq_zero
      (metricTraceHessian4D md) (metricTraceThirdJet4D md)
      (metricTraceThirdJet4D_symmetric md) e a b c d).2
  refine ⟨hzero, ?_⟩
  unfold tracelessPartMetricDerivs4D
  rw [(dWeylTensor4D_linearity e a b c d).2.2.2 md (conformalPartMetricDerivs4D md),
    hzero, sub_zero]

/-! ### 5. Differential Curvature on `plusWaveMetricDerivs4D`, `crossWaveMetricDerivs4D`, and `conformalPlusGravitationalWaveMetricDerivs4D` -/

/-- Because `plusWaveMetricDerivs4D A` has vanishing third-derivative jet (`k = 0`),
all of its third-jet curvature operators (`dR_metric`, `dRic`, `divRic`, `dScalar`,
`dEinstein`, `dWeylTensor4D`) vanish identically. -/
theorem plusWave_differential_curvature_zero (A : ℝ) :
    (∀ e a b c d : Fin 4, dR_metric (plusWaveMetricDerivs4D A) e a b c d = 0) ∧
    (∀ e b d : Fin 4, dRic (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e b d = 0) ∧
    (∀ b : Fin 4, divRic (riemannFromMetric (plusWaveMetricDerivs4D A)) sign b = 0) ∧
    (∀ e : Fin 4, dScalar (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e = 0) ∧
    (∀ e b d : Fin 4, dEinstein (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e b d = 0) ∧
    (∀ e a b c d : Fin 4, dWeylTensor4D (plusWaveMetricDerivs4D A) e a b c d = 0) := by
  have hdR : ∀ e a b c d : Fin 4, dR_metric (plusWaveMetricDerivs4D A) e a b c d = 0 := by
    intro e a b c d
    simp only [dR_metric, plusWaveMetricDerivs4D]
    ring
  have hdRic : ∀ e b d : Fin 4,
      dRic (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e b d = 0 := by
    intro e b d
    unfold dRic riemannFromMetric
    dsimp
    apply Finset.sum_eq_zero
    intro a _
    rw [hdR, mul_zero]
  have hdiv : ∀ b : Fin 4,
      divRic (riemannFromMetric (plusWaveMetricDerivs4D A)) sign b = 0 := by
    intro b
    unfold divRic
    apply Finset.sum_eq_zero
    intro e _
    rw [hdRic, mul_zero]
  have hdScal : ∀ e : Fin 4,
      dScalar (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e = 0 := by
    intro e
    unfold dScalar
    apply Finset.sum_eq_zero
    intro b _
    rw [hdRic, mul_zero]
  have hdEin : ∀ e b d : Fin 4,
      dEinstein (riemannFromMetric (plusWaveMetricDerivs4D A)) sign e b d = 0 := by
    intro e b d
    unfold dEinstein
    rw [hdRic, hdScal]
    ring
  have hdW : ∀ e a b c d : Fin 4,
      dWeylTensor4D (plusWaveMetricDerivs4D A) e a b c d = 0 := by
    intro e a b c d
    unfold dWeylTensor4D dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [hdR, hdRic, hdRic, hdRic, hdRic, hdScal]
    ring
  exact ⟨hdR, hdRic, hdiv, hdScal, hdEin, hdW⟩

/-- Because `crossWaveMetricDerivs4D B` has vanishing third-derivative jet (`k = 0`),
all of its third-jet curvature operators (`dR_metric`, `dRic`, `divRic`, `dScalar`,
`dEinstein`, `dWeylTensor4D`) vanish identically. -/
theorem crossWave_differential_curvature_zero (B : ℝ) :
    (∀ e a b c d : Fin 4, dR_metric (crossWaveMetricDerivs4D B) e a b c d = 0) ∧
    (∀ e b d : Fin 4, dRic (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e b d = 0) ∧
    (∀ b : Fin 4, divRic (riemannFromMetric (crossWaveMetricDerivs4D B)) sign b = 0) ∧
    (∀ e : Fin 4, dScalar (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e = 0) ∧
    (∀ e b d : Fin 4, dEinstein (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e b d = 0) ∧
    (∀ e a b c d : Fin 4, dWeylTensor4D (crossWaveMetricDerivs4D B) e a b c d = 0) := by
  have hdR : ∀ e a b c d : Fin 4, dR_metric (crossWaveMetricDerivs4D B) e a b c d = 0 := by
    intro e a b c d
    simp only [dR_metric, crossWaveMetricDerivs4D]
    ring
  have hdRic : ∀ e b d : Fin 4,
      dRic (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e b d = 0 := by
    intro e b d
    unfold dRic riemannFromMetric
    dsimp
    apply Finset.sum_eq_zero
    intro a _
    rw [hdR, mul_zero]
  have hdiv : ∀ b : Fin 4,
      divRic (riemannFromMetric (crossWaveMetricDerivs4D B)) sign b = 0 := by
    intro b
    unfold divRic
    apply Finset.sum_eq_zero
    intro e _
    rw [hdRic, mul_zero]
  have hdScal : ∀ e : Fin 4,
      dScalar (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e = 0 := by
    intro e
    unfold dScalar
    apply Finset.sum_eq_zero
    intro b _
    rw [hdRic, mul_zero]
  have hdEin : ∀ e b d : Fin 4,
      dEinstein (riemannFromMetric (crossWaveMetricDerivs4D B)) sign e b d = 0 := by
    intro e b d
    unfold dEinstein
    rw [hdRic, hdScal]
    ring
  have hdW : ∀ e a b c d : Fin 4,
      dWeylTensor4D (crossWaveMetricDerivs4D B) e a b c d = 0 := by
    intro e a b c d
    unfold dWeylTensor4D dRicciScalarRiemannPart4D dRicciCurvaturePart4D dScalarCurvaturePart4D
    rw [hdR, hdRic, hdRic, hdRic, hdRic, hdScal]
    ring
  exact ⟨hdR, hdRic, hdiv, hdScal, hdEin, hdW⟩

/-- For any combined conformal-plus-gravitational-wave perturbation
`md = conformalPlusGravitationalWaveMetricDerivs4D H K A B`, its third-jet
curvature operators `dR_metric`, `dRic`, `divRic`, `dScalar`, and `dEinstein`
coincide identically with those of the conformal sector `fullConformalMetricDerivs H K`. -/
theorem conformalPlusGravitationalWave_differential_curvature
    (H : Hessian4D) (K : ThirdJet4D) (A B : ℝ) :
    let md := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    (∀ e a b c d : Fin 4,
      dR_metric md e a b c d = dR_metric (fullConformalMetricDerivs H K) e a b c d) ∧
    (∀ e b d : Fin 4,
      dRic (riemannFromMetric md) sign e b d = fullDRicci4D H K e b d) ∧
    (∀ b : Fin 4,
      divRic (riemannFromMetric md) sign b =
        divRic (riemannFromMetric (fullConformalMetricDerivs H K)) sign b) ∧
    (∀ e : Fin 4,
      dScalar (riemannFromMetric md) sign e = fullDScalar4D H K e) ∧
    (∀ e b d : Fin 4,
      dEinstein (riemannFromMetric md) sign e b d = fullDEinstein4D H K e b d) := by
  intro md
  have hp := plusWave_differential_curvature_zero A
  have hc := crossWave_differential_curvature_zero B
  refine ⟨fun e a b c d => ?_, fun e b d => ?_, fun b => ?_, fun e => ?_, fun e b d => ?_⟩
  · unfold md conformalPlusGravitationalWaveMetricDerivs4D
    rw [dR_metric_add, dR_metric_add, hp.1, hc.1]; ring
  · unfold md conformalPlusGravitationalWaveMetricDerivs4D fullDRicci4D
    rw [dRic_add, dRic_add, hp.2.1, hc.2.1]; ring
  · unfold md conformalPlusGravitationalWaveMetricDerivs4D
    rw [divRic_add, divRic_add, hp.2.2.1, hc.2.2.1]; ring
  · unfold md conformalPlusGravitationalWaveMetricDerivs4D fullDScalar4D
    rw [dScalar_add, dScalar_add, hp.2.2.2.1, hc.2.2.2.1]; ring
  · unfold md conformalPlusGravitationalWaveMetricDerivs4D fullDEinstein4D
    rw [dEinstein_add, dEinstein_add, hp.2.2.2.2.1, hc.2.2.2.2.1]; ring

/-- **Master Differential Bianchi & Channel Cancellation Theorem for Combined
Conformal-Plus-Gravitational-Wave Perturbations**: for any `H : Hessian4D`,
symmetric `K : ThirdJet4D`, and gravitational-wave amplitudes `A, B : ℝ`:
1. `∂_e G_{bd}(md) = -2 K_{ebd} + 2 (□ ∂_e Ω) η_{bd}`,
2. `2 * divRic(md)_b = ∂_b R(md) = -6 (□ ∂_b Ω)`,
3. The Lorentzian divergence `∑ e, sign e * ∂_e G_{νe}(md)` splits into the
   diagonal channel `2 * ∑_{e ≠ ν} sign e * K ν e e` and the off-diagonal
   shear/flux channel `-2 * ∑_{e ≠ ν} sign e * K ν e e`, which cancel identically to `0`. -/
theorem conformalPlusGravitationalWave_bianchi_conservation_master
    (H : Hessian4D) (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K) (A B : ℝ) (ν : Fin 4) :
    let md := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    (∀ e b d : Fin 4,
      dEinstein (riemannFromMetric md) sign e b d =
        -2 * K e b d + 2 * dBox4D K e * minkMetric4D b d) ∧
    2 * divRic (riemannFromMetric md) sign ν = -6 * dBox4D K ν ∧
    (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) =
      bianchiDiagonalChannel4D H K ν + bianchiOffDiagonalChannel4D H K ν ∧
    bianchiDiagonalChannel4D H K ν =
      2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e ∧
    bianchiOffDiagonalChannel4D H K ν =
      -2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e ∧
    (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) = 0 := by
  intro md
  have hdiff := conformalPlusGravitationalWave_differential_curvature H K A B
  have hchan := bianchi_diagonal_offDiagonal_channel_decomposition H K hK ν
  refine ⟨fun e b d => ?_, ?_, ?_, hchan.2.1, hchan.2.2.1, ?_⟩
  · rw [hdiff.2.2.2.2 e b d]
    exact fullDEinstein4D_master_formula H K hK e b d
  · rw [dRic_contracted_bianchi md sign ν, hdiff.2.2.2.1 ν]
    exact fullDScalar4D_master_formula H K hK ν
  · have hsum : (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) =
        ∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hdiff.2.2.2.2 e ν e]
    rw [hsum]
    exact hchan.1
  · exact (dEinstein_lorentzian_divergence_zero md ν).1

#print axioms dRic_zero
#print axioms divRic_zero
#print axioms divRic_add
#print axioms divRic_smul
#print axioms divRic_sub
#print axioms dScalar_zero
#print axioms dEinstein_zero
#print axioms dR_metric_antisym1
#print axioms dR_metric_antisym2
#print axioms dR_metric_pair_symm
#print axioms dR_metric_first_bianchi
#print axioms dR_metric_second_bianchi
#print axioms dRic_symm
#print axioms dEinstein_symm
#print axioms dR_metric_once_contracted
#print axioms dRic_contracted_bianchi
#print axioms dEinstein_lorentzian_divergence_zero
#print axioms dR_metric_eq_dWeyl_add_dRicciScalar
#print axioms dRicciScalarRiemannPart4D_linearity
#print axioms dWeylTensor4D_linearity
#print axioms dWeylTensor4D_algebraic_symmetries
#print axioms dRicciCurvaturePart4D_trace_13
#print axioms dScalarCurvaturePart4D_trace_13
#print axioms dWeylTensor4D_trace_free_13
#print axioms dWeylTensor4D_second_bianchi_coupling
#print axioms fullConformal_dR_metric_formula
#print axioms dWeylTensor4D_fullConformal_eq_zero
#print axioms dWeylTensor4D_conformal_invariance
#print axioms plusWave_differential_curvature_zero
#print axioms crossWave_differential_curvature_zero
#print axioms conformalPlusGravitationalWave_differential_curvature
#print axioms conformalPlusGravitationalWave_bianchi_conservation_master

end
end UnifiedTheory.Audit.KFCausalCurved4DDifferentialBianchiIdentity
