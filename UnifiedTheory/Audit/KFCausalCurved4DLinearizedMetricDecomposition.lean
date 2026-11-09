import UnifiedTheory.Audit.KFCausalConformal4DCurvedDiamondMasterSynthesis

/-! Vector-space algebra, exact operator linearity, Lorentzian trace extraction,
and conformal/traceless jet projection for general 4D linearized metric
perturbations `MetricDerivs 4`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DLinearizedMetricDecomposition
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic dScalar dEinstein)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D symmetrizeHessian4D symmetrizeThirdJet4D
  minkMetric4D box4D dBox4D fullConformalMetricSecond fullConformalMetricThird
  fullConformalMetricDerivs zeroThirdJet4D fullRicciTensor4D fullScalarCurvature4D
  fullEinsteinTensor4D fullEinsteinTrace4D fullDRicci4D fullDScalar4D fullDEinstein4D
  symmetrizeHessian4D_eq_of_symm symmetrizeThirdJet4D_eq_of_symm minkMetric4D_diag)

variable {n : ℕ}

/-- Zero metric perturbation jet in dimension `n`. -/
def zeroMetricDerivs (n : ℕ) : MetricDerivs n where
  h := fun _ _ _ _ => 0
  h_metric := fun _ _ _ _ => rfl
  h_comm := fun _ _ _ _ => rfl
  k := fun _ _ _ _ _ => 0
  k_metric := fun _ _ _ _ _ => rfl
  k_sym12 := fun _ _ _ _ _ => rfl
  k_sym23 := fun _ _ _ _ _ => rfl

/-- Pointwise sum of two metric perturbation jets in dimension `n`. -/
def addMetricDerivs (md₁ md₂ : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => md₁.h e f a b + md₂.h e f a b
  h_metric := fun e f a b => by rw [md₁.h_metric, md₂.h_metric]
  h_comm := fun e f a b => by rw [md₁.h_comm, md₂.h_comm]
  k := fun e f g a b => md₁.k e f g a b + md₂.k e f g a b
  k_metric := fun e f g a b => by rw [md₁.k_metric, md₂.k_metric]
  k_sym12 := fun e f g a b => by rw [md₁.k_sym12, md₂.k_sym12]
  k_sym23 := fun e f g a b => by rw [md₁.k_sym23, md₂.k_sym23]

/-- Scalar multiplication of a metric perturbation jet by `c : ℝ`. -/
def smulMetricDerivs (c : ℝ) (md : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => c * md.h e f a b
  h_metric := fun e f a b => by rw [md.h_metric]
  h_comm := fun e f a b => by rw [md.h_comm]
  k := fun e f g a b => c * md.k e f g a b
  k_metric := fun e f g a b => by rw [md.k_metric]
  k_sym12 := fun e f g a b => by rw [md.k_sym12]
  k_sym23 := fun e f g a b => by rw [md.k_sym23]

/-- Pointwise negation of a metric perturbation jet. -/
def negMetricDerivs (md : MetricDerivs n) : MetricDerivs n :=
  smulMetricDerivs (-1) md

/-- Pointwise difference of two metric perturbation jets in dimension `n`. -/
def subMetricDerivs (md₁ md₂ : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => md₁.h e f a b - md₂.h e f a b
  h_metric := fun e f a b => by rw [md₁.h_metric, md₂.h_metric]
  h_comm := fun e f a b => by rw [md₁.h_comm, md₂.h_comm]
  k := fun e f g a b => md₁.k e f g a b - md₂.k e f g a b
  k_metric := fun e f g a b => by rw [md₁.k_metric, md₂.k_metric]
  k_sym12 := fun e f g a b => by rw [md₁.k_sym12, md₂.k_sym12]
  k_sym23 := fun e f g a b => by rw [md₁.k_sym23, md₂.k_sym23]

/-- Finite linear combination `∑ i ∈ s, c i • md i` of metric perturbation jets. -/
def finsetSumMetricDerivs {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (md : ι → MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => ∑ i ∈ s, c i * (md i).h e f a b
  h_metric := fun e f a b => by
    apply Finset.sum_congr rfl
    intro i _
    rw [(md i).h_metric]
  h_comm := fun e f a b => by
    apply Finset.sum_congr rfl
    intro i _
    rw [(md i).h_comm]
  k := fun e f g a b => ∑ i ∈ s, c i * (md i).k e f g a b
  k_metric := fun e f g a b => by
    apply Finset.sum_congr rfl
    intro i _
    rw [(md i).k_metric]
  k_sym12 := fun e f g a b => by
    apply Finset.sum_congr rfl
    intro i _
    rw [(md i).k_sym12]
  k_sym23 := fun e f g a b => by
    apply Finset.sum_congr rfl
    intro i _
    rw [(md i).k_sym23]

/-! ### Linearity of Riemann, Ricci, Scalar, Einstein, and their derivatives -/

theorem R_metric_zero (a b c d : Fin n) :
    R_metric (zeroMetricDerivs n) a b c d = 0 := by
  simp [R_metric, zeroMetricDerivs]

theorem R_metric_add (md₁ md₂ : MetricDerivs n) (a b c d : Fin n) :
    R_metric (addMetricDerivs md₁ md₂) a b c d =
      R_metric md₁ a b c d + R_metric md₂ a b c d := by
  simp only [R_metric, addMetricDerivs]
  ring

theorem R_metric_smul (r : ℝ) (md : MetricDerivs n) (a b c d : Fin n) :
    R_metric (smulMetricDerivs r md) a b c d = r * R_metric md a b c d := by
  simp only [R_metric, smulMetricDerivs]
  ring

theorem R_metric_sub (md₁ md₂ : MetricDerivs n) (a b c d : Fin n) :
    R_metric (subMetricDerivs md₁ md₂) a b c d =
      R_metric md₁ a b c d - R_metric md₂ a b c d := by
  simp only [R_metric, subMetricDerivs]
  ring

theorem R_metric_finsetSum {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (md : ι → MetricDerivs n) (a b c d : Fin n) :
    R_metric (finsetSumMetricDerivs s coeff md) a b c d =
      ∑ i ∈ s, coeff i * R_metric (md i) a b c d := by
  simp only [R_metric, finsetSumMetricDerivs]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dR_metric_zero (e a b c d : Fin n) :
    dR_metric (zeroMetricDerivs n) e a b c d = 0 := by
  simp [dR_metric, zeroMetricDerivs]

theorem dR_metric_add (md₁ md₂ : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (addMetricDerivs md₁ md₂) e a b c d =
      dR_metric md₁ e a b c d + dR_metric md₂ e a b c d := by
  simp only [dR_metric, addMetricDerivs]
  ring

theorem dR_metric_smul (r : ℝ) (md : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (smulMetricDerivs r md) e a b c d = r * dR_metric md e a b c d := by
  simp only [dR_metric, smulMetricDerivs]
  ring

theorem dR_metric_sub (md₁ md₂ : MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (subMetricDerivs md₁ md₂) e a b c d =
      dR_metric md₁ e a b c d - dR_metric md₂ e a b c d := by
  simp only [dR_metric, subMetricDerivs]
  ring

theorem dR_metric_finsetSum {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (md : ι → MetricDerivs n) (e a b c d : Fin n) :
    dR_metric (finsetSumMetricDerivs s coeff md) e a b c d =
      ∑ i ∈ s, coeff i * dR_metric (md i) e a b c d := by
  simp only [dR_metric, finsetSumMetricDerivs]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ricci_zero (w : Fin n → ℝ) (b d : Fin n) :
    ricci (zeroMetricDerivs n) w b d = 0 := by
  unfold ricci
  apply Finset.sum_eq_zero
  intro a _
  rw [R_metric_zero, mul_zero]

theorem ricci_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    ricci (addMetricDerivs md₁ md₂) w b d =
      ricci md₁ w b d + ricci md₂ w b d := by
  unfold ricci
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [R_metric_add]
  ring

theorem ricci_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    ricci (smulMetricDerivs r md) w b d = r * ricci md w b d := by
  unfold ricci
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [R_metric_smul]
  ring

theorem ricci_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    ricci (subMetricDerivs md₁ md₂) w b d =
      ricci md₁ w b d - ricci md₂ w b d := by
  unfold ricci
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [R_metric_sub]
  ring

theorem ricci_finsetSum {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (md : ι → MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    ricci (finsetSumMetricDerivs s coeff md) w b d =
      ∑ i ∈ s, coeff i * ricci (md i) w b d := by
  unfold ricci
  simp_rw [R_metric_finsetSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scalar_zero (w : Fin n → ℝ) :
    scalar (zeroMetricDerivs n) w = 0 := by
  unfold scalar
  apply Finset.sum_eq_zero
  intro b _
  rw [ricci_zero, mul_zero]

theorem scalar_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) :
    scalar (addMetricDerivs md₁ md₂) w =
      scalar md₁ w + scalar md₂ w := by
  unfold scalar
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [ricci_add]
  ring

theorem scalar_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) :
    scalar (smulMetricDerivs r md) w = r * scalar md w := by
  unfold scalar
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [ricci_smul]
  ring

theorem scalar_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) :
    scalar (subMetricDerivs md₁ md₂) w =
      scalar md₁ w - scalar md₂ w := by
  unfold scalar
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [ricci_sub]
  ring

theorem scalar_finsetSum {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (md : ι → MetricDerivs n) (w : Fin n → ℝ) :
    scalar (finsetSumMetricDerivs s coeff md) w =
      ∑ i ∈ s, coeff i * scalar (md i) w := by
  unfold scalar
  simp_rw [ricci_finsetSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem einstein_zero (w : Fin n → ℝ) (b d : Fin n) :
    einstein (zeroMetricDerivs n) w b d = 0 := by
  unfold einstein
  rw [ricci_zero, scalar_zero]
  ring

theorem einstein_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    einstein (addMetricDerivs md₁ md₂) w b d =
      einstein md₁ w b d + einstein md₂ w b d := by
  unfold einstein
  rw [ricci_add, scalar_add]
  ring

theorem einstein_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    einstein (smulMetricDerivs r md) w b d = r * einstein md w b d := by
  unfold einstein
  rw [ricci_smul, scalar_smul]
  ring

theorem einstein_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    einstein (subMetricDerivs md₁ md₂) w b d =
      einstein md₁ w b d - einstein md₂ w b d := by
  unfold einstein
  rw [ricci_sub, scalar_sub]
  ring

theorem einstein_finsetSum {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (md : ι → MetricDerivs n) (w : Fin n → ℝ) (b d : Fin n) :
    einstein (finsetSumMetricDerivs s coeff md) w b d =
      ∑ i ∈ s, coeff i * einstein (md i) w b d := by
  unfold einstein
  rw [ricci_finsetSum, scalar_finsetSum, Finset.sum_div, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dRic_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dRic (riemannFromMetric (addMetricDerivs md₁ md₂)) w e b d =
      dRic (riemannFromMetric md₁) w e b d + dRic (riemannFromMetric md₂) w e b d := by
  unfold dRic riemannFromMetric
  dsimp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [dR_metric_add]
  ring

theorem dRic_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dRic (riemannFromMetric (smulMetricDerivs r md)) w e b d =
      r * dRic (riemannFromMetric md) w e b d := by
  unfold dRic riemannFromMetric
  dsimp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [dR_metric_smul]
  ring

theorem dRic_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dRic (riemannFromMetric (subMetricDerivs md₁ md₂)) w e b d =
      dRic (riemannFromMetric md₁) w e b d - dRic (riemannFromMetric md₂) w e b d := by
  unfold dRic riemannFromMetric
  dsimp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [dR_metric_sub]
  ring

theorem dScalar_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e : Fin n) :
    dScalar (riemannFromMetric (addMetricDerivs md₁ md₂)) w e =
      dScalar (riemannFromMetric md₁) w e + dScalar (riemannFromMetric md₂) w e := by
  unfold dScalar
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [dRic_add]
  ring

theorem dScalar_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (e : Fin n) :
    dScalar (riemannFromMetric (smulMetricDerivs r md)) w e =
      r * dScalar (riemannFromMetric md) w e := by
  unfold dScalar
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [dRic_smul]
  ring

theorem dScalar_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e : Fin n) :
    dScalar (riemannFromMetric (subMetricDerivs md₁ md₂)) w e =
      dScalar (riemannFromMetric md₁) w e - dScalar (riemannFromMetric md₂) w e := by
  unfold dScalar
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [dRic_sub]
  ring

theorem dEinstein_add (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dEinstein (riemannFromMetric (addMetricDerivs md₁ md₂)) w e b d =
      dEinstein (riemannFromMetric md₁) w e b d +
        dEinstein (riemannFromMetric md₂) w e b d := by
  unfold dEinstein
  rw [dRic_add, dScalar_add]
  ring

theorem dEinstein_smul (r : ℝ) (md : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dEinstein (riemannFromMetric (smulMetricDerivs r md)) w e b d =
      r * dEinstein (riemannFromMetric md) w e b d := by
  unfold dEinstein
  rw [dRic_smul, dScalar_smul]
  ring

theorem dEinstein_sub (md₁ md₂ : MetricDerivs n) (w : Fin n → ℝ) (e b d : Fin n) :
    dEinstein (riemannFromMetric (subMetricDerivs md₁ md₂)) w e b d =
      dEinstein (riemannFromMetric md₁) w e b d -
        dEinstein (riemannFromMetric md₂) w e b d := by
  unfold dEinstein
  rw [dRic_sub, dScalar_sub]
  ring

/-! ### 4D Lorentzian Metric-Trace Hessian, Third-Jet, and Conformal/Traceless Split -/

private theorem sign_sq_one (a : Fin 4) : sign a * sign a = 1 := by
  simp only [sign]
  split_ifs <;> norm_num

/-- The 4D Lorentzian trace `∑ a, sign a * minkMetric4D a a` of the flat
Minkowski metric equals `4`. -/
theorem minkMetric4D_lorentzian_trace :
    (∑ a : Fin 4, sign a * minkMetric4D a a) = 4 := by
  have hterm : ∀ a : Fin 4, sign a * minkMetric4D a a = 1 := by
    intro a
    rw [minkMetric4D_diag, sign_sq_one]
  simp_rw [hterm]
  norm_num

/-- Raw Lorentzian metric-trace second-derivative matrix
`Tr_η(∂_e ∂_f h) = ∑ a, sign a * md.h e f a a`. -/
def lorentzianMetricTrace4D (md : MetricDerivs 4) : Hessian4D :=
  fun e f => ∑ a : Fin 4, sign a * md.h e f a a

/-- Raw Lorentzian metric-trace third-derivative tensor
`Tr_η(∂_e ∂_f ∂_g h) = ∑ a, sign a * md.k e f g a a`. -/
def lorentzianMetricThirdTrace4D (md : MetricDerivs 4) : ThirdJet4D :=
  fun e f g => ∑ a : Fin 4, sign a * md.k e f g a a

/-- Extracted 4D conformal-factor Hessian `H_{ef} = (1/8) ∑ a, sign a * md.h e f a a`
(since `fullConformalMetricSecond H e f a b = 2 * H_{ef} * η_{ab}` has trace `8 * H_{ef}`). -/
def metricTraceHessian4D (md : MetricDerivs 4) : Hessian4D :=
  fun e f => (1 / 8) * lorentzianMetricTrace4D md e f

/-- Extracted 4D conformal-factor third jet `K_{efg} = (1/8) ∑ a, sign a * md.k e f g a a`. -/
def metricTraceThirdJet4D (md : MetricDerivs 4) : ThirdJet4D :=
  fun e f g => (1 / 8) * lorentzianMetricThirdTrace4D md e f g

/-- The Lorentzian metric-trace Hessian `metricTraceHessian4D md` is symmetric
for every `md : MetricDerivs 4`. -/
theorem metricTraceHessian4D_symmetric (md : MetricDerivs 4) :
    IsSymmetricHessian4D (metricTraceHessian4D md) := by
  intro e f
  unfold metricTraceHessian4D lorentzianMetricTrace4D
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [md.h_comm e f a a]

/-- The Lorentzian metric-trace third jet `metricTraceThirdJet4D md` is fully
symmetric in all 3 derivative indices for every `md : MetricDerivs 4`. -/
theorem metricTraceThirdJet4D_symmetric (md : MetricDerivs 4) :
    IsSymmetricThirdJet4D (metricTraceThirdJet4D md) := by
  refine ⟨?_, ?_⟩
  · intro e f g
    unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [md.k_sym12 e f g a a]
  · intro e f g
    unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [md.k_sym23 e f g a a]

/-- Conformal (pure-trace) part of a general 4D metric perturbation jet `md`,
constructed as `fullConformalMetricDerivs (metricTraceHessian4D md) (metricTraceThirdJet4D md)`. -/
def conformalPartMetricDerivs4D (md : MetricDerivs 4) : MetricDerivs 4 :=
  fullConformalMetricDerivs (metricTraceHessian4D md) (metricTraceThirdJet4D md)

/-- Traceless (non-conformal) part of a general 4D metric perturbation jet `md`,
obtained by subtracting its conformal trace part. -/
def tracelessPartMetricDerivs4D (md : MetricDerivs 4) : MetricDerivs 4 :=
  subMetricDerivs md (conformalPartMetricDerivs4D md)

/-- Explicit formula for the second-derivative components of `conformalPartMetricDerivs4D md`:
`(conformalPartMetricDerivs4D md).h e f a b = 2 * metricTraceHessian4D md e f * minkMetric4D a b`
`= (1 / 4) * (∑ c, sign c * md.h e f c c) * minkMetric4D a b`. -/
theorem conformalPartMetricDerivs4D_h_eq (md : MetricDerivs 4) (e f a b : Fin 4) :
    (conformalPartMetricDerivs4D md).h e f a b =
      2 * metricTraceHessian4D md e f * minkMetric4D a b ∧
    (conformalPartMetricDerivs4D md).h e f a b =
      (1 / 4) * (∑ c : Fin 4, sign c * md.h e f c c) * minkMetric4D a b := by
  have h1 : (conformalPartMetricDerivs4D md).h e f a b =
      2 * metricTraceHessian4D md e f * minkMetric4D a b := by
    simp only [conformalPartMetricDerivs4D, fullConformalMetricDerivs,
      fullConformalMetricSecond, minkMetric4D,
      symmetrizeHessian4D_eq_of_symm _ (metricTraceHessian4D_symmetric md)]
  refine ⟨h1, ?_⟩
  rw [h1]
  unfold metricTraceHessian4D lorentzianMetricTrace4D
  ring

/-- Explicit formula for the third-derivative components of `conformalPartMetricDerivs4D md`:
`(conformalPartMetricDerivs4D md).k e f g a b = 2 * metricTraceThirdJet4D md e f g * minkMetric4D a b`
`= (1 / 4) * (∑ c, sign c * md.k e f g c c) * minkMetric4D a b`. -/
theorem conformalPartMetricDerivs4D_k_eq (md : MetricDerivs 4) (e f g a b : Fin 4) :
    (conformalPartMetricDerivs4D md).k e f g a b =
      2 * metricTraceThirdJet4D md e f g * minkMetric4D a b ∧
    (conformalPartMetricDerivs4D md).k e f g a b =
      (1 / 4) * (∑ c : Fin 4, sign c * md.k e f g c c) * minkMetric4D a b := by
  have h1 : (conformalPartMetricDerivs4D md).k e f g a b =
      2 * metricTraceThirdJet4D md e f g * minkMetric4D a b := by
    simp only [conformalPartMetricDerivs4D, fullConformalMetricDerivs,
      fullConformalMetricThird, minkMetric4D,
      symmetrizeThirdJet4D_eq_of_symm _ (metricTraceThirdJet4D_symmetric md)]
  refine ⟨h1, ?_⟩
  rw [h1]
  unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
  ring

/-- Exact decomposition of any 4D metric perturbation jet `md` into its
conformal trace part and its traceless part. -/
theorem metricDerivs4D_conformal_traceless_decomposition (md : MetricDerivs 4) :
    (∀ e f a b : Fin 4,
      md.h e f a b =
        (conformalPartMetricDerivs4D md).h e f a b +
          (tracelessPartMetricDerivs4D md).h e f a b) ∧
    (∀ e f g a b : Fin 4,
      md.k e f g a b =
        (conformalPartMetricDerivs4D md).k e f g a b +
          (tracelessPartMetricDerivs4D md).k e f g a b) := by
  refine ⟨fun e f a b => ?_, fun e f g a b => ?_⟩
  · simp only [tracelessPartMetricDerivs4D, subMetricDerivs]; ring
  · simp only [tracelessPartMetricDerivs4D, subMetricDerivs]; ring

/-- The conformal part `conformalPartMetricDerivs4D md` has the exact same
Lorentzian metric trace as `md`. -/
theorem lorentzianMetricTrace4D_conformalPart (md : MetricDerivs 4) (e f : Fin 4) :
    lorentzianMetricTrace4D (conformalPartMetricDerivs4D md) e f =
      lorentzianMetricTrace4D md e f ∧
    (∀ g : Fin 4,
      lorentzianMetricThirdTrace4D (conformalPartMetricDerivs4D md) e f g =
        lorentzianMetricThirdTrace4D md e f g) := by
  refine ⟨?_, ?_⟩
  · unfold lorentzianMetricTrace4D
    have hdiag : ∀ a : Fin 4,
        (conformalPartMetricDerivs4D md).h e f a a =
          2 * metricTraceHessian4D md e f * minkMetric4D a a :=
      fun a => (conformalPartMetricDerivs4D_h_eq md e f a a).1
    simp_rw [hdiag]
    have hpull : (∑ a : Fin 4,
        sign a * (2 * metricTraceHessian4D md e f * minkMetric4D a a)) =
        2 * metricTraceHessian4D md e f *
          (∑ a : Fin 4, sign a * minkMetric4D a a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hpull, minkMetric4D_lorentzian_trace]
    unfold metricTraceHessian4D lorentzianMetricTrace4D
    ring
  · intro g
    unfold lorentzianMetricThirdTrace4D
    have hdiag : ∀ a : Fin 4,
        (conformalPartMetricDerivs4D md).k e f g a a =
          2 * metricTraceThirdJet4D md e f g * minkMetric4D a a :=
      fun a => (conformalPartMetricDerivs4D_k_eq md e f g a a).1
    simp_rw [hdiag]
    have hpull : (∑ a : Fin 4,
        sign a * (2 * metricTraceThirdJet4D md e f g * minkMetric4D a a)) =
        2 * metricTraceThirdJet4D md e f g *
          (∑ a : Fin 4, sign a * minkMetric4D a a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hpull, minkMetric4D_lorentzian_trace]
    unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
    ring

/-- The traceless part `tracelessPartMetricDerivs4D md` has identically zero
Lorentzian metric trace in both second and third derivatives. -/
theorem tracelessPartMetricDerivs4D_trace_free (md : MetricDerivs 4) :
    (∀ e f : Fin 4,
      (∑ a : Fin 4, sign a * (tracelessPartMetricDerivs4D md).h e f a a) = 0) ∧
    (∀ e f g : Fin 4,
      (∑ a : Fin 4, sign a * (tracelessPartMetricDerivs4D md).k e f g a a) = 0) := by
  refine ⟨fun e f => ?_, fun e f g => ?_⟩
  · have htr := (lorentzianMetricTrace4D_conformalPart md e f).1
    unfold lorentzianMetricTrace4D at htr
    simp only [tracelessPartMetricDerivs4D, subMetricDerivs, mul_sub,
      Finset.sum_sub_distrib, htr, sub_self]
  · have htr := (lorentzianMetricTrace4D_conformalPart md e f).2 g
    unfold lorentzianMetricThirdTrace4D at htr
    simp only [tracelessPartMetricDerivs4D, subMetricDerivs, mul_sub,
      Finset.sum_sub_distrib, htr, sub_self]

/-- On any pure conformal metric jet `fullConformalMetricDerivs H K` with symmetric
`H` and `K`, `metricTraceHessian4D` and `metricTraceThirdJet4D` recover `H` and `K`. -/
theorem metricTrace_of_fullConformalMetricDerivs (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K) :
    (∀ e f : Fin 4,
      metricTraceHessian4D (fullConformalMetricDerivs H K) e f = H e f) ∧
    (∀ e f g : Fin 4,
      metricTraceThirdJet4D (fullConformalMetricDerivs H K) e f g = K e f g) := by
  refine ⟨fun e f => ?_, fun e f g => ?_⟩
  · unfold metricTraceHessian4D lorentzianMetricTrace4D
    simp only [fullConformalMetricDerivs, fullConformalMetricSecond,
      symmetrizeHessian4D_eq_of_symm H hH]
    have hpull : (∑ a : Fin 4, sign a * (2 * H e f * eta a a)) =
        2 * H e f * (∑ a : Fin 4, sign a * minkMetric4D a a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      unfold minkMetric4D
      ring
    rw [hpull, minkMetric4D_lorentzian_trace]
    ring
  · unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
    simp only [fullConformalMetricDerivs, fullConformalMetricThird,
      symmetrizeThirdJet4D_eq_of_symm K hK]
    have hpull : (∑ a : Fin 4, sign a * (2 * K e f g * eta a a)) =
        2 * K e f g * (∑ a : Fin 4, sign a * minkMetric4D a a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      unfold minkMetric4D
      ring
    rw [hpull, minkMetric4D_lorentzian_trace]
    ring

/-- Idempotence and orthogonality of the conformal/traceless projection on
`MetricDerivs 4`. -/
theorem metricTrace_projection_idempotent_and_orthogonal (md : MetricDerivs 4) :
    metricTraceHessian4D (conformalPartMetricDerivs4D md) = metricTraceHessian4D md ∧
    (∀ e f : Fin 4, metricTraceHessian4D (tracelessPartMetricDerivs4D md) e f = 0) ∧
    metricTraceThirdJet4D (conformalPartMetricDerivs4D md) = metricTraceThirdJet4D md ∧
    (∀ e f g : Fin 4, metricTraceThirdJet4D (tracelessPartMetricDerivs4D md) e f g = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext e f
    unfold metricTraceHessian4D
    rw [(lorentzianMetricTrace4D_conformalPart md e f).1]
  · intro e f
    unfold metricTraceHessian4D lorentzianMetricTrace4D
    rw [(tracelessPartMetricDerivs4D_trace_free md).1 e f, mul_zero]
  · funext e f g
    unfold metricTraceThirdJet4D
    rw [(lorentzianMetricTrace4D_conformalPart md e f).2 g]
  · intro e f g
    unfold metricTraceThirdJet4D lorentzianMetricThirdTrace4D
    rw [(tracelessPartMetricDerivs4D_trace_free md).2 e f g, mul_zero]

/-- Exact curvature decomposition across the conformal/traceless split of any
4D metric perturbation `md : MetricDerivs 4`. -/
theorem curvature_conformal_traceless_split (md : MetricDerivs 4) :
    (∀ a b c d : Fin 4,
      R_metric md a b c d =
        R_metric (conformalPartMetricDerivs4D md) a b c d +
          R_metric (tracelessPartMetricDerivs4D md) a b c d) ∧
    (∀ b d : Fin 4,
      ricci md sign b d =
        fullRicciTensor4D (metricTraceHessian4D md) b d +
          ricci (tracelessPartMetricDerivs4D md) sign b d) ∧
    (scalar md sign =
      fullScalarCurvature4D (metricTraceHessian4D md) +
        scalar (tracelessPartMetricDerivs4D md) sign) ∧
    (∀ b d : Fin 4,
      einstein md sign b d =
        fullEinsteinTensor4D (metricTraceHessian4D md) b d +
          einstein (tracelessPartMetricDerivs4D md) sign b d) := by
  have hR : ∀ a b c d : Fin 4,
      R_metric md a b c d =
        R_metric (conformalPartMetricDerivs4D md) a b c d +
          R_metric (tracelessPartMetricDerivs4D md) a b c d := by
    intro a b c d
    unfold tracelessPartMetricDerivs4D
    rw [R_metric_sub]
    ring
  have hconf_ric : ∀ b d : Fin 4,
      ricci (conformalPartMetricDerivs4D md) sign b d =
        fullRicciTensor4D (metricTraceHessian4D md) b d := by
    intro b d
    rfl
  have hconf_scal :
      scalar (conformalPartMetricDerivs4D md) sign =
        fullScalarCurvature4D (metricTraceHessian4D md) := rfl
  have hconf_ein : ∀ b d : Fin 4,
      einstein (conformalPartMetricDerivs4D md) sign b d =
        fullEinsteinTensor4D (metricTraceHessian4D md) b d := by
    intro b d
    rfl
  refine ⟨hR, ?_, ?_, ?_⟩
  · intro b d
    unfold tracelessPartMetricDerivs4D
    rw [ricci_sub, ← hconf_ric]
    ring
  · unfold tracelessPartMetricDerivs4D
    rw [scalar_sub, ← hconf_scal]
    ring
  · intro b d
    unfold tracelessPartMetricDerivs4D
    rw [einstein_sub, ← hconf_ein]
    ring

#print axioms R_metric_zero
#print axioms R_metric_add
#print axioms R_metric_smul
#print axioms R_metric_sub
#print axioms R_metric_finsetSum
#print axioms dR_metric_zero
#print axioms dR_metric_add
#print axioms dR_metric_smul
#print axioms dR_metric_sub
#print axioms dR_metric_finsetSum
#print axioms ricci_zero
#print axioms ricci_add
#print axioms ricci_smul
#print axioms ricci_sub
#print axioms ricci_finsetSum
#print axioms scalar_zero
#print axioms scalar_add
#print axioms scalar_smul
#print axioms scalar_sub
#print axioms scalar_finsetSum
#print axioms einstein_zero
#print axioms einstein_add
#print axioms einstein_smul
#print axioms einstein_sub
#print axioms einstein_finsetSum
#print axioms dRic_add
#print axioms dRic_smul
#print axioms dRic_sub
#print axioms dScalar_add
#print axioms dScalar_smul
#print axioms dScalar_sub
#print axioms dEinstein_add
#print axioms dEinstein_smul
#print axioms dEinstein_sub
#print axioms minkMetric4D_lorentzian_trace
#print axioms metricTraceHessian4D_symmetric
#print axioms metricTraceThirdJet4D_symmetric
#print axioms conformalPartMetricDerivs4D_h_eq
#print axioms conformalPartMetricDerivs4D_k_eq
#print axioms metricDerivs4D_conformal_traceless_decomposition
#print axioms lorentzianMetricTrace4D_conformalPart
#print axioms tracelessPartMetricDerivs4D_trace_free
#print axioms metricTrace_of_fullConformalMetricDerivs
#print axioms metricTrace_projection_idempotent_and_orthogonal
#print axioms curvature_conformal_traceless_split

end
end UnifiedTheory.Audit.KFCausalCurved4DLinearizedMetricDecomposition
