import UnifiedTheory.Audit.KFCausalCurved4DLinearizedMetricDecomposition

/-! 4D Lorentzian Weyl-Ricci-Scalar (Kulkarni-Nomizu) curvature decomposition
for general linearized metric perturbations `MetricDerivs 4`:
exact algebraic Riemann symmetries and first Bianchi identity of the 4D Weyl
tensor, identical vanishing of all six Lorentzian contractions of the Weyl
tensor, and identical vanishing of the Weyl tensor on all 4D conformal metric
perturbations (`weylTensor4D md = weylTensor4D (tracelessPartMetricDerivs4D md)`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DLinearizedWeylRicciSplit
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open UnifiedTheory.LayerA.VariationalEinstein (R_metric_pair_symm)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein ricci_symmetric)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D symmetrizeHessian4D
  minkMetric4D box4D fullConformalMetricSecond fullConformalMetricDerivs
  zeroThirdJet4D fullRicciTensor4D fullScalarCurvature4D fullEinsteinTensor4D
  symmetrizeHessian4D_eq_of_symm minkMetric4D_diag minkMetric4D_offDiag
  fullRicciTensor4D_master_formula fullScalarCurvature4D_master_formula)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs subMetricDerivs finsetSumMetricDerivs
  R_metric_zero R_metric_add R_metric_smul R_metric_sub R_metric_finsetSum
  ricci_zero ricci_add ricci_smul ricci_sub ricci_finsetSum
  scalar_zero scalar_add scalar_smul scalar_sub scalar_finsetSum
  minkMetric4D_lorentzian_trace metricTraceHessian4D metricTraceThirdJet4D
  metricTraceHessian4D_symmetric conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)

variable {n : ℕ}

/-- First (algebraic) Bianchi identity for the linearized Riemann tensor `R_metric`
of any metric perturbation jet `md : MetricDerivs n`. -/
theorem R_metric_first_bianchi (md : MetricDerivs n) (a b c d : Fin n) :
    R_metric md a b c d + R_metric md b c a d + R_metric md c a b d = 0 := by
  simp only [R_metric]
  have h1 : md.h c b a d = md.h b c a d := md.h_comm c b a d
  have h2 : md.h c a b d = md.h a c b d := md.h_comm c a b d
  have h3 : md.h b a c d = md.h a b c d := md.h_comm b a c d
  have h4 : md.h d b a c = md.h d b c a := md.h_metric d b a c
  have h5 : md.h d a b c = md.h d a c b := md.h_metric d a b c
  have h6 : md.h d c b a = md.h d c a b := md.h_metric d c b a
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- Symmetry of the flat 4D Minkowski metric `minkMetric4D`. -/
theorem minkMetric4D_symm (a b : Fin 4) :
    minkMetric4D a b = minkMetric4D b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp [minkMetric4D, eta, h, Ne.symm h]

private theorem sign_sq_one (a : Fin 4) : sign a * sign a = 1 := by
  simp only [sign]
  split_ifs <;> norm_num

/-- Lorentzian contraction of `minkMetric4D a c` against any 4-vector `f a` on the
first index recovers `f c`. -/
theorem lorentzian_minkMetric4D_contract_left (f : Fin 4 → ℝ) (c : Fin 4) :
    (∑ a : Fin 4, sign a * (minkMetric4D a c * f a)) = f c := by
  have hterm : ∀ a : Fin 4,
      sign a * (minkMetric4D a c * f a) =
        if a = c then (sign a * sign a) * f a else 0 := by
    intro a
    simp only [minkMetric4D, eta]
    split_ifs <;> ring
  simp_rw [hterm, sign_sq_one, one_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ c)]

/-- Lorentzian contraction of `minkMetric4D c a` against any 4-vector `f a` on the
second index recovers `f c`. -/
theorem lorentzian_minkMetric4D_contract_right (f : Fin 4 → ℝ) (c : Fin 4) :
    (∑ a : Fin 4, sign a * (minkMetric4D c a * f a)) = f c := by
  have h : ∀ a : Fin 4, minkMetric4D c a = minkMetric4D a c :=
    fun a => minkMetric4D_symm c a
  simp_rw [h]
  exact lorentzian_minkMetric4D_contract_left f c

/-! ### 4D Lorentzian Weyl-Ricci-Scalar Decomposition Definitions -/

/-- Ricci Kulkarni-Nomizu part `(1/2)(η_{ac} Ric_{bd} - η_{ad} Ric_{bc} - η_{bc} Ric_{ad} + η_{bd} Ric_{ac})`
of the 4D Lorentzian Riemann tensor in dimension `d = 4` (`1 / (d - 2) = 1 / 2`). -/
def ricciCurvaturePart4D (md : MetricDerivs 4) (a b c d : Fin 4) : ℝ :=
  (1 / 2) * (minkMetric4D a c * ricci md sign b d -
    minkMetric4D a d * ricci md sign b c -
    minkMetric4D b c * ricci md sign a d +
    minkMetric4D b d * ricci md sign a c)

/-- Scalar Kulkarni-Nomizu part `-(1/6) R (η_{ac} η_{bd} - η_{ad} η_{bc})`
of the 4D Lorentzian Riemann tensor in dimension `d = 4` (`1 / ((d - 1)(d - 2)) = 1 / 6`). -/
def scalarCurvaturePart4D (md : MetricDerivs 4) (a b c d : Fin 4) : ℝ :=
  -(1 / 6) * scalar md sign *
    (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c)

/-- Combined Ricci-plus-Scalar (Schouten / Kulkarni-Nomizu) part of the 4D
Lorentzian Riemann tensor. -/
def ricciScalarRiemannPart4D (md : MetricDerivs 4) (a b c d : Fin 4) : ℝ :=
  ricciCurvaturePart4D md a b c d + scalarCurvaturePart4D md a b c d

/-- 4D Lorentzian Weyl conformal curvature tensor `C_{abcd}`, defined as the
trace-free part of the Riemann tensor `R_{abcd}`. -/
def weylTensor4D (md : MetricDerivs 4) (a b c d : Fin 4) : ℝ :=
  R_metric md a b c d - ricciScalarRiemannPart4D md a b c d

/-- Exact 4D Lorentzian Riemann-Weyl-Ricci-Scalar decomposition:
`R_{abcd} = C_{abcd} + ricciCurvaturePart4D_{abcd} + scalarCurvaturePart4D_{abcd}`. -/
theorem riemann_eq_weyl_add_ricciScalar (md : MetricDerivs 4) (a b c d : Fin 4) :
    R_metric md a b c d =
      weylTensor4D md a b c d + ricciScalarRiemannPart4D md a b c d ∧
    R_metric md a b c d =
      weylTensor4D md a b c d +
        ricciCurvaturePart4D md a b c d +
        scalarCurvaturePart4D md a b c d := by
  unfold weylTensor4D ricciScalarRiemannPart4D
  exact ⟨by ring, by ring⟩

/-! ### Linearity of `ricciScalarRiemannPart4D` and `weylTensor4D` -/

theorem ricciScalarRiemannPart4D_zero (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (zeroMetricDerivs 4) a b c d = 0 := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  rw [ricci_zero, ricci_zero, ricci_zero, ricci_zero, scalar_zero]
  ring

theorem ricciScalarRiemannPart4D_add (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (addMetricDerivs md₁ md₂) a b c d =
      ricciScalarRiemannPart4D md₁ a b c d +
        ricciScalarRiemannPart4D md₂ a b c d := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  rw [ricci_add, ricci_add, ricci_add, ricci_add, scalar_add]
  ring

theorem ricciScalarRiemannPart4D_smul (r : ℝ) (md : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (smulMetricDerivs r md) a b c d =
      r * ricciScalarRiemannPart4D md a b c d := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  rw [ricci_smul, ricci_smul, ricci_smul, ricci_smul, scalar_smul]
  ring

theorem ricciScalarRiemannPart4D_sub (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (subMetricDerivs md₁ md₂) a b c d =
      ricciScalarRiemannPart4D md₁ a b c d -
        ricciScalarRiemannPart4D md₂ a b c d := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  rw [ricci_sub, ricci_sub, ricci_sub, ricci_sub, scalar_sub]
  ring

theorem weylTensor4D_zero (a b c d : Fin 4) :
    weylTensor4D (zeroMetricDerivs 4) a b c d = 0 := by
  unfold weylTensor4D
  rw [R_metric_zero, ricciScalarRiemannPart4D_zero]
  ring

theorem weylTensor4D_add (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D (addMetricDerivs md₁ md₂) a b c d =
      weylTensor4D md₁ a b c d + weylTensor4D md₂ a b c d := by
  unfold weylTensor4D
  rw [R_metric_add, ricciScalarRiemannPart4D_add]
  ring

theorem weylTensor4D_smul (r : ℝ) (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D (smulMetricDerivs r md) a b c d =
      r * weylTensor4D md a b c d := by
  unfold weylTensor4D
  rw [R_metric_smul, ricciScalarRiemannPart4D_smul]
  ring

theorem weylTensor4D_sub (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D (subMetricDerivs md₁ md₂) a b c d =
      weylTensor4D md₁ a b c d - weylTensor4D md₂ a b c d := by
  unfold weylTensor4D
  rw [R_metric_sub, ricciScalarRiemannPart4D_sub]
  ring

/-! ### Algebraic Riemann Symmetries and First Bianchi Identity of `weylTensor4D` -/

theorem ricciScalarRiemannPart4D_antisym1 (md : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D md a b c d =
      -ricciScalarRiemannPart4D md b a c d := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  ring

theorem ricciScalarRiemannPart4D_antisym2 (md : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D md a b c d =
      -ricciScalarRiemannPart4D md a b d c := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  ring

theorem ricciScalarRiemannPart4D_pair_symm (md : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D md a b c d =
      ricciScalarRiemannPart4D md c d a b := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  have hη1 : minkMetric4D a c = minkMetric4D c a := minkMetric4D_symm a c
  have hη2 : minkMetric4D a d = minkMetric4D d a := minkMetric4D_symm a d
  have hη3 : minkMetric4D b c = minkMetric4D c b := minkMetric4D_symm b c
  have hη4 : minkMetric4D b d = minkMetric4D d b := minkMetric4D_symm b d
  have hR1 : ricci md sign b d = ricci md sign d b := ricci_symmetric md sign b d
  have hR2 : ricci md sign b c = ricci md sign c b := ricci_symmetric md sign b c
  have hR3 : ricci md sign a d = ricci md sign d a := ricci_symmetric md sign a d
  have hR4 : ricci md sign a c = ricci md sign c a := ricci_symmetric md sign a c
  rw [hη1, hη2, hη3, hη4, hR1, hR2, hR3, hR4]
  ring

theorem ricciScalarRiemannPart4D_first_bianchi (md : MetricDerivs 4) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D md a b c d +
      ricciScalarRiemannPart4D md b c a d +
      ricciScalarRiemannPart4D md c a b d = 0 := by
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  have hη_ba : minkMetric4D b a = minkMetric4D a b := minkMetric4D_symm b a
  have hη_ca : minkMetric4D c a = minkMetric4D a c := minkMetric4D_symm c a
  have hη_cb : minkMetric4D c b = minkMetric4D b c := minkMetric4D_symm c b
  have hR_ba : ricci md sign b a = ricci md sign a b := ricci_symmetric md sign b a
  have hR_ca : ricci md sign c a = ricci md sign a c := ricci_symmetric md sign c a
  have hR_cb : ricci md sign c b = ricci md sign b c := ricci_symmetric md sign c b
  rw [hη_ba, hη_ca, hη_cb, hR_ba, hR_ca, hR_cb]
  ring

/-- Antisymmetry of `weylTensor4D` in the first index pair `(a, b)`. -/
theorem weylTensor4D_antisym1 (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D md a b c d = -weylTensor4D md b a c d := by
  unfold weylTensor4D
  rw [UnifiedTheory.LayerA.MetricConstruction.R_antisym1 md a b c d,
    ricciScalarRiemannPart4D_antisym1 md a b c d]
  ring

/-- Antisymmetry of `weylTensor4D` in the second index pair `(c, d)`. -/
theorem weylTensor4D_antisym2 (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D md a b c d = -weylTensor4D md a b d c := by
  unfold weylTensor4D
  rw [UnifiedTheory.LayerA.MetricConstruction.R_antisym2 md a b c d,
    ricciScalarRiemannPart4D_antisym2 md a b c d]
  ring

/-- Pair exchange symmetry `C_{abcd} = C_{cdab}` of `weylTensor4D`. -/
theorem weylTensor4D_pair_symm (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D md a b c d = weylTensor4D md c d a b := by
  unfold weylTensor4D
  rw [R_metric_pair_symm md a b c d,
    ricciScalarRiemannPart4D_pair_symm md a b c d]

/-- First (algebraic) Bianchi identity `C_{abcd} + C_{bcad} + C_{cabd} = 0`
for `weylTensor4D`. -/
theorem weylTensor4D_first_bianchi (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D md a b c d +
      weylTensor4D md b c a d +
      weylTensor4D md c a b d = 0 := by
  have hR := R_metric_first_bianchi md a b c d
  have hS := ricciScalarRiemannPart4D_first_bianchi md a b c d
  unfold weylTensor4D
  linarith

/-! ### Identical Trace-Freeness of `weylTensor4D` in All 6 Lorentzian Contractions -/

/-- The `(1,3)` Lorentzian contraction of `ricciCurvaturePart4D md` equals
`Ric_{bd} + (1/2) R η_{bd}`. -/
theorem ricciCurvaturePart4D_trace_13 (md : MetricDerivs 4) (b d : Fin 4) :
    (∑ a : Fin 4, sign a * ricciCurvaturePart4D md a b a d) =
      ricci md sign b d + (1 / 2) * scalar md sign * minkMetric4D b d := by
  unfold ricciCurvaturePart4D
  have hterm : ∀ a : Fin 4,
      sign a * ((1 / 2) * (minkMetric4D a a * ricci md sign b d -
        minkMetric4D a d * ricci md sign b a -
        minkMetric4D b a * ricci md sign a d +
        minkMetric4D b d * ricci md sign a a)) =
      (1 / 2) * ((sign a * minkMetric4D a a) * ricci md sign b d -
        sign a * (minkMetric4D a d * ricci md sign b a) -
        sign a * (minkMetric4D b a * ricci md sign a d) +
        (sign a * ricci md sign a a) * minkMetric4D b d) := by
    intro a; ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  rw [minkMetric4D_lorentzian_trace,
    lorentzian_minkMetric4D_contract_left (fun a => ricci md sign b a) d,
    lorentzian_minkMetric4D_contract_right (fun a => ricci md sign a d) b]
  change (1 / 2) * (4 * ricci md sign b d - ricci md sign b d -
      ricci md sign b d + scalar md sign * minkMetric4D b d) =
    ricci md sign b d + (1 / 2) * scalar md sign * minkMetric4D b d
  ring

/-- The `(1,3)` Lorentzian contraction of `scalarCurvaturePart4D md` equals
`-(1/2) R η_{bd}`. -/
theorem scalarCurvaturePart4D_trace_13 (md : MetricDerivs 4) (b d : Fin 4) :
    (∑ a : Fin 4, sign a * scalarCurvaturePart4D md a b a d) =
      -(1 / 2) * scalar md sign * minkMetric4D b d := by
  unfold scalarCurvaturePart4D
  have hterm : ∀ a : Fin 4,
      sign a * (-(1 / 6) * scalar md sign *
        (minkMetric4D a a * minkMetric4D b d - minkMetric4D a d * minkMetric4D b a)) =
      -(1 / 6) * scalar md sign *
        ((sign a * minkMetric4D a a) * minkMetric4D b d -
          sign a * (minkMetric4D a d * minkMetric4D b a)) := by
    intro a; ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [minkMetric4D_lorentzian_trace,
    lorentzian_minkMetric4D_contract_left (fun a => minkMetric4D b a) d,
    minkMetric4D_symm b d]
  ring

/-- The `(1,3)` Lorentzian contraction of `ricciScalarRiemannPart4D md` equals
the full Ricci tensor `ricci md sign b d`. -/
theorem ricciScalarRiemannPart4D_trace_eq_ricci (md : MetricDerivs 4) (b d : Fin 4) :
    (∑ a : Fin 4, sign a * ricciScalarRiemannPart4D md a b a d) =
      ricci md sign b d := by
  unfold ricciScalarRiemannPart4D
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [ricciCurvaturePart4D_trace_13, scalarCurvaturePart4D_trace_13]
  ring

/-- The `(1,3)` Lorentzian contraction of the 4D Weyl tensor vanishes identically
for every metric perturbation `md : MetricDerivs 4`. -/
theorem weylTensor4D_trace_free_13 (md : MetricDerivs 4) (b d : Fin 4) :
    (∑ a : Fin 4, sign a * weylTensor4D md a b a d) = 0 := by
  unfold weylTensor4D
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [ricciScalarRiemannPart4D_trace_eq_ricci]
  unfold ricci
  ring

/-- The `(1,2)` Lorentzian contraction of the 4D Weyl tensor vanishes identically. -/
theorem weylTensor4D_trace_free_12 (md : MetricDerivs 4) (c d : Fin 4) :
    (∑ a : Fin 4, sign a * weylTensor4D md a a c d) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have h0 : weylTensor4D md a a c d = 0 := by
    have h := weylTensor4D_antisym1 md a a c d
    linarith
  rw [h0, mul_zero]

/-- The `(3,4)` Lorentzian contraction of the 4D Weyl tensor vanishes identically. -/
theorem weylTensor4D_trace_free_34 (md : MetricDerivs 4) (a b : Fin 4) :
    (∑ c : Fin 4, sign c * weylTensor4D md a b c c) = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  have h0 : weylTensor4D md a b c c = 0 := by
    have h := weylTensor4D_antisym2 md a b c c
    linarith
  rw [h0, mul_zero]

/-- The `(1,4)` Lorentzian contraction of the 4D Weyl tensor vanishes identically. -/
theorem weylTensor4D_trace_free_14 (md : MetricDerivs 4) (b c : Fin 4) :
    (∑ a : Fin 4, sign a * weylTensor4D md a b c a) = 0 := by
  have h : (∑ a : Fin 4, sign a * weylTensor4D md a b c a) =
      -(∑ a : Fin 4, sign a * weylTensor4D md a b a c) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [weylTensor4D_antisym2 md a b c a]
    ring
  rw [h, weylTensor4D_trace_free_13, neg_zero]

/-- The `(2,3)` Lorentzian contraction of the 4D Weyl tensor vanishes identically. -/
theorem weylTensor4D_trace_free_23 (md : MetricDerivs 4) (a d : Fin 4) :
    (∑ b : Fin 4, sign b * weylTensor4D md a b b d) = 0 := by
  have h : (∑ b : Fin 4, sign b * weylTensor4D md a b b d) =
      -(∑ b : Fin 4, sign b * weylTensor4D md b a b d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [weylTensor4D_antisym1 md a b b d]
    ring
  rw [h, weylTensor4D_trace_free_13, neg_zero]

/-- The `(2,4)` Lorentzian contraction of the 4D Weyl tensor vanishes identically. -/
theorem weylTensor4D_trace_free_24 (md : MetricDerivs 4) (a c : Fin 4) :
    (∑ b : Fin 4, sign b * weylTensor4D md a b c b) = 0 := by
  have h : (∑ b : Fin 4, sign b * weylTensor4D md a b c b) =
      ∑ b : Fin 4, sign b * weylTensor4D md b a b c := by
    apply Finset.sum_congr rfl
    intro b _
    rw [weylTensor4D_antisym1 md a b c b, weylTensor4D_antisym2 md b a c b, neg_neg]
  rw [h, weylTensor4D_trace_free_13]

/-- Complete Lorentzian trace-freeness theorem: all six possible single
Lorentzian contractions `(1,2)`, `(3,4)`, `(1,3)`, `(1,4)`, `(2,3)`, and `(2,4)`
of `weylTensor4D md` vanish identically for every `md : MetricDerivs 4`. -/
theorem weylTensor4D_all_six_traces_vanish (md : MetricDerivs 4) :
    (∀ c d : Fin 4, (∑ a : Fin 4, sign a * weylTensor4D md a a c d) = 0) ∧
    (∀ a b : Fin 4, (∑ c : Fin 4, sign c * weylTensor4D md a b c c) = 0) ∧
    (∀ b d : Fin 4, (∑ a : Fin 4, sign a * weylTensor4D md a b a d) = 0) ∧
    (∀ b c : Fin 4, (∑ a : Fin 4, sign a * weylTensor4D md a b c a) = 0) ∧
    (∀ a d : Fin 4, (∑ b : Fin 4, sign b * weylTensor4D md a b b d) = 0) ∧
    (∀ a c : Fin 4, (∑ b : Fin 4, sign b * weylTensor4D md a b c b) = 0) :=
  ⟨weylTensor4D_trace_free_12 md,
   weylTensor4D_trace_free_34 md,
   weylTensor4D_trace_free_13 md,
   weylTensor4D_trace_free_14 md,
   weylTensor4D_trace_free_23 md,
   weylTensor4D_trace_free_24 md⟩

/-! ### 4D Conformal Flatness: Identical Vanishing of `weylTensor4D` on Conformal Jets -/

/-- Exact formula for the Riemann tensor `R_metric (fullConformalMetricDerivs H K)`
of any 4D conformal metric jet with symmetric Hessian `H`:
`R_{abcd}(H) = H_{cb} η_{ad} - H_{ca} η_{bd} - H_{db} η_{ac} + H_{da} η_{bc}`. -/
theorem fullConformal_R_metric_formula (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (a b c d : Fin 4) :
    R_metric (fullConformalMetricDerivs H K) a b c d =
      H c b * minkMetric4D a d - H c a * minkMetric4D b d -
        H d b * minkMetric4D a c + H d a * minkMetric4D b c := by
  simp only [R_metric, fullConformalMetricDerivs, fullConformalMetricSecond,
    minkMetric4D, symmetrizeHessian4D_eq_of_symm H hH]
  ring

/-- For any 4D conformal metric jet `fullConformalMetricDerivs H K` with symmetric
Hessian `H`, the Ricci-Scalar Kulkarni-Nomizu part `ricciScalarRiemannPart4D`
equals the full Riemann tensor `R_metric` identically. -/
theorem fullConformal_ricciScalarRiemannPart4D_eq_R_metric (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (fullConformalMetricDerivs H K) a b c d =
      R_metric (fullConformalMetricDerivs H K) a b c d := by
  have hric : ∀ μ ν : Fin 4,
      ricci (fullConformalMetricDerivs H K) sign μ ν =
        -2 * H μ ν - box4D H * minkMetric4D μ ν := by
    intro μ ν
    exact fullRicciTensor4D_master_formula H hH μ ν
  have hscal :
      scalar (fullConformalMetricDerivs H K) sign = -6 * box4D H :=
    (fullScalarCurvature4D_master_formula H).1
  rw [fullConformal_R_metric_formula H hH K a b c d]
  unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
  rw [hric b d, hric b c, hric a d, hric a c, hscal,
    hH b d, hH b c, hH a d, hH a c]
  ring

/-- **4D Conformal Flatness Theorem**: the 4D Lorentzian Weyl tensor vanishes
identically (`weylTensor4D (fullConformalMetricDerivs H K) a b c d = 0`) for
every symmetric 4×4 conformal Hessian `H` and third jet `K`. -/
theorem weylTensor4D_fullConformal_eq_zero (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (a b c d : Fin 4) :
    weylTensor4D (fullConformalMetricDerivs H K) a b c d = 0 := by
  unfold weylTensor4D
  rw [fullConformal_ricciScalarRiemannPart4D_eq_R_metric H hH K a b c d, sub_self]

/-- The conformal trace part `conformalPartMetricDerivs4D md` of any general 4D
metric perturbation `md : MetricDerivs 4` has identically zero Weyl tensor. -/
theorem weylTensor4D_conformalPart_eq_zero (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 :=
  weylTensor4D_fullConformal_eq_zero
    (metricTraceHessian4D md) (metricTraceHessian4D_symmetric md)
    (metricTraceThirdJet4D md) a b c d

/-- **Conformal Invariance of Linearized 4D Weyl Curvature**: for every general
4D metric perturbation `md : MetricDerivs 4`, the Weyl tensor of `md` equals the
Weyl tensor of its traceless non-conformal part `tracelessPartMetricDerivs4D md`:
`weylTensor4D md a b c d = weylTensor4D (tracelessPartMetricDerivs4D md) a b c d`. -/
theorem weylTensor4D_eq_tracelessPart (md : MetricDerivs 4) (a b c d : Fin 4) :
    weylTensor4D md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d := by
  unfold tracelessPartMetricDerivs4D
  rw [weylTensor4D_sub, weylTensor4D_conformalPart_eq_zero, sub_zero]

#print axioms R_metric_first_bianchi
#print axioms minkMetric4D_symm
#print axioms lorentzian_minkMetric4D_contract_left
#print axioms lorentzian_minkMetric4D_contract_right
#print axioms riemann_eq_weyl_add_ricciScalar
#print axioms ricciScalarRiemannPart4D_zero
#print axioms ricciScalarRiemannPart4D_add
#print axioms ricciScalarRiemannPart4D_smul
#print axioms ricciScalarRiemannPart4D_sub
#print axioms weylTensor4D_zero
#print axioms weylTensor4D_add
#print axioms weylTensor4D_smul
#print axioms weylTensor4D_sub
#print axioms ricciScalarRiemannPart4D_antisym1
#print axioms ricciScalarRiemannPart4D_antisym2
#print axioms ricciScalarRiemannPart4D_pair_symm
#print axioms ricciScalarRiemannPart4D_first_bianchi
#print axioms weylTensor4D_antisym1
#print axioms weylTensor4D_antisym2
#print axioms weylTensor4D_pair_symm
#print axioms weylTensor4D_first_bianchi
#print axioms ricciCurvaturePart4D_trace_13
#print axioms scalarCurvaturePart4D_trace_13
#print axioms ricciScalarRiemannPart4D_trace_eq_ricci
#print axioms weylTensor4D_trace_free_13
#print axioms weylTensor4D_trace_free_12
#print axioms weylTensor4D_trace_free_34
#print axioms weylTensor4D_trace_free_14
#print axioms weylTensor4D_trace_free_23
#print axioms weylTensor4D_trace_free_24
#print axioms weylTensor4D_all_six_traces_vanish
#print axioms fullConformal_R_metric_formula
#print axioms fullConformal_ricciScalarRiemannPart4D_eq_R_metric
#print axioms weylTensor4D_fullConformal_eq_zero
#print axioms weylTensor4D_conformalPart_eq_zero
#print axioms weylTensor4D_eq_tracelessPart

end
end UnifiedTheory.Audit.KFCausalCurved4DLinearizedWeylRicciSplit
