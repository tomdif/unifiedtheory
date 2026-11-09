import UnifiedTheory.Audit.KFCausalCurved4DLinearizedWeylRicciSplit
import UnifiedTheory.Audit.KFCausalCurved4DGeneralProbeCurvatureExtraction

/-! 4D Lorentzian Weyl gravito-electric and gravito-magnetic decomposition:
defines the gravito-electric tidal tensor `E_{ab} = C_{0a0b}` and gravito-magnetic
tensor `B_{abc} = C_{0abc}` for any linearized 4D metric perturbation `md : MetricDerivs 4`,
proves their exact symmetries, temporal vanishing, spatial trace-freeness,
cyclic Bianchi identity, conformal invariance, and the 4D double-dual spatial
reconstruction theorems showing that all 256 components of `weylTensor4D md` are
uniquely and explicitly determined by `(weylElectric4D md, weylMagnetic4D md)`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DWeylElectricMagneticDecomposition
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D minkMetric4D fullConformalMetricDerivs)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs negMetricDerivs subMetricDerivs
  metricTraceHessian4D metricTraceThirdJet4D metricTraceHessian4D_symmetric
  conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (weylTensor4D
  weylTensor4D_zero weylTensor4D_add weylTensor4D_smul weylTensor4D_sub
  weylTensor4D_antisym1 weylTensor4D_antisym2
  weylTensor4D_pair_symm weylTensor4D_first_bianchi
  weylTensor4D_trace_free_13 weylTensor4D_trace_free_23 weylTensor4D_trace_free_24
  weylTensor4D_fullConformal_eq_zero weylTensor4D_conformalPart_eq_zero
  weylTensor4D_eq_tracelessPart)

/-! ### Definitions of the 4D Gravito-Electric and Gravito-Magnetic Weyl Tensors -/

/-- 4D gravito-electric Weyl tidal tensor `E_{ab}(md) = C_{0a0b}(md)`. -/
def weylElectric4D (md : MetricDerivs 4) (a b : Fin 4) : ℝ :=
  weylTensor4D md 0 a 0 b

/-- 4D gravito-magnetic Weyl tensor `B_{abc}(md) = C_{0abc}(md)` (in 3+1 form,
dual to the spatial 2-index magnetic tidal tensor). -/
def weylMagnetic4D (md : MetricDerivs 4) (a b c : Fin 4) : ℝ :=
  weylTensor4D md 0 a b c

/-! ### Vector-Space Linearity and Conformal Invariance -/

theorem weylElectric4D_zero (a b : Fin 4) :
    weylElectric4D (zeroMetricDerivs 4) a b = 0 :=
  weylTensor4D_zero 0 a 0 b

theorem weylElectric4D_add (md₁ md₂ : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D (addMetricDerivs md₁ md₂) a b =
      weylElectric4D md₁ a b + weylElectric4D md₂ a b :=
  weylTensor4D_add md₁ md₂ 0 a 0 b

theorem weylElectric4D_smul (r : ℝ) (md : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D (smulMetricDerivs r md) a b = r * weylElectric4D md a b :=
  weylTensor4D_smul r md 0 a 0 b

theorem weylElectric4D_sub (md₁ md₂ : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D (subMetricDerivs md₁ md₂) a b =
      weylElectric4D md₁ a b - weylElectric4D md₂ a b :=
  weylTensor4D_sub md₁ md₂ 0 a 0 b

theorem weylElectric4D_neg (md : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D (negMetricDerivs md) a b = -weylElectric4D md a b := by
  unfold negMetricDerivs
  rw [weylElectric4D_smul]
  ring

theorem weylMagnetic4D_zero (a b c : Fin 4) :
    weylMagnetic4D (zeroMetricDerivs 4) a b c = 0 :=
  weylTensor4D_zero 0 a b c

theorem weylMagnetic4D_add (md₁ md₂ : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D (addMetricDerivs md₁ md₂) a b c =
      weylMagnetic4D md₁ a b c + weylMagnetic4D md₂ a b c :=
  weylTensor4D_add md₁ md₂ 0 a b c

theorem weylMagnetic4D_smul (r : ℝ) (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D (smulMetricDerivs r md) a b c = r * weylMagnetic4D md a b c :=
  weylTensor4D_smul r md 0 a b c

theorem weylMagnetic4D_sub (md₁ md₂ : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D (subMetricDerivs md₁ md₂) a b c =
      weylMagnetic4D md₁ a b c - weylMagnetic4D md₂ a b c :=
  weylTensor4D_sub md₁ md₂ 0 a b c

theorem weylMagnetic4D_neg (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D (negMetricDerivs md) a b c = -weylMagnetic4D md a b c := by
  unfold negMetricDerivs
  rw [weylMagnetic4D_smul]
  ring

theorem weylElectric4D_fullConformal_eq_zero (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (a b : Fin 4) :
    weylElectric4D (fullConformalMetricDerivs H K) a b = 0 :=
  weylTensor4D_fullConformal_eq_zero H hH K 0 a 0 b

theorem weylMagnetic4D_fullConformal_eq_zero (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) (a b c : Fin 4) :
    weylMagnetic4D (fullConformalMetricDerivs H K) a b c = 0 :=
  weylTensor4D_fullConformal_eq_zero H hH K 0 a b c

theorem weylElectric4D_conformalPart_eq_zero (md : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D (conformalPartMetricDerivs4D md) a b = 0 :=
  weylTensor4D_conformalPart_eq_zero md 0 a 0 b

theorem weylMagnetic4D_conformalPart_eq_zero (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D (conformalPartMetricDerivs4D md) a b c = 0 :=
  weylTensor4D_conformalPart_eq_zero md 0 a b c

theorem weylElectric4D_eq_tracelessPart (md : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D md a b = weylElectric4D (tracelessPartMetricDerivs4D md) a b :=
  weylTensor4D_eq_tracelessPart md 0 a 0 b

theorem weylMagnetic4D_eq_tracelessPart (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D md a b c = weylMagnetic4D (tracelessPartMetricDerivs4D md) a b c :=
  weylTensor4D_eq_tracelessPart md 0 a b c

/-! ### Symmetry, Temporal Orthogonality, and Spatial Trace-Freeness of `weylElectric4D` -/

theorem weylTensor4D_self_12 (md : MetricDerivs 4) (a c d : Fin 4) :
    weylTensor4D md a a c d = 0 := by
  have h := weylTensor4D_antisym1 md a a c d
  linarith

theorem weylTensor4D_self_34 (md : MetricDerivs 4) (a b c : Fin 4) :
    weylTensor4D md a b c c = 0 := by
  have h := weylTensor4D_antisym2 md a b c c
  linarith

/-- Symmetry `E_{ab} = E_{ba}` of the gravito-electric Weyl tensor. -/
theorem weylElectric4D_symm (md : MetricDerivs 4) (a b : Fin 4) :
    weylElectric4D md a b = weylElectric4D md b a :=
  weylTensor4D_pair_symm md 0 a 0 b

/-- Vanishing of `weylElectric4D` when the first index is temporal (`a = 0`). -/
theorem weylElectric4D_zero_left (md : MetricDerivs 4) (b : Fin 4) :
    weylElectric4D md 0 b = 0 :=
  weylTensor4D_self_12 md 0 0 b

/-- Vanishing of `weylElectric4D` when the second index is temporal (`b = 0`). -/
theorem weylElectric4D_zero_right (md : MetricDerivs 4) (a : Fin 4) :
    weylElectric4D md a 0 = 0 :=
  weylTensor4D_self_34 md 0 a 0

/-- Spatial trace-freeness of the gravito-electric Weyl tensor:
`E_{11} + E_{22} + E_{33} = 0`. -/
theorem weylElectric4D_spatial_trace_zero (md : MetricDerivs 4) :
    weylElectric4D md 1 1 + weylElectric4D md 2 2 + weylElectric4D md 3 3 = 0 := by
  have htr := weylTensor4D_trace_free_24 md 0 0
  rw [Fin.sum_univ_four] at htr
  change sign 0 * weylElectric4D md 0 0 +
      sign 1 * weylElectric4D md 1 1 +
      sign 2 * weylElectric4D md 2 2 +
      sign 3 * weylElectric4D md 3 3 = 0 at htr
  rw [weylElectric4D_zero_left md 0] at htr
  have hs0 : sign 0 = -1 := rfl
  have hs1 : sign 1 = 1 := rfl
  have hs2 : sign 2 = 1 := rfl
  have hs3 : sign 3 = 1 := rfl
  rw [hs0, hs1, hs2, hs3] at htr
  linarith

/-- Full 4D Lorentzian trace-freeness of `weylElectric4D`. -/
theorem weylElectric4D_lorentzian_trace_zero (md : MetricDerivs 4) :
    (∑ a : Fin 4, sign a * weylElectric4D md a a) = 0 :=
  weylTensor4D_trace_free_24 md 0 0

/-! ### Symmetries, Bianchi Identity, and Spatial Trace-Freeness of `weylMagnetic4D` -/

/-- Skew-symmetry `B_{abc} = -B_{acb}` of `weylMagnetic4D` in its last two indices. -/
theorem weylMagnetic4D_antisym (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D md a b c = -weylMagnetic4D md a c b :=
  weylTensor4D_antisym2 md 0 a b c

/-- Diagonal vanishing `B_{abb} = 0` in the last two indices. -/
theorem weylMagnetic4D_self_zero (md : MetricDerivs 4) (a b : Fin 4) :
    weylMagnetic4D md a b b = 0 :=
  weylTensor4D_self_34 md 0 a b

/-- Vanishing `B_{0bc} = 0` when the first index of `weylMagnetic4D` is temporal. -/
theorem weylMagnetic4D_zero_first (md : MetricDerivs 4) (b c : Fin 4) :
    weylMagnetic4D md 0 b c = 0 :=
  weylTensor4D_self_12 md 0 b c

/-- When the second index of `weylMagnetic4D` is temporal (`b = 0`), it reduces to
`weylElectric4D`: `B_{a0c} = E_{ac}`. -/
theorem weylMagnetic4D_zero_second_eq_electric (md : MetricDerivs 4) (a c : Fin 4) :
    weylMagnetic4D md a 0 c = weylElectric4D md a c := rfl

/-- When the third index of `weylMagnetic4D` is temporal (`c = 0`), it reduces to
`-weylElectric4D`: `B_{ab0} = -E_{ab}`. -/
theorem weylMagnetic4D_zero_third_eq_neg_electric (md : MetricDerivs 4) (a b : Fin 4) :
    weylMagnetic4D md a b 0 = -weylElectric4D md a b :=
  weylTensor4D_antisym2 md 0 a b 0

/-- Cyclic algebraic Bianchi identity for `weylMagnetic4D`:
`B_{abc} + B_{bca} + B_{cab} = 0`. -/
theorem weylMagnetic4D_cyclic_bianchi (md : MetricDerivs 4) (a b c : Fin 4) :
    weylMagnetic4D md a b c + weylMagnetic4D md b c a + weylMagnetic4D md c a b = 0 := by
  unfold weylMagnetic4D
  have h1 : weylTensor4D md 0 a b c = -weylTensor4D md b c a 0 := by
    rw [weylTensor4D_pair_symm md 0 a b c, weylTensor4D_antisym2 md b c 0 a]
  have h2 : weylTensor4D md 0 b c a = -weylTensor4D md c a b 0 := by
    rw [weylTensor4D_pair_symm md 0 b c a, weylTensor4D_antisym2 md c a 0 b]
  have h3 : weylTensor4D md 0 c a b = -weylTensor4D md a b c 0 := by
    rw [weylTensor4D_pair_symm md 0 c a b, weylTensor4D_antisym2 md a b 0 c]
  have hb := weylTensor4D_first_bianchi md a b c 0
  linarith

/-- Spatial cyclic Bianchi identity `B_{123} + B_{231} + B_{312} = 0`. -/
theorem weylMagnetic4D_spatial_cyclic (md : MetricDerivs 4) :
    weylMagnetic4D md 1 2 3 + weylMagnetic4D md 2 3 1 + weylMagnetic4D md 3 1 2 = 0 :=
  weylMagnetic4D_cyclic_bianchi md 1 2 3

/-- Spatial trace-freeness of `weylMagnetic4D` in its first two indices:
`B_{11c} + B_{22c} + B_{33c} = 0`. -/
theorem weylMagnetic4D_spatial_trace_zero (md : MetricDerivs 4) (c : Fin 4) :
    weylMagnetic4D md 1 1 c + weylMagnetic4D md 2 2 c + weylMagnetic4D md 3 3 c = 0 := by
  have htr := weylTensor4D_trace_free_23 md 0 c
  rw [Fin.sum_univ_four] at htr
  change sign 0 * weylMagnetic4D md 0 0 c +
      sign 1 * weylMagnetic4D md 1 1 c +
      sign 2 * weylMagnetic4D md 2 2 c +
      sign 3 * weylMagnetic4D md 3 3 c = 0 at htr
  rw [weylMagnetic4D_zero_first md 0 c] at htr
  have hs0 : sign 0 = -1 := rfl
  have hs1 : sign 1 = 1 := rfl
  have hs2 : sign 2 = 1 := rfl
  have hs3 : sign 3 = 1 := rfl
  rw [hs0, hs1, hs2, hs3] at htr
  linarith

/-! ### 4D Double-Dual Spatial Weyl Reconstruction from `weylElectric4D` -/

/-- Fundamental 3+1 trace relation linking the spatial sum of `weylTensor4D`
to `weylElectric4D`:
`C_{1b1d} + C_{2b2d} + C_{3b3d} = E_{bd}` for all `b d : Fin 4`. -/
theorem weylTensor4D_spatial_sum_eq_weylElectric4D (md : MetricDerivs 4) (b d : Fin 4) :
    weylTensor4D md 1 b 1 d + weylTensor4D md 2 b 2 d + weylTensor4D md 3 b 3 d =
      weylElectric4D md b d := by
  have htr := weylTensor4D_trace_free_13 md b d
  rw [Fin.sum_univ_four] at htr
  have hs0 : sign 0 = -1 := rfl
  have hs1 : sign 1 = 1 := rfl
  have hs2 : sign 2 = 1 := rfl
  have hs3 : sign 3 = 1 := rfl
  rw [hs0, hs1, hs2, hs3] at htr
  unfold weylElectric4D
  linarith

/-- Diagonal spatial Weyl sectional curvature in the `(1, 2)` plane:
`C_{1212} = E_{11} + E_{22} = -E_{33}`. -/
theorem weylTensor4D_spatial_1212_eq_neg_electric_33 (md : MetricDerivs 4) :
    weylTensor4D md 1 2 1 2 = -weylElectric4D md 3 3 ∧
    weylTensor4D md 1 2 1 2 = weylElectric4D md 1 1 + weylElectric4D md 2 2 := by
  have h1 := weylTensor4D_spatial_sum_eq_weylElectric4D md 1 1
  have h2 := weylTensor4D_spatial_sum_eq_weylElectric4D md 2 2
  have h3 := weylTensor4D_spatial_sum_eq_weylElectric4D md 3 3
  have htr := weylElectric4D_spatial_trace_zero md
  rw [weylTensor4D_self_12 md 1 1 1] at h1
  rw [weylTensor4D_self_12 md 2 2 2] at h2
  rw [weylTensor4D_self_12 md 3 3 3] at h3
  have hs12 : weylTensor4D md 2 1 2 1 = weylTensor4D md 1 2 1 2 := by
    rw [weylTensor4D_antisym1 md 2 1 2 1, weylTensor4D_antisym2 md 1 2 2 1, neg_neg]
  have hs13 : weylTensor4D md 3 1 3 1 = weylTensor4D md 1 3 1 3 := by
    rw [weylTensor4D_antisym1 md 3 1 3 1, weylTensor4D_antisym2 md 1 3 3 1, neg_neg]
  have hs23 : weylTensor4D md 3 2 3 2 = weylTensor4D md 2 3 2 3 := by
    rw [weylTensor4D_antisym1 md 3 2 3 2, weylTensor4D_antisym2 md 2 3 3 2, neg_neg]
  rw [hs12, hs13] at h1
  rw [hs23] at h2
  refine ⟨by linarith, by linarith⟩

/-- Diagonal spatial Weyl sectional curvature in the `(1, 3)` plane:
`C_{1313} = E_{11} + E_{33} = -E_{22}`. -/
theorem weylTensor4D_spatial_1313_eq_neg_electric_22 (md : MetricDerivs 4) :
    weylTensor4D md 1 3 1 3 = -weylElectric4D md 2 2 ∧
    weylTensor4D md 1 3 1 3 = weylElectric4D md 1 1 + weylElectric4D md 3 3 := by
  have h1 := weylTensor4D_spatial_sum_eq_weylElectric4D md 1 1
  have h12 := (weylTensor4D_spatial_1212_eq_neg_electric_33 md).1
  have htr := weylElectric4D_spatial_trace_zero md
  rw [weylTensor4D_self_12 md 1 1 1] at h1
  have hs12 : weylTensor4D md 2 1 2 1 = weylTensor4D md 1 2 1 2 := by
    rw [weylTensor4D_antisym1 md 2 1 2 1, weylTensor4D_antisym2 md 1 2 2 1, neg_neg]
  have hs13 : weylTensor4D md 3 1 3 1 = weylTensor4D md 1 3 1 3 := by
    rw [weylTensor4D_antisym1 md 3 1 3 1, weylTensor4D_antisym2 md 1 3 3 1, neg_neg]
  rw [hs12, hs13] at h1
  refine ⟨by linarith, by linarith⟩

/-- Diagonal spatial Weyl sectional curvature in the `(2, 3)` plane:
`C_{2323} = E_{22} + E_{33} = -E_{11}`. -/
theorem weylTensor4D_spatial_2323_eq_neg_electric_11 (md : MetricDerivs 4) :
    weylTensor4D md 2 3 2 3 = -weylElectric4D md 1 1 ∧
    weylTensor4D md 2 3 2 3 = weylElectric4D md 2 2 + weylElectric4D md 3 3 := by
  have h2 := weylTensor4D_spatial_sum_eq_weylElectric4D md 2 2
  have h12 := (weylTensor4D_spatial_1212_eq_neg_electric_33 md).1
  have htr := weylElectric4D_spatial_trace_zero md
  rw [weylTensor4D_self_12 md 2 2 2] at h2
  have hs23 : weylTensor4D md 3 2 3 2 = weylTensor4D md 2 3 2 3 := by
    rw [weylTensor4D_antisym1 md 3 2 3 2, weylTensor4D_antisym2 md 2 3 3 2, neg_neg]
  rw [hs23] at h2
  refine ⟨by linarith, by linarith⟩

/-- The sum of the three spatial sectional Weyl curvatures vanishes identically:
`C_{1212} + C_{1313} + C_{2323} = 0`. -/
theorem weylTensor4D_spatial_sectional_sum_zero (md : MetricDerivs 4) :
    weylTensor4D md 1 2 1 2 + weylTensor4D md 1 3 1 3 + weylTensor4D md 2 3 2 3 = 0 := by
  rw [(weylTensor4D_spatial_1212_eq_neg_electric_33 md).1,
    (weylTensor4D_spatial_1313_eq_neg_electric_22 md).1,
    (weylTensor4D_spatial_2323_eq_neg_electric_11 md).1]
  have htr := weylElectric4D_spatial_trace_zero md
  linarith

/-- Off-diagonal spatial Weyl components equal the off-diagonal gravito-electric
components:
`C_{1213} = E_{23}`, `C_{2123} = E_{13}`, and `C_{3132} = E_{12}`. -/
theorem weylTensor4D_spatial_offDiag_eq_electric (md : MetricDerivs 4) :
    weylTensor4D md 1 2 1 3 = weylElectric4D md 2 3 ∧
    weylTensor4D md 2 1 2 3 = weylElectric4D md 1 3 ∧
    weylTensor4D md 3 1 3 2 = weylElectric4D md 1 2 := by
  have h23 := weylTensor4D_spatial_sum_eq_weylElectric4D md 2 3
  have h13 := weylTensor4D_spatial_sum_eq_weylElectric4D md 1 3
  have h12 := weylTensor4D_spatial_sum_eq_weylElectric4D md 1 2
  rw [weylTensor4D_self_12 md 2 2 3, weylTensor4D_self_34 md 3 2 3] at h23
  rw [weylTensor4D_self_12 md 1 1 3, weylTensor4D_self_34 md 3 1 3] at h13
  rw [weylTensor4D_self_12 md 1 1 2, weylTensor4D_self_34 md 2 1 2] at h12
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ### Full 256-Component Reconstruction of `weylTensor4D` from `(weylElectric4D, weylMagnetic4D)` -/

/-- Explicit algebraic reconstruction of all 256 components of a 4D Weyl tensor
from its gravito-electric tensor `E_{ab}` and gravito-magnetic tensor `B_{abc}`. -/
def reconstructWeylFromElectricMagnetic4D
    (E : Fin 4 → Fin 4 → ℝ) (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a b c d : Fin 4) : ℝ :=
  if a = 0 then B b c d
  else if b = 0 then -B a c d
  else if c = 0 then B d a b
  else if d = 0 then -B c a b
  else
    minkMetric4D a c * E b d - minkMetric4D a d * E b c -
      minkMetric4D b c * E a d + minkMetric4D b d * E a c

private theorem weylTensor4D_spatial_12_cd (md : MetricDerivs 4)
    (c d : Fin 4) (hc : c ≠ 0) (hd : d ≠ 0) :
    weylTensor4D md 1 2 c d =
      minkMetric4D 1 c * weylElectric4D md 2 d -
        minkMetric4D 1 d * weylElectric4D md 2 c -
        minkMetric4D 2 c * weylElectric4D md 1 d +
        minkMetric4D 2 d * weylElectric4D md 1 c := by
  have h1212 := (weylTensor4D_spatial_1212_eq_neg_electric_33 md).2
  have hoff := weylTensor4D_spatial_offDiag_eq_electric md
  have h1213 : weylTensor4D md 1 2 1 3 = weylElectric4D md 2 3 := hoff.1
  have h1223 : weylTensor4D md 1 2 2 3 = -weylElectric4D md 1 3 := by
    rw [weylTensor4D_antisym1 md 1 2 2 3, hoff.2.1]
  have h1221 : weylTensor4D md 1 2 2 1 = -(weylElectric4D md 1 1 + weylElectric4D md 2 2) := by
    rw [weylTensor4D_antisym2 md 1 2 2 1, h1212]
  have h1231 : weylTensor4D md 1 2 3 1 = -weylElectric4D md 2 3 := by
    rw [weylTensor4D_antisym2 md 1 2 3 1, h1213]
  have h1232 : weylTensor4D md 1 2 3 2 = weylElectric4D md 1 3 := by
    rw [weylTensor4D_antisym2 md 1 2 3 2, h1223, neg_neg]
  have h1211 := weylTensor4D_self_34 md 1 2 1
  have h1222 := weylTensor4D_self_34 md 1 2 2
  have h1233 := weylTensor4D_self_34 md 1 2 3
  fin_cases c <;> fin_cases d
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1211]
  · simp [minkMetric4D, eta, sign, h1212]; ring
  · simp [minkMetric4D, eta, sign, h1213]
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1221]; ring
  · simp [minkMetric4D, eta, sign, h1222]
  · simp [minkMetric4D, eta, sign, h1223]
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1231]
  · simp [minkMetric4D, eta, sign, h1232]
  · simp [minkMetric4D, eta, h1233]

private theorem weylTensor4D_spatial_13_cd (md : MetricDerivs 4)
    (c d : Fin 4) (hc : c ≠ 0) (hd : d ≠ 0) :
    weylTensor4D md 1 3 c d =
      minkMetric4D 1 c * weylElectric4D md 3 d -
        minkMetric4D 1 d * weylElectric4D md 3 c -
        minkMetric4D 3 c * weylElectric4D md 1 d +
        minkMetric4D 3 d * weylElectric4D md 1 c := by
  have h1313 := (weylTensor4D_spatial_1313_eq_neg_electric_22 md).2
  have hoff := weylTensor4D_spatial_offDiag_eq_electric md
  have h1312 : weylTensor4D md 1 3 1 2 = weylElectric4D md 3 2 := by
    rw [weylTensor4D_pair_symm md 1 3 1 2, hoff.1, weylElectric4D_symm md 2 3]
  have h1323 : weylTensor4D md 1 3 2 3 = weylElectric4D md 1 2 := by
    rw [weylTensor4D_antisym1 md 1 3 2 3, weylTensor4D_antisym2 md 3 1 2 3,
      neg_neg, hoff.2.2]
  have h1321 : weylTensor4D md 1 3 2 1 = -weylElectric4D md 3 2 := by
    rw [weylTensor4D_antisym2 md 1 3 2 1, h1312]
  have h1331 : weylTensor4D md 1 3 3 1 = -(weylElectric4D md 1 1 + weylElectric4D md 3 3) := by
    rw [weylTensor4D_antisym2 md 1 3 3 1, h1313]
  have h1332 : weylTensor4D md 1 3 3 2 = -weylElectric4D md 1 2 := by
    rw [weylTensor4D_antisym2 md 1 3 3 2, h1323]
  have h1311 := weylTensor4D_self_34 md 1 3 1
  have h1322 := weylTensor4D_self_34 md 1 3 2
  have h1333 := weylTensor4D_self_34 md 1 3 3
  fin_cases c <;> fin_cases d
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1311]
  · simp [minkMetric4D, eta, sign, h1312]
  · simp [minkMetric4D, eta, sign, h1313]; ring
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1321]
  · simp [minkMetric4D, eta, h1322]
  · simp [minkMetric4D, eta, sign, h1323]
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h1331]; ring
  · simp [minkMetric4D, eta, sign, h1332]
  · simp [minkMetric4D, eta, sign, h1333]

private theorem weylTensor4D_spatial_23_cd (md : MetricDerivs 4)
    (c d : Fin 4) (hc : c ≠ 0) (hd : d ≠ 0) :
    weylTensor4D md 2 3 c d =
      minkMetric4D 2 c * weylElectric4D md 3 d -
        minkMetric4D 2 d * weylElectric4D md 3 c -
        minkMetric4D 3 c * weylElectric4D md 2 d +
        minkMetric4D 3 d * weylElectric4D md 2 c := by
  have h2323 := (weylTensor4D_spatial_2323_eq_neg_electric_11 md).2
  have hoff := weylTensor4D_spatial_offDiag_eq_electric md
  have h2312 : weylTensor4D md 2 3 1 2 = -weylElectric4D md 3 1 := by
    rw [weylTensor4D_pair_symm md 2 3 1 2, weylTensor4D_antisym1 md 1 2 2 3,
      hoff.2.1, weylElectric4D_symm md 1 3]
  have h2313 : weylTensor4D md 2 3 1 3 = weylElectric4D md 2 1 := by
    rw [weylTensor4D_pair_symm md 2 3 1 3, weylTensor4D_antisym1 md 1 3 2 3,
      weylTensor4D_antisym2 md 3 1 2 3, neg_neg, hoff.2.2, weylElectric4D_symm md 1 2]
  have h2321 : weylTensor4D md 2 3 2 1 = weylElectric4D md 3 1 := by
    rw [weylTensor4D_antisym2 md 2 3 2 1, h2312, neg_neg]
  have h2331 : weylTensor4D md 2 3 3 1 = -weylElectric4D md 2 1 := by
    rw [weylTensor4D_antisym2 md 2 3 3 1, h2313]
  have h2332 : weylTensor4D md 2 3 3 2 = -(weylElectric4D md 2 2 + weylElectric4D md 3 3) := by
    rw [weylTensor4D_antisym2 md 2 3 3 2, h2323]
  have h2311 := weylTensor4D_self_34 md 2 3 1
  have h2322 := weylTensor4D_self_34 md 2 3 2
  have h2333 := weylTensor4D_self_34 md 2 3 3
  fin_cases c <;> fin_cases d
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hc
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, h2311]
  · simp [minkMetric4D, eta, sign, h2312]
  · simp [minkMetric4D, eta, sign, h2313]
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h2321]
  · simp [minkMetric4D, eta, sign, h2322]
  · simp [minkMetric4D, eta, sign, h2323]; ring
  · exact absurd rfl hd
  · simp [minkMetric4D, eta, sign, h2331]
  · simp [minkMetric4D, eta, sign, h2332]; ring
  · simp [minkMetric4D, eta, sign, h2333]

/-- **3D Spatial Weyl Kulkarni-Nomizu Formula**: for all spatial indices
`a, b, c, d ≠ 0`, the spatial Weyl tensor is given by
`C_{abcd} = η_{ac} E_{bd} - η_{ad} E_{bc} - η_{bc} E_{ad} + η_{bd} E_{ac}`. -/
theorem weylTensor4D_spatial_formula (md : MetricDerivs 4)
    (a b c d : Fin 4) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    weylTensor4D md a b c d =
      minkMetric4D a c * weylElectric4D md b d -
        minkMetric4D a d * weylElectric4D md b c -
        minkMetric4D b c * weylElectric4D md a d +
        minkMetric4D b d * weylElectric4D md a c := by
  have h12 := weylTensor4D_spatial_12_cd md c d hc hd
  have h13 := weylTensor4D_spatial_13_cd md c d hc hd
  have h23 := weylTensor4D_spatial_23_cd md c d hc hd
  have h21 : weylTensor4D md 2 1 c d = -weylTensor4D md 1 2 c d :=
    weylTensor4D_antisym1 md 2 1 c d
  have h31 : weylTensor4D md 3 1 c d = -weylTensor4D md 1 3 c d :=
    weylTensor4D_antisym1 md 3 1 c d
  have h32 : weylTensor4D md 3 2 c d = -weylTensor4D md 2 3 c d :=
    weylTensor4D_antisym1 md 3 2 c d
  fin_cases a <;> fin_cases b
  · exact absurd rfl ha
  · exact absurd rfl ha
  · exact absurd rfl ha
  · exact absurd rfl ha
  · exact absurd rfl hb
  · rw [weylTensor4D_self_12]; ring
  · exact h12
  · exact h13
  · exact absurd rfl hb
  · change weylTensor4D md 2 1 c d =
      minkMetric4D 2 c * weylElectric4D md 1 d -
        minkMetric4D 2 d * weylElectric4D md 1 c -
        minkMetric4D 1 c * weylElectric4D md 2 d +
        minkMetric4D 1 d * weylElectric4D md 2 c
    rw [h21, h12]; ring
  · rw [weylTensor4D_self_12]; ring
  · exact h23
  · exact absurd rfl hb
  · change weylTensor4D md 3 1 c d =
      minkMetric4D 3 c * weylElectric4D md 1 d -
        minkMetric4D 3 d * weylElectric4D md 1 c -
        minkMetric4D 1 c * weylElectric4D md 3 d +
        minkMetric4D 1 d * weylElectric4D md 3 c
    rw [h31, h13]; ring
  · change weylTensor4D md 3 2 c d =
      minkMetric4D 3 c * weylElectric4D md 2 d -
        minkMetric4D 3 d * weylElectric4D md 2 c -
        minkMetric4D 2 c * weylElectric4D md 3 d +
        minkMetric4D 2 d * weylElectric4D md 3 c
    rw [h32, h23]; ring
  · rw [weylTensor4D_self_12]; ring

/-- **Exact 256-Component Weyl Reconstruction Theorem**: for every 4D metric
perturbation `md : MetricDerivs 4` and all `a b c d : Fin 4`,
`reconstructWeylFromElectricMagnetic4D (weylElectric4D md) (weylMagnetic4D md) a b c d = weylTensor4D md a b c d`. -/
theorem reconstructWeylFromElectricMagnetic4D_exact
    (md : MetricDerivs 4) (a b c d : Fin 4) :
    reconstructWeylFromElectricMagnetic4D
      (weylElectric4D md) (weylMagnetic4D md) a b c d =
      weylTensor4D md a b c d := by
  unfold reconstructWeylFromElectricMagnetic4D
  by_cases ha : a = 0
  · subst a; rw [if_pos rfl]; rfl
  · rw [if_neg ha]
    by_cases hb : b = 0
    · subst b; rw [if_pos rfl]
      unfold weylMagnetic4D
      rw [weylTensor4D_antisym1 md a 0 c d]
    · rw [if_neg hb]
      by_cases hc : c = 0
      · subst c; rw [if_pos rfl]
        unfold weylMagnetic4D
        exact (weylTensor4D_pair_symm md a b 0 d).symm
      · rw [if_neg hc]
        by_cases hd : d = 0
        · subst d; rw [if_pos rfl]
          unfold weylMagnetic4D
          rw [weylTensor4D_pair_symm md a b c 0, weylTensor4D_antisym1 md c 0 a b]
        · rw [if_neg hd]
          exact (weylTensor4D_spatial_formula md a b c d ha hb hc hd).symm

/-- **Complete Electric-Magnetic Determination of the 4D Weyl Tensor**:
two metric perturbations `md₁ md₂ : MetricDerivs 4` have identical 4D Weyl
tensors if and only if they have identical gravito-electric and gravito-magnetic
Weyl tensors. -/
theorem weylTensor4D_eq_iff_electric_and_magnetic_eq (md₁ md₂ : MetricDerivs 4) :
    weylTensor4D md₁ = weylTensor4D md₂ ↔
      (weylElectric4D md₁ = weylElectric4D md₂ ∧
        weylMagnetic4D md₁ = weylMagnetic4D md₂) := by
  refine ⟨fun h => ?_, fun ⟨hE, hB⟩ => ?_⟩
  · refine ⟨?_, ?_⟩
    · funext a b; unfold weylElectric4D; rw [h]
    · funext a b c; unfold weylMagnetic4D; rw [h]
  · funext a b c d
    rw [← reconstructWeylFromElectricMagnetic4D_exact md₁ a b c d,
      ← reconstructWeylFromElectricMagnetic4D_exact md₂ a b c d, hE, hB]

/-- A 4D metric perturbation `md : MetricDerivs 4` is conformally flat
(`weylTensor4D md = 0`) if and only if both `weylElectric4D md = 0` and
`weylMagnetic4D md = 0`. -/
theorem weylTensor4D_eq_zero_iff_electric_and_magnetic_zero (md : MetricDerivs 4) :
    (∀ a b c d : Fin 4, weylTensor4D md a b c d = 0) ↔
      ((∀ a b : Fin 4, weylElectric4D md a b = 0) ∧
        (∀ a b c : Fin 4, weylMagnetic4D md a b c = 0)) := by
  refine ⟨fun h => ⟨fun a b => h 0 a 0 b, fun a b c => h 0 a b c⟩, fun ⟨hE, hB⟩ a b c d => ?_⟩
  have hE_fn : weylElectric4D md = weylElectric4D (zeroMetricDerivs 4) := by
    funext i j; rw [hE i j, weylElectric4D_zero]
  have hB_fn : weylMagnetic4D md = weylMagnetic4D (zeroMetricDerivs 4) := by
    funext i j k; rw [hB i j k, weylMagnetic4D_zero]
  have hW := (weylTensor4D_eq_iff_electric_and_magnetic_eq md (zeroMetricDerivs 4)).mpr ⟨hE_fn, hB_fn⟩
  exact congr_fun (congr_fun (congr_fun (congr_fun hW a) b) c) d |>.trans (weylTensor4D_zero a b c d)

#print axioms weylElectric4D_zero
#print axioms weylElectric4D_add
#print axioms weylElectric4D_smul
#print axioms weylElectric4D_sub
#print axioms weylElectric4D_neg
#print axioms weylMagnetic4D_zero
#print axioms weylMagnetic4D_add
#print axioms weylMagnetic4D_smul
#print axioms weylMagnetic4D_sub
#print axioms weylMagnetic4D_neg
#print axioms weylElectric4D_fullConformal_eq_zero
#print axioms weylMagnetic4D_fullConformal_eq_zero
#print axioms weylElectric4D_conformalPart_eq_zero
#print axioms weylMagnetic4D_conformalPart_eq_zero
#print axioms weylElectric4D_eq_tracelessPart
#print axioms weylMagnetic4D_eq_tracelessPart
#print axioms weylTensor4D_self_12
#print axioms weylTensor4D_self_34
#print axioms weylElectric4D_symm
#print axioms weylElectric4D_zero_left
#print axioms weylElectric4D_zero_right
#print axioms weylElectric4D_spatial_trace_zero
#print axioms weylElectric4D_lorentzian_trace_zero
#print axioms weylMagnetic4D_antisym
#print axioms weylMagnetic4D_self_zero
#print axioms weylMagnetic4D_zero_first
#print axioms weylMagnetic4D_zero_second_eq_electric
#print axioms weylMagnetic4D_zero_third_eq_neg_electric
#print axioms weylMagnetic4D_cyclic_bianchi
#print axioms weylMagnetic4D_spatial_cyclic
#print axioms weylMagnetic4D_spatial_trace_zero
#print axioms weylTensor4D_spatial_sum_eq_weylElectric4D
#print axioms weylTensor4D_spatial_1212_eq_neg_electric_33
#print axioms weylTensor4D_spatial_1313_eq_neg_electric_22
#print axioms weylTensor4D_spatial_2323_eq_neg_electric_11
#print axioms weylTensor4D_spatial_sectional_sum_zero
#print axioms weylTensor4D_spatial_offDiag_eq_electric
#print axioms weylTensor4D_spatial_formula
#print axioms reconstructWeylFromElectricMagnetic4D_exact
#print axioms weylTensor4D_eq_iff_electric_and_magnetic_eq
#print axioms weylTensor4D_eq_zero_iff_electric_and_magnetic_zero

end
end UnifiedTheory.Audit.KFCausalCurved4DWeylElectricMagneticDecomposition
