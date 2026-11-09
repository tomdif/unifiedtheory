import UnifiedTheory.Audit.KFCausalCurved4DWeylElectricMagneticDecomposition

/-! 4D tidal/bivector curvature probe functionals (`riemannTidalProbe`,
`weylTidalProbe`, `ricciTidalProbe`), coordinate basis extraction of all
Riemann, Weyl, gravito-electric, and gravito-magnetic components, and explicit
transverse-traceless gravitational-wave metric perturbations
(`plusWaveMetricDerivs4D` and `crossWaveMetricDerivs4D`) demonstrating exact
linearized Einstein-vacuum solutions (`G_{μν} = 0`, `Ric_{μν} = 0`, `R = 0`)
with nonvanishing pure-Weyl curvature extracted by tidal probes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DTidalWeylProbeExtraction
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric R_antisym1 R_antisym2)
open UnifiedTheory.LayerA.VariationalEinstein (R_metric_pair_symm)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D minkMetric4D fullConformalMetricDerivs)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs subMetricDerivs
  R_metric_zero R_metric_add R_metric_smul R_metric_sub
  lorentzianMetricTrace4D metricTraceHessian4D
  conformalPartMetricDerivs4D tracelessPartMetricDerivs4D
  conformalPartMetricDerivs4D_h_eq)
open KFCausalCurved4DLinearizedWeylRicciSplit (ricciCurvaturePart4D
  scalarCurvaturePart4D ricciScalarRiemannPart4D weylTensor4D
  riemann_eq_weyl_add_ricciScalar
  ricciScalarRiemannPart4D_zero ricciScalarRiemannPart4D_add
  ricciScalarRiemannPart4D_smul ricciScalarRiemannPart4D_sub
  weylTensor4D_zero weylTensor4D_add weylTensor4D_smul weylTensor4D_sub
  weylTensor4D_antisym1 weylTensor4D_antisym2 weylTensor4D_pair_symm
  weylTensor4D_fullConformal_eq_zero weylTensor4D_conformalPart_eq_zero
  weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DWeylElectricMagneticDecomposition (weylElectric4D weylMagnetic4D
  weylElectric4D_add weylMagnetic4D_add)

/-! ### 4D Tidal / Bivector Curvature Probe Functionals -/

/-- General quadrilinear contraction of a rank-4 4D tensor `T` against four
directional vectors `u v w z : Fin 4 → ℝ`. -/
def quadrilinearEval4D (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (u v w z : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
    u ρ * v σ * w μ * z ν * T ρ σ μ ν

/-- Full 4D Riemann tidal/bivector curvature probe functional
`R(u, v, w, z) = ∑_{ρ,σ,μ,ν} u_ρ v_σ w_μ z_ν R_{ρσμν}(md)`. -/
def riemannTidalProbe (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
    u ρ * v σ * w μ * z ν * R_metric md ρ σ μ ν

/-- 4D Weyl conformal tidal/bivector curvature probe functional
`C(u, v, w, z) = ∑_{ρ,σ,μ,ν} u_ρ v_σ w_μ z_ν C_{ρσμν}(md)`. -/
def weylTidalProbe (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
    u ρ * v σ * w μ * z ν * weylTensor4D md ρ σ μ ν

/-- 4D Ricci-Scalar (Kulkarni-Nomizu) tidal probe functional
`R^{(Ric,R)}(u, v, w, z) = ∑_{ρ,σ,μ,ν} u_ρ v_σ w_μ z_ν ricciScalarRiemannPart4D_{ρσμν}(md)`. -/
def ricciTidalProbe (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
    u ρ * v σ * w μ * z ν * ricciScalarRiemannPart4D md ρ σ μ ν

/-- Standard coordinate basis vector `e_α` in `ℝ⁴`. -/
def basisVec4D (α : Fin 4) : Fin 4 → ℝ :=
  fun β => if β = α then 1 else 0

/-- Exact Weyl + Ricci-Scalar decomposition of the 4D Riemann tidal probe:
`riemannTidalProbe u v w z md = weylTidalProbe u v w z md + ricciTidalProbe u v w z md`. -/
theorem riemannTidalProbe_eq_weyl_add_ricci (u v w z : Fin 4 → ℝ)
    (md : MetricDerivs 4) :
    riemannTidalProbe u v w z md =
      weylTidalProbe u v w z md + ricciTidalProbe u v w z md := by
  unfold riemannTidalProbe weylTidalProbe ricciTidalProbe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [(riemann_eq_weyl_add_ricciScalar md ρ σ μ ν).1]
  ring

/-! ### Linearity and Conformal Invariance of the 4D Tidal Probes -/

theorem riemannTidalProbe_zero (u v w z : Fin 4 → ℝ) :
    riemannTidalProbe u v w z (zeroMetricDerivs 4) = 0 := by
  unfold riemannTidalProbe
  apply Finset.sum_eq_zero; intro ρ _
  apply Finset.sum_eq_zero; intro σ _
  apply Finset.sum_eq_zero; intro μ _
  apply Finset.sum_eq_zero; intro ν _
  rw [R_metric_zero, mul_zero]

theorem riemannTidalProbe_add (u v w z : Fin 4 → ℝ)
    (md₁ md₂ : MetricDerivs 4) :
    riemannTidalProbe u v w z (addMetricDerivs md₁ md₂) =
      riemannTidalProbe u v w z md₁ + riemannTidalProbe u v w z md₂ := by
  unfold riemannTidalProbe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [R_metric_add]
  ring

theorem riemannTidalProbe_smul (u v w z : Fin 4 → ℝ)
    (r : ℝ) (md : MetricDerivs 4) :
    riemannTidalProbe u v w z (smulMetricDerivs r md) =
      r * riemannTidalProbe u v w z md := by
  unfold riemannTidalProbe
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ρ _
  apply Finset.sum_congr rfl; intro σ _
  apply Finset.sum_congr rfl; intro μ _
  apply Finset.sum_congr rfl; intro ν _
  rw [R_metric_smul]
  ring

theorem riemannTidalProbe_sub (u v w z : Fin 4 → ℝ)
    (md₁ md₂ : MetricDerivs 4) :
    riemannTidalProbe u v w z (subMetricDerivs md₁ md₂) =
      riemannTidalProbe u v w z md₁ - riemannTidalProbe u v w z md₂ := by
  unfold riemannTidalProbe
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [R_metric_sub]
  ring

theorem weylTidalProbe_zero (u v w z : Fin 4 → ℝ) :
    weylTidalProbe u v w z (zeroMetricDerivs 4) = 0 := by
  unfold weylTidalProbe
  apply Finset.sum_eq_zero; intro ρ _
  apply Finset.sum_eq_zero; intro σ _
  apply Finset.sum_eq_zero; intro μ _
  apply Finset.sum_eq_zero; intro ν _
  rw [weylTensor4D_zero, mul_zero]

theorem weylTidalProbe_add (u v w z : Fin 4 → ℝ)
    (md₁ md₂ : MetricDerivs 4) :
    weylTidalProbe u v w z (addMetricDerivs md₁ md₂) =
      weylTidalProbe u v w z md₁ + weylTidalProbe u v w z md₂ := by
  unfold weylTidalProbe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [weylTensor4D_add]
  ring

theorem weylTidalProbe_smul (u v w z : Fin 4 → ℝ)
    (r : ℝ) (md : MetricDerivs 4) :
    weylTidalProbe u v w z (smulMetricDerivs r md) =
      r * weylTidalProbe u v w z md := by
  unfold weylTidalProbe
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ρ _
  apply Finset.sum_congr rfl; intro σ _
  apply Finset.sum_congr rfl; intro μ _
  apply Finset.sum_congr rfl; intro ν _
  rw [weylTensor4D_smul]
  ring

theorem weylTidalProbe_sub (u v w z : Fin 4 → ℝ)
    (md₁ md₂ : MetricDerivs 4) :
    weylTidalProbe u v w z (subMetricDerivs md₁ md₂) =
      weylTidalProbe u v w z md₁ - weylTidalProbe u v w z md₂ := by
  unfold weylTidalProbe
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [weylTensor4D_sub]
  ring

/-- The Weyl tidal probe vanishes identically on any 4D conformal metric
perturbation `fullConformalMetricDerivs H K` with symmetric `H`. -/
theorem weylTidalProbe_fullConformal_eq_zero (u v w z : Fin 4 → ℝ)
    (H : Hessian4D) (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) :
    weylTidalProbe u v w z (fullConformalMetricDerivs H K) = 0 := by
  unfold weylTidalProbe
  apply Finset.sum_eq_zero; intro ρ _
  apply Finset.sum_eq_zero; intro σ _
  apply Finset.sum_eq_zero; intro μ _
  apply Finset.sum_eq_zero; intro ν _
  rw [weylTensor4D_fullConformal_eq_zero H hH K ρ σ μ ν, mul_zero]

/-- The Weyl tidal probe vanishes identically on `conformalPartMetricDerivs4D md`. -/
theorem weylTidalProbe_conformalPart_eq_zero (u v w z : Fin 4 → ℝ)
    (md : MetricDerivs 4) :
    weylTidalProbe u v w z (conformalPartMetricDerivs4D md) = 0 := by
  unfold weylTidalProbe
  apply Finset.sum_eq_zero; intro ρ _
  apply Finset.sum_eq_zero; intro σ _
  apply Finset.sum_eq_zero; intro μ _
  apply Finset.sum_eq_zero; intro ν _
  rw [weylTensor4D_conformalPart_eq_zero md ρ σ μ ν, mul_zero]

/-- Conformal invariance of the 4D Weyl tidal probe:
`weylTidalProbe u v w z md = weylTidalProbe u v w z (tracelessPartMetricDerivs4D md)`. -/
theorem weylTidalProbe_eq_tracelessPart (u v w z : Fin 4 → ℝ)
    (md : MetricDerivs 4) :
    weylTidalProbe u v w z md =
      weylTidalProbe u v w z (tracelessPartMetricDerivs4D md) := by
  unfold tracelessPartMetricDerivs4D
  rw [weylTidalProbe_sub, weylTidalProbe_conformalPart_eq_zero, sub_zero]

/-! ### Directional Bivector Symmetries and Exact Basis Extraction -/

theorem weylTidalProbe_antisym1 (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) :
    weylTidalProbe u v w z md = -weylTidalProbe v u w z md := by
  unfold weylTidalProbe
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [weylTensor4D_antisym1 md ρ σ μ ν]
  ring

theorem weylTidalProbe_antisym2 (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) :
    weylTidalProbe u v w z md = -weylTidalProbe u v z w md := by
  unfold weylTidalProbe
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro σ _
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro ν _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [weylTensor4D_antisym2 md ρ σ μ ν]
  ring

theorem weylTidalProbe_pair_symm (u v w z : Fin 4 → ℝ) (md : MetricDerivs 4) :
    weylTidalProbe u v w z md = weylTidalProbe w z u v md := by
  unfold weylTidalProbe
  have hswap1 : ∀ ρ σ : Fin 4,
      (∑ μ : Fin 4, ∑ ν : Fin 4, u ρ * v σ * w μ * z ν * weylTensor4D md ρ σ μ ν) =
      (∑ μ : Fin 4, ∑ ν : Fin 4, w μ * z ν * u ρ * v σ * weylTensor4D md μ ν ρ σ) := by
    intro ρ σ
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro ν _
    rw [weylTensor4D_pair_symm md ρ σ μ ν]
    ring
  simp_rw [hswap1]
  have hs1 : (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      w μ * z ν * u ρ * v σ * weylTensor4D md μ ν ρ σ) =
      ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ σ : Fin 4, ∑ ν : Fin 4,
        w μ * z ν * u ρ * v σ * weylTensor4D md μ ν ρ σ :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  rw [hs1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro μ _
  have hs2 : (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ ν : Fin 4,
      w μ * z ν * u ρ * v σ * weylTensor4D md μ ν ρ σ) =
      ∑ ρ : Fin 4, ∑ ν : Fin 4, ∑ σ : Fin 4,
        w μ * z ν * u ρ * v σ * weylTensor4D md μ ν ρ σ :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  rw [hs2, Finset.sum_comm]

/-- Evaluating `quadrilinearEval4D T` on coordinate basis vectors
`(basisVec4D ρ, basisVec4D σ, basisVec4D μ, basisVec4D ν)` extracts `T ρ σ μ ν`. -/
theorem quadrilinearEval4D_basis (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ρ σ μ ν : Fin 4) :
    quadrilinearEval4D T (basisVec4D ρ) (basisVec4D σ)
      (basisVec4D μ) (basisVec4D ν) = T ρ σ μ ν := by
  unfold quadrilinearEval4D basisVec4D
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Coordinate basis extraction of the full Riemann tensor `R_metric md ρ σ μ ν`. -/
theorem riemannTidalProbe_basis (ρ σ μ ν : Fin 4) (md : MetricDerivs 4) :
    riemannTidalProbe (basisVec4D ρ) (basisVec4D σ)
      (basisVec4D μ) (basisVec4D ν) md = R_metric md ρ σ μ ν :=
  quadrilinearEval4D_basis (R_metric md) ρ σ μ ν

/-- Coordinate basis extraction of the 4D Weyl tensor `weylTensor4D md ρ σ μ ν`. -/
theorem weylTidalProbe_basis (ρ σ μ ν : Fin 4) (md : MetricDerivs 4) :
    weylTidalProbe (basisVec4D ρ) (basisVec4D σ)
      (basisVec4D μ) (basisVec4D ν) md = weylTensor4D md ρ σ μ ν :=
  quadrilinearEval4D_basis (weylTensor4D md) ρ σ μ ν

/-- Coordinate basis extraction of `ricciScalarRiemannPart4D md ρ σ μ ν`. -/
theorem ricciTidalProbe_basis (ρ σ μ ν : Fin 4) (md : MetricDerivs 4) :
    ricciTidalProbe (basisVec4D ρ) (basisVec4D σ)
      (basisVec4D μ) (basisVec4D ν) md = ricciScalarRiemannPart4D md ρ σ μ ν :=
  quadrilinearEval4D_basis (ricciScalarRiemannPart4D md) ρ σ μ ν

/-- Extraction of the gravito-electric Weyl tensor `weylElectric4D md a b` via
`weylTidalProbe (basisVec4D 0) (basisVec4D a) (basisVec4D 0) (basisVec4D b) md`. -/
theorem weylTidalProbe_extract_electric (a b : Fin 4) (md : MetricDerivs 4) :
    weylTidalProbe (basisVec4D 0) (basisVec4D a)
      (basisVec4D 0) (basisVec4D b) md = weylElectric4D md a b :=
  weylTidalProbe_basis 0 a 0 b md

/-- Extraction of the gravito-magnetic Weyl tensor `weylMagnetic4D md a b c` via
`weylTidalProbe (basisVec4D 0) (basisVec4D a) (basisVec4D b) (basisVec4D c) md`. -/
theorem weylTidalProbe_extract_magnetic (a b c : Fin 4) (md : MetricDerivs 4) :
    weylTidalProbe (basisVec4D 0) (basisVec4D a)
      (basisVec4D b) (basisVec4D c) md = weylMagnetic4D md a b c :=
  weylTidalProbe_basis 0 a b c md

/-! ### Explicit Transverse-Traceless Gravitational-Wave Metric Perturbations -/

/-- Null wave covector `k_μ = (1, 0, 0, -1)` for a plane wave propagating in the
`+z` (`x³`) direction. -/
def nullWaveVec4D (e : Fin 4) : ℝ :=
  if e = 0 then 1 else if e = 3 then -1 else 0

/-- Transverse-traceless `+`-polarization tensor `e^+_{ab}(A)` in the `(x¹, x²)`
plane (`e^+_{11} = A`, `e^+_{22} = -A`, all other components `0`). -/
def plusPolarizationTensor4D (A : ℝ) (a b : Fin 4) : ℝ :=
  if a = 1 ∧ b = 1 then A
  else if a = 2 ∧ b = 2 then -A
  else 0

/-- Transverse-traceless `×`-polarization tensor `e^×_{ab}(B)` in the `(x¹, x²)`
plane (`e^×_{12} = e^×_{21} = B`, all other components `0`). -/
def crossPolarizationTensor4D (B : ℝ) (a b : Fin 4) : ℝ :=
  if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then B else 0

/-- Linearized 4D metric perturbation jet `plusWaveMetricDerivs4D A` for a
`+`-polarized gravitational wave of amplitude `A` propagating along `x³`:
`∂_e ∂_f h^+_{ab} = -2 k_e k_f e^+_{ab}(A)`. -/
def plusWaveMetricDerivs4D (A : ℝ) : MetricDerivs 4 where
  h := fun e f a b =>
    -2 * nullWaveVec4D e * nullWaveVec4D f * plusPolarizationTensor4D A a b
  h_metric := by
    intro e f a b
    unfold plusPolarizationTensor4D
    simp only [and_comm]
  h_comm := by
    intro e f a b; ring
  k := fun _ _ _ _ _ => 0
  k_metric := fun _ _ _ _ _ => rfl
  k_sym12 := fun _ _ _ _ _ => rfl
  k_sym23 := fun _ _ _ _ _ => rfl

/-- Linearized 4D metric perturbation jet `crossWaveMetricDerivs4D B` for a
`×`-polarized gravitational wave of amplitude `B` propagating along `x³`:
`∂_e ∂_f h^×_{ab} = -2 k_e k_f e^×_{ab}(B)`. -/
def crossWaveMetricDerivs4D (B : ℝ) : MetricDerivs 4 where
  h := fun e f a b =>
    -2 * nullWaveVec4D e * nullWaveVec4D f * crossPolarizationTensor4D B a b
  h_metric := by
    intro e f a b
    unfold crossPolarizationTensor4D
    have hiff : ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) ↔
        ((b = 1 ∧ a = 2) ∨ (b = 2 ∧ a = 1)) := by
      tauto
    by_cases h : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hb => h (hiff.mpr hb))]
  h_comm := by
    intro e f a b; ring
  k := fun _ _ _ _ _ => 0
  k_metric := fun _ _ _ _ _ => rfl
  k_sym12 := fun _ _ _ _ _ => rfl
  k_sym23 := fun _ _ _ _ _ => rfl

/-- `plusWaveMetricDerivs4D A` is strictly traceless: its Lorentzian metric trace,
`metricTraceHessian4D`, and `conformalPartMetricDerivs4D` all vanish identically. -/
theorem plusWave_traceless (A : ℝ) (e f a b : Fin 4) :
    lorentzianMetricTrace4D (plusWaveMetricDerivs4D A) e f = 0 ∧
    metricTraceHessian4D (plusWaveMetricDerivs4D A) e f = 0 ∧
    (conformalPartMetricDerivs4D (plusWaveMetricDerivs4D A)).h e f a b = 0 := by
  have htr : lorentzianMetricTrace4D (plusWaveMetricDerivs4D A) e f = 0 := by
    unfold lorentzianMetricTrace4D
    rw [Fin.sum_univ_four]
    dsimp [plusWaveMetricDerivs4D, plusPolarizationTensor4D, sign]
    ring
  have hH : metricTraceHessian4D (plusWaveMetricDerivs4D A) e f = 0 := by
    unfold metricTraceHessian4D
    rw [htr, mul_zero]
  have hC : (conformalPartMetricDerivs4D (plusWaveMetricDerivs4D A)).h e f a b = 0 := by
    rw [(conformalPartMetricDerivs4D_h_eq (plusWaveMetricDerivs4D A) e f a b).1, hH]
    ring
  exact ⟨htr, hH, hC⟩

/-- `crossWaveMetricDerivs4D B` is strictly traceless: its Lorentzian metric trace,
`metricTraceHessian4D`, and `conformalPartMetricDerivs4D` all vanish identically. -/
theorem crossWave_traceless (B : ℝ) (e f a b : Fin 4) :
    lorentzianMetricTrace4D (crossWaveMetricDerivs4D B) e f = 0 ∧
    metricTraceHessian4D (crossWaveMetricDerivs4D B) e f = 0 ∧
    (conformalPartMetricDerivs4D (crossWaveMetricDerivs4D B)).h e f a b = 0 := by
  have htr : lorentzianMetricTrace4D (crossWaveMetricDerivs4D B) e f = 0 := by
    unfold lorentzianMetricTrace4D
    rw [Fin.sum_univ_four]
    dsimp [crossWaveMetricDerivs4D, crossPolarizationTensor4D, sign]
    ring
  have hH : metricTraceHessian4D (crossWaveMetricDerivs4D B) e f = 0 := by
    unfold metricTraceHessian4D
    rw [htr, mul_zero]
  have hC : (conformalPartMetricDerivs4D (crossWaveMetricDerivs4D B)).h e f a b = 0 := by
    rw [(conformalPartMetricDerivs4D_h_eq (crossWaveMetricDerivs4D B) e f a b).1, hH]
    ring
  exact ⟨htr, hH, hC⟩

/-- `plusWaveMetricDerivs4D A` has identically zero Ricci tensor (`Ric_{bd} = 0`)
for all `b d : Fin 4`. -/
theorem plusWave_ricci_eq_zero (A : ℝ) (b d : Fin 4) :
    ricci (plusWaveMetricDerivs4D A) sign b d = 0 := by
  unfold ricci R_metric
  rw [Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;>
    { dsimp [plusWaveMetricDerivs4D, nullWaveVec4D, plusPolarizationTensor4D, sign]; ring }

/-- `crossWaveMetricDerivs4D B` has identically zero Ricci tensor (`Ric_{bd} = 0`)
for all `b d : Fin 4`. -/
theorem crossWave_ricci_eq_zero (B : ℝ) (b d : Fin 4) :
    ricci (crossWaveMetricDerivs4D B) sign b d = 0 := by
  unfold ricci R_metric
  rw [Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;>
    { dsimp [crossWaveMetricDerivs4D, nullWaveVec4D, crossPolarizationTensor4D, sign]; ring }

/-- `plusWaveMetricDerivs4D A` is an exact linearized Einstein-vacuum solution:
its scalar curvature, Einstein tensor, and `ricciScalarRiemannPart4D` vanish
identically, and its Riemann tensor is pure Weyl curvature (`R_metric = weylTensor4D`). -/
theorem plusWave_vacuum_pure_weyl (A : ℝ) :
    scalar (plusWaveMetricDerivs4D A) sign = 0 ∧
    (∀ b d : Fin 4, einstein (plusWaveMetricDerivs4D A) sign b d = 0) ∧
    (∀ a b c d : Fin 4, ricciScalarRiemannPart4D (plusWaveMetricDerivs4D A) a b c d = 0) ∧
    (∀ a b c d : Fin 4,
      weylTensor4D (plusWaveMetricDerivs4D A) a b c d =
        R_metric (plusWaveMetricDerivs4D A) a b c d) := by
  have hS : scalar (plusWaveMetricDerivs4D A) sign = 0 := by
    unfold scalar
    apply Finset.sum_eq_zero; intro b _
    rw [plusWave_ricci_eq_zero A b b, mul_zero]
  have hG : ∀ b d : Fin 4, einstein (plusWaveMetricDerivs4D A) sign b d = 0 := by
    intro b d; unfold einstein
    rw [plusWave_ricci_eq_zero A b d, hS]; ring
  have hRS : ∀ a b c d : Fin 4,
      ricciScalarRiemannPart4D (plusWaveMetricDerivs4D A) a b c d = 0 := by
    intro a b c d
    unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
    rw [plusWave_ricci_eq_zero, plusWave_ricci_eq_zero,
      plusWave_ricci_eq_zero, plusWave_ricci_eq_zero, hS]
    ring
  refine ⟨hS, hG, hRS, fun a b c d => ?_⟩
  unfold weylTensor4D
  rw [hRS a b c d, sub_zero]

/-- `crossWaveMetricDerivs4D B` is an exact linearized Einstein-vacuum solution:
its scalar curvature, Einstein tensor, and `ricciScalarRiemannPart4D` vanish
identically, and its Riemann tensor is pure Weyl curvature (`R_metric = weylTensor4D`). -/
theorem crossWave_vacuum_pure_weyl (B : ℝ) :
    scalar (crossWaveMetricDerivs4D B) sign = 0 ∧
    (∀ b d : Fin 4, einstein (crossWaveMetricDerivs4D B) sign b d = 0) ∧
    (∀ a b c d : Fin 4, ricciScalarRiemannPart4D (crossWaveMetricDerivs4D B) a b c d = 0) ∧
    (∀ a b c d : Fin 4,
      weylTensor4D (crossWaveMetricDerivs4D B) a b c d =
        R_metric (crossWaveMetricDerivs4D B) a b c d) := by
  have hS : scalar (crossWaveMetricDerivs4D B) sign = 0 := by
    unfold scalar
    apply Finset.sum_eq_zero; intro b _
    rw [crossWave_ricci_eq_zero B b b, mul_zero]
  have hG : ∀ b d : Fin 4, einstein (crossWaveMetricDerivs4D B) sign b d = 0 := by
    intro b d; unfold einstein
    rw [crossWave_ricci_eq_zero B b d, hS]; ring
  have hRS : ∀ a b c d : Fin 4,
      ricciScalarRiemannPart4D (crossWaveMetricDerivs4D B) a b c d = 0 := by
    intro a b c d
    unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
    rw [crossWave_ricci_eq_zero, crossWave_ricci_eq_zero,
      crossWave_ricci_eq_zero, crossWave_ricci_eq_zero, hS]
    ring
  refine ⟨hS, hG, hRS, fun a b c d => ?_⟩
  unfold weylTensor4D
  rw [hRS a b c d, sub_zero]

/-- Exact gravito-electric and gravito-magnetic Weyl components of the `+`-polarized
gravitational wave `plusWaveMetricDerivs4D A`:
`E_{11} = A`, `E_{22} = -A`, `E_{12} = 0`, `B_{131} = -A`, `B_{232} = A`, `B_{132} = 0`. -/
theorem plusWave_electric_and_magnetic_components (A : ℝ) :
    weylElectric4D (plusWaveMetricDerivs4D A) 1 1 = A ∧
    weylElectric4D (plusWaveMetricDerivs4D A) 2 2 = -A ∧
    weylElectric4D (plusWaveMetricDerivs4D A) 1 2 = 0 ∧
    weylElectric4D (plusWaveMetricDerivs4D A) 3 3 = 0 ∧
    weylMagnetic4D (plusWaveMetricDerivs4D A) 1 3 1 = -A ∧
    weylMagnetic4D (plusWaveMetricDerivs4D A) 2 3 2 = A ∧
    weylMagnetic4D (plusWaveMetricDerivs4D A) 1 3 2 = 0 := by
  have hW := (plusWave_vacuum_pure_weyl A).2.2.2
  unfold weylElectric4D weylMagnetic4D
  rw [hW 0 1 0 1, hW 0 2 0 2, hW 0 1 0 2, hW 0 3 0 3,
    hW 0 1 3 1, hW 0 2 3 2, hW 0 1 3 2]
  dsimp [R_metric, plusWaveMetricDerivs4D, nullWaveVec4D, plusPolarizationTensor4D]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- Exact gravito-electric and gravito-magnetic Weyl components of the `×`-polarized
gravitational wave `crossWaveMetricDerivs4D B`:
`E_{12} = B`, `E_{21} = B`, `E_{11} = 0`, `E_{22} = 0`, `B_{132} = -B`, `B_{231} = -B`, `B_{131} = 0`. -/
theorem crossWave_electric_and_magnetic_components (B : ℝ) :
    weylElectric4D (crossWaveMetricDerivs4D B) 1 2 = B ∧
    weylElectric4D (crossWaveMetricDerivs4D B) 2 1 = B ∧
    weylElectric4D (crossWaveMetricDerivs4D B) 1 1 = 0 ∧
    weylElectric4D (crossWaveMetricDerivs4D B) 2 2 = 0 ∧
    weylMagnetic4D (crossWaveMetricDerivs4D B) 1 3 2 = -B ∧
    weylMagnetic4D (crossWaveMetricDerivs4D B) 2 3 1 = -B ∧
    weylMagnetic4D (crossWaveMetricDerivs4D B) 1 3 1 = 0 := by
  have hW := (crossWave_vacuum_pure_weyl B).2.2.2
  unfold weylElectric4D weylMagnetic4D
  rw [hW 0 1 0 2, hW 0 2 0 1, hW 0 1 0 1, hW 0 2 0 2,
    hW 0 1 3 2, hW 0 2 3 1, hW 0 1 3 1]
  dsimp [R_metric, crossWaveMetricDerivs4D, nullWaveVec4D, crossPolarizationTensor4D]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- Simultaneous tidal-probe extraction of both gravitational-wave polarization
amplitudes `(A, B)` from the combined wave `addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)`. -/
theorem gravitationalWave_tidalProbe_polarization_extraction (A B : ℝ) :
    let mdGW := addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 1) mdGW = A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 2) (basisVec4D 0) (basisVec4D 2) mdGW = -A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 2) mdGW = B ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 3) (basisVec4D 1) mdGW = -A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 3) (basisVec4D 2) mdGW = -B := by
  intro mdGW
  have hplus := plusWave_electric_and_magnetic_components A
  have hcross := crossWave_electric_and_magnetic_components B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [weylTidalProbe_extract_electric, weylElectric4D_add, hplus.1, hcross.2.2.1]; ring
  · rw [weylTidalProbe_extract_electric, weylElectric4D_add, hplus.2.1, hcross.2.2.2.1]; ring
  · rw [weylTidalProbe_extract_electric, weylElectric4D_add, hplus.2.2.1, hcross.1]; ring
  · rw [weylTidalProbe_extract_magnetic, weylMagnetic4D_add, hplus.2.2.2.2.1, hcross.2.2.2.2.2.2]; ring
  · rw [weylTidalProbe_extract_magnetic, weylMagnetic4D_add, hplus.2.2.2.2.2.2, hcross.2.2.2.2.1]; ring

#print axioms riemannTidalProbe_eq_weyl_add_ricci
#print axioms riemannTidalProbe_zero
#print axioms riemannTidalProbe_add
#print axioms riemannTidalProbe_smul
#print axioms riemannTidalProbe_sub
#print axioms weylTidalProbe_zero
#print axioms weylTidalProbe_add
#print axioms weylTidalProbe_smul
#print axioms weylTidalProbe_sub
#print axioms weylTidalProbe_fullConformal_eq_zero
#print axioms weylTidalProbe_conformalPart_eq_zero
#print axioms weylTidalProbe_eq_tracelessPart
#print axioms weylTidalProbe_antisym1
#print axioms weylTidalProbe_antisym2
#print axioms weylTidalProbe_pair_symm
#print axioms quadrilinearEval4D_basis
#print axioms riemannTidalProbe_basis
#print axioms weylTidalProbe_basis
#print axioms ricciTidalProbe_basis
#print axioms weylTidalProbe_extract_electric
#print axioms weylTidalProbe_extract_magnetic
#print axioms plusWave_traceless
#print axioms crossWave_traceless
#print axioms plusWave_ricci_eq_zero
#print axioms crossWave_ricci_eq_zero
#print axioms plusWave_vacuum_pure_weyl
#print axioms crossWave_vacuum_pure_weyl
#print axioms plusWave_electric_and_magnetic_components
#print axioms crossWave_electric_and_magnetic_components
#print axioms gravitationalWave_tidalProbe_polarization_extraction

end
end UnifiedTheory.Audit.KFCausalCurved4DTidalWeylProbeExtraction
