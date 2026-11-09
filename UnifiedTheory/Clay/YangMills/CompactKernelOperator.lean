/- Continuous real kernels on compact probability spaces define actual bounded
complex L² integral operators. Compactness follows from Arzelà–Ascoli, and
symmetric kernels give self-adjoint operators by Fubini and density. These
finite-space constructions supply no cutoff-uniform spectral estimates. -/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactKernelOperator
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace BoundedContinuousFunction ComplexConjugate

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

abbrev Hilbert := Lp ℂ 2 μ

/-- The actual real kernel row, regarded as a continuous complex function. -/
def rowContinuous (K : C(X × X, ℝ)) (x : X) : C(X, ℂ) :=
  ⟨fun y => (K (x, y) : ℂ), Complex.continuous_ofReal.comp
    (K.continuous.comp (continuous_const.prodMk continuous_id))⟩

/-- The row is an actual L² equivalence class, not an independently supplied vector. -/
def row (K : C(X × X, ℝ)) (x : X) : Hilbert μ :=
  ContinuousMap.toLp 2 μ ℂ (rowContinuous K x)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem rowContinuous_continuous (K : C(X × X, ℝ)) : Continuous (rowContinuous K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact Complex.continuous_ofReal.comp K.continuous

theorem row_continuous (K : C(X × X, ℝ)) : Continuous (row μ K) :=
  (ContinuousMap.toLp 2 μ ℂ).continuous.comp (rowContinuous_continuous K)

theorem embedding_norm_le : ‖(ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Hilbert μ)‖ ≤ 1 := by
  have h := ContinuousMap.toLp_norm_le (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ
  simpa [measureUnivNNReal, measure_univ] using h

omit [MeasurableSpace X] [BorelSpace X] in
theorem rowContinuous_norm_le (K : C(X × X, ℝ)) (x : X) :
    ‖rowContinuous K x‖ ≤ ‖K‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
  intro y
  simpa only [rowContinuous, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs]
    using K.norm_coe_le_norm (x, y)

theorem row_norm_le (K : C(X × X, ℝ)) (x : X) : ‖row μ K x‖ ≤ ‖K‖ := by
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Hilbert μ)‖ * ‖rowContinuous K x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖rowContinuous K x‖ :=
      mul_le_mul_of_nonneg_right (embedding_norm_le μ) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using rowContinuous_norm_le K x

/-- The continuous representative obtained by integrating a genuine L² vector. -/
def smoothing (K : C(X × X, ℝ)) (f : Hilbert μ) : C(X, ℂ) :=
  ⟨fun x => inner ℂ (row μ K x) f, (row_continuous μ K).inner continuous_const⟩

theorem smoothing_norm_le (K : C(X × X, ℝ)) (f : Hilbert μ) :
    ‖smoothing μ K f‖ ≤ ‖K‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg K) (norm_nonneg f))).mpr
  intro x
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (row_norm_le μ K x) (norm_nonneg f))

/-- The kernel integral is complex linear in its input vector. -/
def smoothingLinear (K : C(X × X, ℝ)) : Hilbert μ →ₗ[ℂ] C(X, ℂ) where
  toFun := smoothing μ K
  map_add' f g := by
    ext x
    change inner ℂ (row μ K x) (f + g) = inner ℂ (row μ K x) f + inner ℂ (row μ K x) g
    exact inner_add_right _ _ _
  map_smul' c f := by
    ext x
    change inner ℂ (row μ K x) (c • f) = c * inner ℂ (row μ K x) f
    exact inner_smul_right _ _ _

def smoothingOperator (K : C(X × X, ℝ)) : Hilbert μ →L[ℂ] C(X, ℂ) :=
  (smoothingLinear μ K).mkContinuous ‖K‖ (smoothing_norm_le μ K)

/-- The actual bounded complex L² integral operator. -/
def operator (K : C(X × X, ℝ)) : Hilbert μ →L[ℂ] Hilbert μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp (smoothingOperator μ K)

theorem smoothingOperator_norm_le (K : C(X × X, ℝ)) : ‖smoothingOperator μ K‖ ≤ ‖K‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg K) (smoothing_norm_le μ K)

theorem operator_norm_le (K : C(X × X, ℝ)) : ‖operator μ K‖ ≤ ‖K‖ := by
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Hilbert μ)‖ *
        ‖smoothingOperator μ K‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖K‖ := mul_le_mul (embedding_norm_le μ) (smoothingOperator_norm_le μ K)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem smoothing_integral (K : C(X × X, ℝ)) (f : Hilbert μ) (x : X) :
    smoothing μ K f x = ∫ y, (K (x, y) : ℂ) * f y ∂μ := by
  change inner ℂ (row μ K x) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hrow := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ (rowContinuous K x)
  filter_upwards [hrow] with y hy
  change row μ K x y = (K (x, y) : ℂ) at hy
  rw [hy]
  simp [mul_comm]

/-- Equality almost everywhere with the actual kernel integral, for every L² input. -/
theorem operator_integral (K : C(X × X, ℝ)) (f : Hilbert μ) :
    operator μ K f =ᵐ[μ] (fun x => ∫ y, (K (x, y) : ℂ) * f y ∂μ) := by
  have h := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ (smoothing μ K f)
  filter_upwards [h] with x hx
  exact hx.trans (smoothing_integral μ K f x)

theorem smoothing_continuous_input (K : C(X × X, ℝ)) (f : C(X, ℂ)) (x : X) :
    smoothing μ K (ContinuousMap.toLp 2 μ ℂ f) x = ∫ y, (K (x, y) : ℂ) * f y ∂μ := by
  rw [smoothing_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ f] with y hy
  rw [hy]


/-- The modulus of the kernel rows controls the entire image of the L² unit ball. -/
theorem smoothing_dist_le (K : C(X × X, ℝ)) (f : Hilbert μ) (hf : ‖f‖ ≤ 1)
    (x y : X) : dist (smoothing μ K f x) (smoothing μ K f y) ≤ dist (row μ K x) (row μ K y) := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖inner ℂ (row μ K x) f - inner ℂ (row μ K y) f‖ ≤ _
  rw [← inner_sub_left]
  exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hf)

/-- Compactness is derived from the actual kernel rows by Arzelà–Ascoli. -/
theorem smoothingOperator_compact (K : C(X × X, ℝ)) :
    IsCompactOperator (smoothingOperator μ K) := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact X ℂ ℂ
  let S : Hilbert μ →L[ℂ] (X →ᵇ ℂ) :=
    e.toLinearIsometry.toContinuousLinearMap.comp (smoothingOperator μ K)
  let A : Set (X →ᵇ ℂ) := S '' Metric.closedBall 0 1
  have hA : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 ‖K‖)
      (isCompact_closedBall _ _) A
    · intro f x hf
      obtain ⟨g, hg, rfl⟩ := hf
      have hg' : ‖g‖ ≤ 1 := by simpa using hg
      change dist (smoothing μ K g x) 0 ≤ ‖K‖
      rw [dist_zero_right]
      exact ((smoothing μ K g).norm_coe_le_norm x).trans
        ((smoothing_norm_le μ K g).trans (mul_le_of_le_one_right (norm_nonneg K) hg'))
    · intro x
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      have he := (row_continuous μ K).continuousAt.eventually
        (Metric.ball_mem_nhds (row μ K x) hε)
      filter_upwards [he] with y hy
      intro f
      obtain ⟨g, hg, hgf⟩ := f.property
      have hg' : ‖g‖ ≤ 1 := by simpa using hg
      change dist ((f : X →ᵇ ℂ) x) ((f : X →ᵇ ℂ) y) < ε
      rw [← hgf]
      exact (smoothing_dist_le μ K g hg' x y).trans_lt (by simpa [dist_comm] using hy)
  have hS : IsCompactOperator S :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall S.toLinearMap
      (by norm_num : (0 : ℝ) < 1)).mpr hA
  have h := hS.clm_comp e.symm.toLinearIsometry.toContinuousLinearMap
  convert h using 1

/-- Every continuous real kernel on a compact probability space defines a compact L² operator. -/
theorem operator_compact (K : C(X × X, ℝ)) : IsCompactOperator (operator μ K) :=
  (smoothingOperator_compact μ K).clm_comp (ContinuousMap.toLp 2 μ ℂ)


variable [SecondCountableTopology X]

/-- Symmetry first holds on genuine continuous test functions by Fubini. -/
theorem operator_inner_continuous (K : C(X × X, ℝ))
    (hK : ∀ x y, K (x, y) = K (y, x)) (f g : C(X, ℂ)) :
    inner ℂ (operator μ K (ContinuousMap.toLp 2 μ ℂ f))
        (ContinuousMap.toLp 2 μ ℂ g) =
      inner ℂ (ContinuousMap.toLp 2 μ ℂ f)
        (operator μ K (ContinuousMap.toLp 2 μ ℂ g)) := by
  change inner ℂ (ContinuousMap.toLp 2 μ ℂ (smoothing μ K (ContinuousMap.toLp 2 μ ℂ f)))
      (ContinuousMap.toLp 2 μ ℂ g) =
    inner ℂ (ContinuousMap.toLp 2 μ ℂ f)
      (ContinuousMap.toLp 2 μ ℂ (smoothing μ K (ContinuousMap.toLp 2 μ ℂ g)))
  rw [MeasureTheory.ContinuousMap.inner_toLp, MeasureTheory.ContinuousMap.inner_toLp]
  simp_rw [smoothing_continuous_input, ← integral_conj, ← integral_const_mul,
    ← integral_mul_const]
  have hi : Integrable (fun xy : X × X =>
      g xy.1 * conj ((K xy : ℂ) * f xy.2)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, Complex.conj_ofReal, hK x y]
  ring

variable [NormalSpace X] [μ.WeaklyRegular]

/-- The bounded operator is symmetric on all of L², not merely on continuous tests. -/
theorem operator_symmetric (K : C(X × X, ℝ))
    (hK : ∀ x y, K (x, y) = K (y, x)) :
    (operator μ K).toLinearMap.IsSymmetric := by
  intro f g
  apply (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction_on₂
    (p := fun f g => inner ℂ (operator μ K f) g = inner ℂ f (operator μ K g))
  · apply isClosed_eq
    · exact ((operator μ K).continuous.comp continuous_fst).inner continuous_snd
    · exact continuous_fst.inner ((operator μ K).continuous.comp continuous_snd)
  · exact operator_inner_continuous μ K hK

/-- Symmetry of the real kernel gives the Hilbert-space adjoint identity. -/
theorem operator_selfAdjoint (K : C(X × X, ℝ))
    (hK : ∀ x y, K (x, y) = K (y, x)) : IsSelfAdjoint (operator μ K) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (operator_symmetric μ K hK)

end
end UnifiedTheory.Clay.YangMills.CompactKernelOperator
