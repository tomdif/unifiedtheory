/- The full interacting Wilson slab is an actual compact self-adjoint operator
on complex L² of spatial product Haar measure. Spatial plaquette weights and
all temporal-link gauge integration remain in its kernel. This is an
unnormalized finite-cutoff operator, not a continuum construction or a
cutoff-uniform spectral theorem. -/
import UnifiedTheory.Clay.YangMills.CompactKernelOperator
import UnifiedTheory.Clay.YangMills.WilsonSlabGauge
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabOperator
noncomputable section
open MeasureTheory WilsonTimeSlab
open scoped ENNReal InnerProductSpace

abbrev Q := SU2QuaternionEquivalence.UnitQuaternion
abbrev Slice (n : ℕ) := SpatialLinks n Q

variable (n : ℕ) [NeZero n]

/-- Normalized product Haar on every spatial link of the actual slice. -/
abbrev measure : Measure (Slice n) := WilsonSlabGauge.spatialHaar

abbrev Hilbert := Lp ℂ 2 (measure n)

/-- The full kernel includes both spatial potentials and temporal Haar integration. -/
def kernelMap (β : ℝ) : C(Slice n × Slice n, ℝ) :=
  ⟨fun uv => kernel WilsonSingleLinkStaples.character β 2 uv.1 uv.2,
    kernel_continuous _ WilsonSingleLinkStaples.character_continuous β 2⟩

/-- The genuine complex L² Wilson transfer operator at finite cutoff. -/
def transfer (β : ℝ) : Hilbert n →L[ℂ] Hilbert n :=
  CompactKernelOperator.operator (measure n) (kernelMap n β)

/-- Every L² input has this continuous output representative. -/
def representative (β : ℝ) (f : Hilbert n) : C(Slice n, ℂ) :=
  CompactKernelOperator.smoothing (measure n) (kernelMap n β) f

theorem representative_integral (β : ℝ) (f : Hilbert n) (u : Slice n) :
    representative n β f u =
      ∫ v, (kernel WilsonSingleLinkStaples.character β 2 u v : ℂ) * f v ∂measure n :=
  CompactKernelOperator.smoothing_integral (measure n) (kernelMap n β) f u

theorem transfer_integral (β : ℝ) (f : Hilbert n) :
    transfer n β f =ᵐ[measure n]
      (fun u => ∫ v, (kernel WilsonSingleLinkStaples.character β 2 u v : ℂ) * f v ∂measure n) :=
  CompactKernelOperator.operator_integral (measure n) (kernelMap n β) f

theorem transfer_norm_le (β : ℝ) : ‖transfer n β‖ ≤ ‖kernelMap n β‖ :=
  CompactKernelOperator.operator_norm_le (measure n) (kernelMap n β)

/-- Compactness is derived from the full continuous kernel. -/
theorem transfer_compact (β : ℝ) : IsCompactOperator (transfer n β) :=
  CompactKernelOperator.operator_compact (measure n) (kernelMap n β)

theorem kernelMap_symm (β : ℝ) (u v : Slice n) : kernelMap n β (u, v) = kernelMap n β (v, u) :=
  WilsonSlabGauge.kernel_symm _ WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 u v

/-- Actual Wilson symmetry gives the full L² adjoint identity. -/
theorem transfer_selfAdjoint (β : ℝ) : IsSelfAdjoint (transfer n β) :=
  CompactKernelOperator.operator_selfAdjoint (measure n) (kernelMap n β) (kernelMap_symm n β)

/-- Temporal gauge integration makes every continuous output representative gauge invariant. -/
theorem representative_gauge (β : ℝ) (f : Hilbert n) (h : SliceGauge n Q) (u : Slice n) :
    representative n β f (gaugeSlice h u) = representative n β f u := by
  simp only [representative_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [WilsonSlabGauge.kernel_gauge_left _ WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re]


/-- Strict pointwise positivity supplies a positive total kernel mass. This is
not the stronger assertion that the transfer quadratic form is nonnegative. -/
theorem total_kernel_mass_pos (β : ℝ) :
    0 < ∫ uv, kernelMap n β uv ∂(measure n).prod (measure n) := by
  have hpos : ∀ uv, 0 < kernelMap n β uv := fun uv =>
    kernel_positive _ WilsonSingleLinkStaples.character_continuous β 2 uv.1 uv.2
  have hi : Integrable (kernelMap n β) ((measure n).prod (measure n)) :=
    (kernelMap n β).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply (integral_pos_iff_support_of_nonneg (fun uv => (hpos uv).le) hi).mpr
  have hs : Function.support (kernelMap n β) = Set.univ := by
    ext uv
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos uv)
  simp [hs]

/-- The constant test has the actual full kernel mass as its quadratic pairing. -/
theorem transfer_one_pairing (β : ℝ) :
    inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ (1 : C(Slice n, ℂ)))
      (transfer n β (ContinuousMap.toLp 2 (measure n) ℂ (1 : C(Slice n, ℂ)))) =
      (∫ uv, kernelMap n β uv ∂(measure n).prod (measure n) : ℝ) := by
  change inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ (1 : C(Slice n, ℂ)))
    (ContinuousMap.toLp 2 (measure n) ℂ
      (CompactKernelOperator.smoothing (measure n) (kernelMap n β)
        (ContinuousMap.toLp 2 (measure n) ℂ (1 : C(Slice n, ℂ))))) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp only [ContinuousMap.one_apply, map_one, mul_one]
  simp_rw [CompactKernelOperator.smoothing_continuous_input, ContinuousMap.one_apply, mul_one]
  rw [← integral_complex_ofReal]
  have hi : Integrable (fun uv => (kernelMap n β uv : ℂ))
      ((measure n).prod (measure n)) :=
    (Complex.continuous_ofReal.comp (kernelMap n β).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_prod _ hi).symm

/-- The full interacting finite-cutoff operator is nonzero. -/
theorem transfer_ne_zero (β : ℝ) : transfer n β ≠ 0 := by
  intro hz
  have h := transfer_one_pairing n β
  rw [hz] at h
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at h
  have hm : (∫ uv, kernelMap n β uv ∂(measure n).prod (measure n) : ℝ) = 0 := by
    exact_mod_cast h.symm
  exact (ne_of_gt (total_kernel_mass_pos n β)) hm

end
end UnifiedTheory.Clay.YangMills.WilsonSlabOperator
