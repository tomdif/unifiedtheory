/- Measurable, possibly unbounded, multiplication relations pass through
Bochner integrals when both Hilbert curves are integrable. Two bounded
multipliers and a nonzero reciprocal justify the interchange without
point evaluation on arbitrary L2 integrals. -/
import UnifiedTheory.Audit.KFCausalContractiveMultiplier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def reciprocal (w : X → ℂ) (x : X) : ℂ := ((1+‖w x‖:ℝ):ℂ)⁻¹
def normalized (w : X → ℂ) (x : X) : ℂ := reciprocal w x*w x

theorem reciprocal_measurable (w : X → ℂ) (hw : Measurable w) :
    Measurable (reciprocal w) := by
  unfold reciprocal
  exact (Complex.measurable_ofReal.comp (measurable_const.add hw.norm)).inv

theorem normalized_measurable (w : X → ℂ) (hw : Measurable w) :
    Measurable (normalized w) := (reciprocal_measurable w hw).mul hw

omit [MeasurableSpace X] in
theorem reciprocal_ne_zero (w : X → ℂ) (x : X) : reciprocal w x ≠ 0 := by
  apply inv_ne_zero
  exact Complex.ofReal_ne_zero.mpr (by positivity)

omit [MeasurableSpace X] in
theorem reciprocal_bound (w : X → ℂ) (x : X) : ‖reciprocal w x‖ ≤ 1 := by
  rw [reciprocal,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (w x)])

omit [MeasurableSpace X] in
theorem normalized_bound (w : X → ℂ) (x : X) : ‖normalized w x‖ ≤ 1 := by
  rw [normalized,norm_mul,reciprocal,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity),mul_comm,← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg (w x)])

def relation (w : X → ℂ) (f g : Lp ℂ 2 μ) : Prop :=
  g =ᵐ[μ] fun x => w x*f x

theorem relation_iff_bounded (w : X → ℂ) (hw : Measurable w) (f g : Lp ℂ 2 μ) :
    relation w f g ↔
      multiplyL (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g =
        multiplyL (normalized w) (normalized_measurable w hw) (normalized_bound w) f := by
  constructor
  · intro hg
    apply Lp.ext
    filter_upwards [hg,
      multiplyL_coe (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g,
      multiplyL_coe (normalized w) (normalized_measurable w hw) (normalized_bound w) f]
      with x hx hu hv
    rw [hu,hv,hx]
    exact (mul_assoc _ _ _).symm
  · intro he
    filter_upwards [
      multiplyL_coe (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g,
      multiplyL_coe (normalized w) (normalized_measurable w hw) (normalized_bound w) f]
      with x hu hv
    have hx := congrArg (fun u : Lp ℂ 2 μ => u x) he
    dsimp only at hx
    rw [hu,hv] at hx
    exact mul_left_cancel₀ (reciprocal_ne_zero w _) (hx.trans (mul_assoc _ _ _))

theorem relation_smul (w : X → ℂ) (hw : Measurable w) (f g : Lp ℂ 2 μ)
    (hfg : relation w f g) (c : ℂ) : relation w (c • f) (c • g) := by
  apply (relation_iff_bounded w hw _ _).mpr
  simp only [map_smul]
  rw [(relation_iff_bounded w hw f g).mp hfg]

theorem relation_sum {ι : Type*} (w : X → ℂ) (hw : Measurable w)
    (s : Finset ι) (f g : ι → Lp ℂ 2 μ) (hfg : ∀ i ∈ s, relation w (f i) (g i)) :
    relation w (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  apply (relation_iff_bounded w hw _ _).mpr
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => (relation_iff_bounded w hw _ _).mp (hfg i hi))

theorem relation_integral {T : Type*} [MeasurableSpace T] {ν : Measure T}
    (w : X → ℂ) (hw : Measurable w) (f g : T → Lp ℂ 2 μ)
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hfg : ∀ᵐ t ∂ν, relation w (f t) (g t)) :
    relation w (∫ t, f t ∂ν) (∫ t, g t ∂ν) := by
  apply (relation_iff_bounded w hw _ _).mpr
  rw [← (multiplyL (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w)).integral_comp_comm hg,
    ← (multiplyL (normalized w) (normalized_measurable w hw) (normalized_bound w)).integral_comp_comm hf]
  apply integral_congr_ae
  filter_upwards [hfg] with t ht
  exact (relation_iff_bounded w hw _ _).mp ht

theorem integral_weight_memLp {T : Type*} [MeasurableSpace T] {ν : Measure T}
    (w : X → ℂ) (hw : Measurable w) (f g : T → Lp ℂ 2 μ)
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hfg : ∀ᵐ t ∂ν, relation w (f t) (g t)) :
    MemLp (fun x => w x*(∫ t, f t ∂ν : Lp ℂ 2 μ) x) 2 μ :=
  (Lp.memLp (∫ t, g t ∂ν)).ae_eq (relation_integral w hw f g hf hg hfg)

#print axioms reciprocal_measurable
#print axioms normalized_measurable
#print axioms reciprocal_ne_zero
#print axioms reciprocal_bound
#print axioms normalized_bound
#print axioms relation_iff_bounded
#print axioms relation_smul
#print axioms relation_sum
#print axioms relation_integral
#print axioms integral_weight_memLp
end
end UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
