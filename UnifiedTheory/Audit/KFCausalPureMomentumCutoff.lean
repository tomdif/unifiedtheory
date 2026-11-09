/- Bounded signed momentum cutoffs in the actual clock-Fourier coordinates.
The first-moment limit requires the proved absolute-moment domain; no
propagation of that domain is assumed or inferred. -/
import UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
import UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPureMomentumCutoff
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation (multiplier_real_pairing)

def value (b x : ℝ) : ℝ := x/(1+b*|x|)

theorem denominator_positive (b x : ℝ) (hb : 0 ≤ b) : 0 < 1+b*|x| := by positivity

theorem value_abs_le (b x : ℝ) (hb : 0 ≤ b) : |value b x| ≤ |x| := by
  rw [value,abs_div,abs_of_pos (denominator_positive b x hb)]
  exact div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg hb (abs_nonneg x)])

theorem scaled_value_bound (b x : ℝ) (hb : 0 < b) : |b*value b x| ≤ 1 := by
  rw [abs_mul,abs_of_pos hb,value,abs_div,abs_of_pos (denominator_positive b x hb.le)]
  rw [← mul_div_assoc]
  exact (div_le_one (denominator_positive b x hb.le)).mpr (by linarith)

theorem value_tendsto (b : ℕ → ℝ) (hz : Tendsto b atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => value (b n) x) atTop (𝓝 x) := by
  have ht := (tendsto_const_nhds (x := x)).div (tendsto_const_nhds.add (hz.mul_const |x|))
    (by norm_num : (1:ℝ)+0*|x| ≠ 0)
  simpa only [zero_mul,add_zero,div_one,value] using ht

section General
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}
  (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) (b : ℝ) (hb : 0 < b)

def weight (x : X) : ℂ := ((b*value b (w x):ℝ):ℂ)

include hm in
theorem weight_measurable : Measurable (weight w b) := by
  unfold weight value
  exact Complex.continuous_ofReal.measurable.comp
    (measurable_const.mul (hm.div (measurable_const.add (measurable_const.mul (continuous_abs.measurable.comp hm)))))

omit [MeasurableSpace X] in
include hb in
theorem weight_bound (x : X) : ‖weight w b x‖ ≤ 1 := by
  simpa only [weight,Complex.norm_real,Real.norm_eq_abs] using scaled_value_bound b (w x) hb

def operator : H →L[ℂ] H := b⁻¹ •
  (Ω.symm : Lp ℂ 2 μ →L[ℂ] H).comp
    ((multiplyL (weight w b) (weight_measurable w hm b) (weight_bound w b hb)).comp
      (Ω : H →L[ℂ] Lp ℂ 2 μ))

theorem operator_coordinates (f : H) :
    Ω (operator Ω w hm b hb f) =ᵐ[μ] fun x => (value b (w x):ℂ)*(Ω f) x := by
  have he : Ω (operator Ω w hm b hb f) =
      (b⁻¹:ℝ) • multiplyL (weight w b) (weight_measurable w hm b) (weight_bound w b hb) (Ω f) := by
    change Ω ((b⁻¹:ℝ) • Ω.symm (multiplyL (weight w b)
      (weight_measurable w hm b) (weight_bound w b hb) (Ω f))) = _
    exact ((Ω : H →L[ℂ] Lp ℂ 2 μ).map_smul_of_tower _ _).trans
      (congrArg (fun z : Lp ℂ 2 μ => (b⁻¹:ℝ) • z) (Ω.apply_symm_apply _))
  rw [he]
  filter_upwards [Lp.coeFn_smul (b⁻¹:ℝ)
      (multiplyL (weight w b) (weight_measurable w hm b) (weight_bound w b hb) (Ω f)),
    multiplyL_coe (weight w b) (weight_measurable w hm b) (weight_bound w b hb) (Ω f)] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply,hy,weight,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    inv_mul_cancel₀ hb.ne',one_mul]

theorem operator_norm (f : H) : ‖operator Ω w hm b hb f‖ ≤ b⁻¹*‖f‖ := by
  change ‖(b⁻¹:ℝ) • Ω.symm (multiplyL (weight w b)
    (weight_measurable w hm b) (weight_bound w b hb) (Ω f))‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb),Ω.symm.norm_map]
  exact mul_le_mul_of_nonneg_left
    ((multiply_norm_le (weight w b) (weight_measurable w hm b) (weight_bound w b hb) (Ω f)).trans_eq
      (Ω.norm_map f)) (inv_nonneg.mpr hb.le)

theorem operator_opNorm : ‖operator Ω w hm b hb‖ ≤ b⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hb.le) (operator_norm Ω w hm b hb)

include hm hb in
theorem density_integrable (f : H) :
    Integrable (fun x => value b (w x)*‖(Ω f) x‖^2) μ := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) (Ω f) (Ω (operator Ω w hm b hb f))).re
  apply hi.congr
  filter_upwards [operator_coordinates Ω w hm b hb f] with x hx
  rw [hx]
  change (inner ℂ ((Ω f) x) ((value b (w x):ℂ) • (Ω f) x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((value b (w x):ℂ)*(‖(Ω f) x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

theorem operator_symmetric (f g : H) :
    inner ℂ (operator Ω w hm b hb f) g = inner ℂ f (operator Ω w hm b hb g) := by
  let M := multiplyL (μ := μ) (weight w b) (weight_measurable w hm b) (weight_bound w b hb)
  have hs := multiplyL_symmetric (μ := μ) (weight w b) (weight_measurable w hm b)
    (weight_bound w b hb) (fun x => Complex.conj_ofReal _) (Ω f) (Ω g)
  have he (v : H) : operator Ω w hm b hb v = (b⁻¹:ℝ) • Ω.symm (M (Ω v)) := rfl
  rw [he,he,inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  congr 1
  calc
    _ = inner ℂ (M (Ω f)) (Ω g) := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (Ω.inner_map_map (Ω.symm (M (Ω f))) g).symm
    _ = inner ℂ (Ω f) (M (Ω g)) := hs
    _ = _ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        Ω.inner_map_map f (Ω.symm (M (Ω g)))

theorem expectation_integral (f : H) :
    (inner ℂ f (operator Ω w hm b hb f)).re = ∫ x, value b (w x)*‖(Ω f) x‖^2 ∂μ := by
  rw [← Ω.inner_map_map f (operator Ω w hm b hb f)]
  simpa only [Complex.ofReal_re] using multiplier_real_pairing μ
    (fun x => (value b (w x):ℂ)) (Ω f) (Ω (operator Ω w hm b hb f))
    (operator_coordinates Ω w hm b hb f)

omit b hb in
theorem expectation_tendsto (f : H)
    (hf : Integrable (fun x => |w x| *‖(Ω f) x‖^2) μ)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ f (operator Ω w hm (b n) (hb n) f)).re) atTop
      (𝓝 (∫ x, w x*‖(Ω f) x‖^2 ∂μ)) := by
  simp only [expectation_integral]
  apply tendsto_integral_of_dominated_convergence (fun x => |w x| *‖(Ω f) x‖^2)
  · intro n
    have hm' : Measurable (fun x => value (b n) (w x)) := by
      unfold value
      exact hm.div (measurable_const.add (measurable_const.mul (continuous_abs.measurable.comp hm)))
    exact hm'.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (Ω f)).norm.pow 2)
  · exact hf
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_norm]
      exact mul_le_mul_of_nonneg_right (value_abs_le (b n) (w x) (hb n).le) (sq_nonneg _))
  · exact Filter.Eventually.of_forall (fun x => (value_tendsto b hz (w x)).mul_const _)
end General

open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment (spectralCoordinates symbol_measurable momentumHalf momentumHalf_domain)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)

def momentumCutoff (ε : ℝ) (hε : 0 < ε) (h b : ℝ) (hb : 0 < b) : Hilbert →L[ℂ] Hilbert :=
  operator (spectralCoordinates ε hε) (symbol h) (symbol_measurable h) b hb

def absoluteCutoff (ε : ℝ) (hε : 0 < ε) (h b : ℝ) (hb : 0 < b) : Hilbert →L[ℂ] Hilbert :=
  operator (spectralCoordinates ε hε) (fun k => |symbol h k|) (continuous_abs.measurable.comp (symbol_measurable h)) b hb

theorem momentum_expectation_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (momentumHalf ε hε h).domain)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ f (momentumCutoff ε hε h (b n) (hb n) f)).re) atTop
      (𝓝 (∫ k, symbol h k*‖(spectralCoordinates ε hε f) k‖^2)) :=
  expectation_tendsto _ _ _ f ((momentumHalf_domain ε hε h f).mp hf) b hb hz

theorem absolute_expectation_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (momentumHalf ε hε h).domain)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ f (absoluteCutoff ε hε h (b n) (hb n) f)).re) atTop
      (𝓝 (‖momentumHalf ε hε h ⟨f,hf⟩‖^2)) := by
  have hi : Integrable (fun k => abs (abs (symbol h k)) *‖(spectralCoordinates ε hε f) k‖^2) := by
    simpa only [abs_abs] using (momentumHalf_domain ε hε h f).mp hf
  have ht := expectation_tendsto (spectralCoordinates ε hε) (fun k => |symbol h k|)
    (continuous_abs.measurable.comp (symbol_measurable h)) f hi b hb hz
  simpa only [UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment.momentumHalf,
    UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment.halfAbsolute_norm_square] using ht

theorem signed_density_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (momentumHalf ε hε h).domain) :
    Integrable (fun k => symbol h k*‖(spectralCoordinates ε hε f) k‖^2) := by
  apply Integrable.mono' ((momentumHalf_domain ε hε h f).mp hf)
    ((symbol_measurable h).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (spectralCoordinates ε hε f)).norm.pow 2))
  exact Filter.Eventually.of_forall (fun k => by
    simp only [Pi.mul_apply,Pi.pow_apply,Real.norm_eq_abs,abs_mul,abs_pow,abs_norm,le_refl])

theorem graph_expectation_integral (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f g : Hilbert) (hg : (f,g) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph) :
    (inner ℂ f g).re = ∫ k, symbol h k*‖(spectralCoordinates ε hε f) k‖^2 := by
  rw [← (spectralCoordinates ε hε).inner_map_map f g]
  simpa only [Complex.ofReal_re] using multiplier_real_pairing volume
    (fun k => (symbol h k:ℂ)) (spectralCoordinates ε hε f) (spectralCoordinates ε hε g)
    ((KFCausalClockFloorPureClockMomentum.graph_fourier ε hε h hh f g).mp hg)

theorem graph_expectation_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f g : Hilbert) (hg : (f,g) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ f (momentumCutoff ε hε h (b n) (hb n) f)).re) atTop
      (𝓝 (inner ℂ f g).re) := by
  rw [graph_expectation_integral ε hε h hh f g hg]
  exact momentum_expectation_tendsto ε hε h f
    (KFCausalPureMomentumFirstMoment.momentum_graph_domain ε hε h hh f g hg) b hb hz

#print axioms signed_density_integrable
#print axioms graph_expectation_integral
#print axioms graph_expectation_tendsto

#print axioms denominator_positive
#print axioms value_abs_le
#print axioms scaled_value_bound
#print axioms value_tendsto
#print axioms weight_measurable
#print axioms weight_bound
#print axioms operator_coordinates
#print axioms operator_norm
#print axioms operator_opNorm
#print axioms density_integrable
#print axioms operator_symmetric
#print axioms expectation_integral
#print axioms expectation_tendsto
#print axioms momentum_expectation_tendsto
#print axioms absolute_expectation_tendsto
end
end UnifiedTheory.Audit.KFCausalPureMomentumCutoff
