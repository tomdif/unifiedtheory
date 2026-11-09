/- A quantitative criterion for removing bounded absolute-momentum
cutoffs. Uniform expectation bounds are equivalent to the actual first
moment domain. The finite-energy obstruction therefore forbids those
bounds on all energy states, even before evolution. -/
import UnifiedTheory.Audit.KFCausalPureMomentumCutoff
import UnifiedTheory.Audit.KFCausalPureMomentumFirstMomentObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalPureMomentumCutoff
open UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)

theorem integrable_of_uniform_nonnegative_integrals {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (G : ℕ → X → ℝ) (f : X → ℝ)
    (hG : ∀ n, Integrable (G n) μ) (hGn : ∀ n x, 0 ≤ G n x)
    (hf : AEStronglyMeasurable f μ) (hfn : ∀ x, 0 ≤ f x)
    (ht : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (f x)))
    (M : ℝ) (hM : ∀ n, ∫ x, G n x ∂μ ≤ M) : Integrable f μ := by
  have he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x, liminf (fun n => ENNReal.ofReal (G n x)) atTop ∂μ := by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      ((ENNReal.continuous_ofReal.tendsto _).comp (ht x)).liminf_eq.symm)
  have hb (n : ℕ) : (∫⁻ x, ENNReal.ofReal (G n x) ∂μ) ≤ ENNReal.ofReal M := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hG n) (Filter.Eventually.of_forall (hGn n))]
    exact ENNReal.ofReal_le_ofReal (hM n)
  refine ⟨hf,(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfn)).mpr ?_⟩
  calc
    _ = _ := he
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hG n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal M := liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently
    _ < ⊤ := ENNReal.ofReal_lt_top

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "Ω" => spectralCoordinates ε hε
local notation "Q" => momentumHalf ε hε h

theorem absolute_cutoff_nonnegative (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    0 ≤ (inner ℂ f (absoluteCutoff ε hε h b hb f)).re := by
  rw [absoluteCutoff,expectation_integral]
  exact integral_nonneg (fun x => mul_nonneg
    (div_nonneg (abs_nonneg _) (denominator_positive b _ hb.le).le) (sq_nonneg _))

theorem absolute_cutoff_le_moment (b : ℝ) (hb : 0 < b) (f : Hilbert)
    (hf : f ∈ (Q).domain) :
    (inner ℂ f (absoluteCutoff ε hε h b hb f)).re ≤ ‖Q ⟨f,hf⟩‖^2 := by
  rw [absoluteCutoff,expectation_integral]
  change _ ≤ ‖halfAbsolute Ω (symbol h) (symbol_measurable h) ⟨f,hf⟩‖^2
  rw [halfAbsolute_norm_square]
  apply integral_mono (density_integrable Ω (fun k => |symbol h k|)
    (continuous_abs.measurable.comp (symbol_measurable h)) b hb f)
    ((momentumHalf_domain ε hε h f).mp hf)
  intro x
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (le_abs_self _).trans (by simpa only [abs_abs] using value_abs_le b |symbol h x| hb.le)

theorem domain_iff_uniform_absolute_cutoffs (f : Hilbert)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    f ∈ (Q).domain ↔ ∃ M : ℝ, ∀ n,
      (inner ℂ f (absoluteCutoff ε hε h (b n) (hb n) f)).re ≤ M := by
  constructor
  · intro hf
    exact ⟨‖Q ⟨f,hf⟩‖^2,fun n => absolute_cutoff_le_moment ε hε h (b n) (hb n) f hf⟩
  · rintro ⟨M,hM⟩
    apply (momentumHalf_domain ε hε h f).mpr
    apply integrable_of_uniform_nonnegative_integrals
      (fun n k => value (b n) |symbol h k| *‖(Ω f) k‖^2) _
      (fun n => density_integrable Ω (fun k => |symbol h k|)
        (continuous_abs.measurable.comp (symbol_measurable h)) (b n) (hb n) f)
      (fun n k => mul_nonneg (div_nonneg (abs_nonneg _)
        (denominator_positive (b n) _ (hb n).le).le) (sq_nonneg _))
      ((continuous_abs.measurable.comp (symbol_measurable h)).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (Ω f)).norm.pow 2))
      (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun k => (value_tendsto b hz |symbol h k|).mul_const _) M
    intro n
    exact (congrArg (fun x : ℝ => x ≤ M)
      (expectation_integral Ω (fun k => |symbol h k|)
        (continuous_abs.measurable.comp (symbol_measurable h)) (b n) (hb n) f)).mp (hM n)

theorem unbounded_absolute_cutoffs_of_outside_domain (f : Hilbert) (hf : f ∉ (Q).domain)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) (M : ℝ) :
    ∃ n, M < (inner ℂ f (absoluteCutoff ε hε h (b n) (hb n) f)).re := by
  by_contra hn
  push_neg at hn
  exact hf ((domain_iff_uniform_absolute_cutoffs ε hε h f b hb hz).mpr ⟨M,hn⟩)

#print axioms integrable_of_uniform_nonnegative_integrals
#print axioms absolute_cutoff_nonnegative
#print axioms absolute_cutoff_le_moment
#print axioms domain_iff_uniform_absolute_cutoffs
#print axioms unbounded_absolute_cutoffs_of_outside_domain
end
end UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain
