/- The absolute first-moment domain for actual pure-clock momentum.
It is the maximal L2 domain of multiplication by sqrt(abs(symbol)) in
the already proved unitary clock-Fourier coordinates. The exact weighted
integral and expectation bound are derived, not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
import UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

section General
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}
  (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)

def halfAbsolute : H →ₗ.[ℂ] H :=
  positivePullback Ω (fun x => Real.sqrt |w x|)
    (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp hm))
    (fun _ => Real.sqrt_nonneg _)

theorem halfAbsolute_domain (f : H) :
    f ∈ (halfAbsolute Ω w hm).domain ↔
      Integrable (fun x => |w x| *‖(Ω f) x‖^2) μ := by
  rw [halfAbsolute,pullback_domain_integrable_iff]
  simp only [Real.sq_sqrt (abs_nonneg _)]

theorem halfAbsolute_norm_square (f : H) (hf : f ∈ (halfAbsolute Ω w hm).domain) :
    ‖halfAbsolute Ω w hm ⟨f,hf⟩‖^2 = ∫ x, |w x| *‖(Ω f) x‖^2 ∂μ := by
  simpa only [Real.sq_sqrt (abs_nonneg _)] using
    pullback_norm_square Ω (fun x => Real.sqrt |w x|)
      (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp hm))
      (fun _ => Real.sqrt_nonneg _) ⟨f,hf⟩

theorem real_inner_norm (r : ℝ) (z : ℂ) :
    ‖inner ℂ z ((r:ℂ)*z)‖ = |r| *‖z‖^2 := by
  change ‖inner ℂ z ((r:ℂ) • z)‖ = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,RCLike.norm_coe_norm]

theorem graph_halfAbsolute_domain (f b : H)
    (hg : Ω b =ᵐ[μ] fun x => (w x:ℂ)*(Ω f) x) :
    f ∈ (halfAbsolute Ω w hm).domain := by
  apply (halfAbsolute_domain Ω w hm f).mpr
  apply (L2.integrable_inner (𝕜 := ℂ) (Ω f) (Ω b)).norm.congr
  filter_upwards [hg] with x hx
  rw [hx,real_inner_norm]

theorem graph_expectation_bound (f b : H)
    (hg : Ω b =ᵐ[μ] fun x => (w x:ℂ)*(Ω f) x)
    (hf : f ∈ (halfAbsolute Ω w hm).domain) :
    |(inner ℂ f b).re| ≤ ‖halfAbsolute Ω w hm ⟨f,hf⟩‖^2 := by
  calc
    _ ≤ ‖inner ℂ f b‖ := Complex.abs_re_le_norm _
    _ = ‖inner ℂ (Ω f) (Ω b)‖ := congrArg norm (Ω.inner_map_map f b).symm
    _ = ‖∫ x, inner ℂ ((Ω f) x) ((Ω b) x) ∂μ‖ := by rw [L2.inner_def]
    _ ≤ ∫ x, ‖inner ℂ ((Ω f) x) ((Ω b) x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, |w x| *‖(Ω f) x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx,real_inner_norm]
    _ = _ := (halfAbsolute_norm_square Ω w hm f hf).symm

theorem halfAbsolute_closed [CompleteSpace H] : (halfAbsolute Ω w hm).IsClosed :=
  pullback_closed Ω _ _ _
end General

open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert fourierCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum graph_fourier)

def spectralCoordinates (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (coordinates ε hε).symm.trans fourierCoordinates

theorem symbol_measurable (h : ℝ) : Measurable (symbol h) := by
  unfold symbol
  fun_prop

def momentumHalf (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  halfAbsolute (spectralCoordinates ε hε) (symbol h) (symbol_measurable h)

theorem momentumHalf_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert) :
    f ∈ (momentumHalf ε hε h).domain ↔
      Integrable (fun k : Space => |symbol h k| *‖(spectralCoordinates ε hε f) k‖^2) :=
  halfAbsolute_domain _ _ _ f

theorem momentumHalf_closed (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    (momentumHalf ε hε h).IsClosed := halfAbsolute_closed _ _ _

theorem momentum_graph_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f b : Hilbert) (hg : (f,b) ∈ (pureMomentum ε hε h).graph) :
    f ∈ (momentumHalf ε hε h).domain :=
  graph_halfAbsolute_domain _ _ _ f b ((graph_fourier ε hε h hh f b).mp hg)

theorem momentum_expectation_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f b : Hilbert) (hg : (f,b) ∈ (pureMomentum ε hε h).graph)
    (hf : f ∈ (momentumHalf ε hε h).domain) :
    |(inner ℂ f b).re| ≤ ‖momentumHalf ε hε h ⟨f,hf⟩‖^2 :=
  graph_expectation_bound _ _ _ f b ((graph_fourier ε hε h hh f b).mp hg) hf

#print axioms halfAbsolute_domain
#print axioms halfAbsolute_norm_square
#print axioms real_inner_norm
#print axioms graph_halfAbsolute_domain
#print axioms graph_expectation_bound
#print axioms halfAbsolute_closed
#print axioms symbol_measurable
#print axioms momentumHalf_domain
#print axioms momentumHalf_closed
#print axioms momentum_graph_domain
#print axioms momentum_expectation_bound
end
end UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
