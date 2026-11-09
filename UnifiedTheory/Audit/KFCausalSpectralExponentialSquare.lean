/- The half-exponential has the full square-root graph, including the
reverse domain inclusion, and its squared norm gives the quadratic energy. -/
import UnifiedTheory.Audit.KFCausalSpectralExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSpectralExponentialSquare
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalSpectralExponential
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}

theorem exponential_domain_halving (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : H)
    (hf : f ∈ (exponential Ω ν hν (2*a)).domain) :
    f ∈ (exponential Ω ν hν a).domain := by
  rw [exponential_domain_iff] at hf ⊢
  have hn : Integrable (fun x => ‖(Ω f) x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (Ω f)).aestronglyMeasurable).mp (Lp.memLp (Ω f))
  have ha : AEStronglyMeasurable (fun x => Real.exp (2*a*ν x)*‖(Ω f) x‖^2) μ :=
    (weight_measurable ν hν (2*a)).aestronglyMeasurable.mul
      ((Lp.memLp (Ω f)).aestronglyMeasurable.norm.pow 2)
  apply (hn.add hf).mono' ha
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  have hb : Real.exp (2*a*ν x) ≤ 1+Real.exp (2*(2*a)*ν x) := by
    rw [← weight_square ν (2*a) x]
    change weight ν (2*a) x ≤ 1+(weight ν (2*a) x)^2
    nlinarith [sq_nonneg (weight ν (2*a) x-1/2)]
  calc
    _ ≤ (1+Real.exp (2*(2*a)*ν x))*‖(Ω f) x‖^2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = _ := by simp only [Pi.add_apply]; ring

theorem exponential_square_graph (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f h : H) :
    (f,h) ∈ (exponential Ω ν hν (2*a)).graph ↔
      ∃ g : H, (f,g) ∈ (exponential Ω ν hν a).graph ∧ (g,h) ∈ (exponential Ω ν hν a).graph := by
  constructor
  · intro hfh
    have hf := exponential_domain_halving Ω ν hν a f (LinearPMap.mem_domain_of_mem_graph hfh)
    let g := exponential Ω ν hν a ⟨f,hf⟩
    have hfg : (f,g) ∈ (exponential Ω ν hν a).graph := (exponential Ω ν hν a).mem_graph ⟨f,hf⟩
    refine ⟨g,hfg,?_⟩
    rw [exponential_graph_iff] at hfh hfg ⊢
    filter_upwards [hfh,hfg] with x hx hy
    rw [hx,hy,← mul_assoc,← Complex.ofReal_mul]
    change (Real.exp (2*a*ν x):ℂ)*(Ω f) x = ((weight ν a x * weight ν a x:ℝ):ℂ)*(Ω f) x
    rw [← pow_two,weight_square]
  · rintro ⟨g,hfg,hgh⟩
    have he : a+a=2*a := by ring
    simpa only [he] using exponential_comp_graph Ω ν hν a a f g h hfg hgh

theorem exponential_inner (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : (exponential Ω ν hν a).domain) :
    (inner ℂ (exponential Ω ν hν a f) (f:H)).re =
      ∫ x, Real.exp (a*ν x)*‖(Ω f) x‖^2 ∂μ := by
  rw [← Ω.inner_map_map (exponential Ω ν hν a f) (f:H)]
  change (inner ℂ (Ω (positivePullback Ω (weight ν a) _ _ f)) (Ω f)).re = _
  rw [pullback_coordinates]
  exact multiplier_inner (weight ν a) _ _ (spectralState Ω (weight ν a) _ _ f)

def halfState (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : (exponential Ω ν hν (2*a)).domain) :
    (exponential Ω ν hν a).domain := ⟨f,exponential_domain_halving Ω ν hν a f f.property⟩

theorem exponential_square_energy (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : (exponential Ω ν hν (2*a)).domain) :
    (inner ℂ (exponential Ω ν hν (2*a) f) (f:H)).re =
      ‖exponential Ω ν hν a (halfState Ω ν hν a f)‖^2 := by
  rw [exponential_inner,exponential_energy]
  rfl

#print axioms exponential_domain_halving
#print axioms exponential_square_graph
#print axioms exponential_inner
#print axioms exponential_square_energy

end
end UnifiedTheory.Audit.KFCausalSpectralExponentialSquare
