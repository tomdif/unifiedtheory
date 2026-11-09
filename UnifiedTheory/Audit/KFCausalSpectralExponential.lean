/- Unbounded positive exponentials in a given unitary spectral representation.
The graph, inverse, and composition statements keep their exact domains. -/
import UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSpectralExponential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}

def weight (ν : X → ℝ) (a : ℝ) (x : X) : ℝ := Real.exp (a*ν x)

theorem weight_measurable (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) :
    Measurable (weight ν a) := (measurable_const.mul hν).exp

omit [MeasurableSpace X] in
theorem weight_positive (ν : X → ℝ) (a : ℝ) (x : X) :
    0 < weight ν a x := Real.exp_pos _

omit [MeasurableSpace X] in
theorem weight_square (ν : X → ℝ) (a : ℝ) (x : X) :
    (weight ν a x)^2 = Real.exp (2*a*ν x) := by
  rw [pow_two,weight,← Real.exp_add]
  congr 1
  ring

omit [MeasurableSpace X] in
theorem weight_add (ν : X → ℝ) (a b : ℝ) (x : X) :
    weight ν (a+b) x = weight ν a x * weight ν b x := by
  simp only [weight,add_mul,Real.exp_add]

omit [MeasurableSpace X] in
theorem weight_inverse (ν : X → ℝ) (a : ℝ) (x : X) :
    weight ν (-a) x * weight ν a x = 1 := by
  rw [← weight_add]
  simp only [neg_add_cancel,weight,zero_mul,Real.exp_zero]

def exponential (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) :
    H →ₗ.[ℂ] H :=
  positivePullback Ω (weight ν a) (weight_measurable ν hν a) (fun x => (weight_positive ν a x).le)

theorem exponential_selfAdjoint [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) : IsSelfAdjoint (exponential Ω ν hν a) :=
  pullback_selfAdjoint _ _ _ _

theorem exponential_graph_iff (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f g : H) :
    (f,g) ∈ (exponential Ω ν hν a).graph ↔ Ω g =ᵐ[μ] fun x => (Real.exp (a*ν x):ℂ)*(Ω f) x :=
  pullback_graph_iff _ _ _ _ _ _

theorem exponential_domain_iff (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : H) :
    f ∈ (exponential Ω ν hν a).domain ↔ Integrable (fun x => Real.exp (2*a*ν x)*‖(Ω f) x‖^2) μ := by
  rw [exponential,pullback_domain_integrable_iff]
  simp only [weight_square]

theorem exponential_energy (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : (exponential Ω ν hν a).domain) :
    ‖exponential Ω ν hν a f‖^2 = ∫ x, Real.exp (2*a*ν x)*‖(Ω f) x‖^2 ∂μ := by
  exact (pullback_norm_square Ω (weight ν a) _ _ f).trans
    (integral_congr_ae (Filter.Eventually.of_forall (fun x => by dsimp only; rw [weight_square])))

theorem exponential_positive (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f : (exponential Ω ν hν a).domain) :
    0 ≤ (inner ℂ (exponential Ω ν hν a f) (f:H)).re :=
  pullback_positive _ _ _ _ f

theorem exponential_dense [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) :
    Dense ((exponential Ω ν hν a).domain : Set H) := (exponential_selfAdjoint Ω ν hν a).dense_domain

theorem exponential_closed [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) :
    (exponential Ω ν hν a).IsClosed := (exponential_selfAdjoint Ω ν hν a).isClosed

theorem exponential_zero_graph (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (f g : H) :
    (f,g) ∈ (exponential Ω ν hν 0).graph ↔ g=f := by
  rw [exponential_graph_iff]
  simp only [zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul]
  constructor
  · intro h
    exact Ω.injective (Lp.ext h)
  · rintro rfl
    exact Filter.EventuallyEq.rfl

theorem exponential_inverse_graph (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a : ℝ) (f g : H) :
    (f,g) ∈ (exponential Ω ν hν a).graph ↔ (g,f) ∈ (exponential Ω ν hν (-a)).graph := by
  have hinv : ∀ b : ℝ, ∀ u v : H,
      (u,v) ∈ (exponential Ω ν hν b).graph → (v,u) ∈ (exponential Ω ν hν (-b)).graph := by
    intro b u v h
    rw [exponential_graph_iff] at h ⊢
    filter_upwards [h] with x hx
    rw [hx,← mul_assoc,← Complex.ofReal_mul]
    change (Ω u) x = ((weight ν (-b) x * weight ν b x:ℝ):ℂ)*(Ω u) x
    rw [weight_inverse,Complex.ofReal_one,one_mul]
  constructor
  · exact hinv a f g
  · intro h
    simpa only [neg_neg] using hinv (-a) g f h

theorem exponential_comp_graph (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (ν : X → ℝ) (hν : Measurable ν) (a b : ℝ) (f g h : H)
    (hfg : (f,g) ∈ (exponential Ω ν hν a).graph)
    (hgh : (g,h) ∈ (exponential Ω ν hν b).graph) :
    (f,h) ∈ (exponential Ω ν hν (a+b)).graph := by
  rw [exponential_graph_iff] at hfg hgh ⊢
  filter_upwards [hfg,hgh] with x hx hy
  rw [hy,hx,← mul_assoc,← Complex.ofReal_mul]
  change ((weight ν b x * weight ν a x:ℝ):ℂ)*(Ω f) x = (weight ν (a+b) x:ℂ)*(Ω f) x
  rw [weight_add,mul_comm (weight ν b x) (weight ν a x)]

#print axioms weight_square
#print axioms weight_inverse
#print axioms exponential_selfAdjoint
#print axioms exponential_graph_iff
#print axioms exponential_domain_iff
#print axioms exponential_energy
#print axioms exponential_positive
#print axioms exponential_dense
#print axioms exponential_closed
#print axioms exponential_zero_graph
#print axioms exponential_inverse_graph
#print axioms exponential_comp_graph

end
end UnifiedTheory.Audit.KFCausalSpectralExponential
