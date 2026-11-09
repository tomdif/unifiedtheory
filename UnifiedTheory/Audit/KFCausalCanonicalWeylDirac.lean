/- The scaled commutator of the actual bounded canonical phase tests
has the classical symplectic coefficient, uniformly on unit vectors.
This does not extend the estimate to the unbounded ordered Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCanonicalWeylDirac
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

def coefficient (h a b : ℝ) : ℂ :=
  (-Complex.I)*(h:ℂ)⁻¹*(scalar (h*a)-scalar (h*b))

theorem scalar_derivative (a : ℝ) :
    HasDerivAt (fun h : ℝ => scalar (h*a)) (Complex.I*(a:ℂ)) 0 := by
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const a).ofReal_comp.const_mul Complex.I).cexp
  simpa only [scalar,id_eq,zero_mul,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,one_mul] using hd

theorem coefficient_tendsto (a b : ℝ) :
    Tendsto (fun h => coefficient h a b) (𝓝[≠] (0:ℝ)) (𝓝 ((a-b:ℝ):ℂ)) := by
  have hd := (scalar_derivative a).sub (scalar_derivative b)
  have ht := hd.tendsto_slope.const_mul (-Complex.I)
  convert ht using 1
  · funext h
    simp only [coefficient,slope_def_module,Pi.sub_apply,sub_zero,scalar,zero_mul,Complex.ofReal_zero,
      mul_zero,Complex.exp_zero,sub_self,Complex.real_smul,
      Complex.ofReal_inv]
    ring
  · push_cast
    ring_nf
    simp [Complex.I_sq,sub_eq_add_neg]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]

def residual (h : ℝ) (z w : Frequency (X := X)) (f : Hilbert μ) : Hilbert μ :=
  ((-Complex.I)*(h:ℂ)⁻¹) •
    (operator μ h z (operator μ h w f)-operator μ h w (operator μ h z f))-
    ((w.1 z.2-z.1 w.2:ℝ):ℂ) • operator μ h (z+w) f

theorem residual_norm (h : ℝ) (z w : Frequency (X := X)) (f : Hilbert μ) :
    ‖residual μ h z w f‖ =
      ‖coefficient h (w.1 z.2) (z.1 w.2)-((w.1 z.2-z.1 w.2:ℝ):ℂ)‖*‖f‖ := by
  unfold residual
  rw [operator_product,operator_product,add_comm w z,← sub_smul,smul_smul,← sub_smul,
    norm_smul,(operator μ h (z+w)).norm_map]
  rfl

theorem residual_uniform_limit (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hz : Tendsto h atTop (𝓝 0)) (z w : Frequency (X := X)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : Hilbert μ, ‖f‖ = 1 → ‖residual μ (h n) z w f‖ < δ := by
  have hn : Tendsto h atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => hh n)⟩
  have ht := ((coefficient_tendsto (w.1 z.2) (z.1 w.2)).comp hn).sub_const
    (((w.1 z.2-z.1 w.2:ℝ):ℂ)) |>.norm
  simp only [sub_self,norm_zero] at ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N,?_⟩
  intro n hNn f hf
  rw [residual_norm,hf,mul_one]
  exact hN n hNn

#print axioms scalar_derivative
#print axioms coefficient_tendsto
#print axioms residual_norm
#print axioms residual_uniform_limit

end
end UnifiedTheory.Audit.KFCausalCanonicalWeylDirac
