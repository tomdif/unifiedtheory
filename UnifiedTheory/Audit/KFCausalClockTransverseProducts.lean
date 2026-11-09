/- Actual L1 and L2 product states in the clock and transverse variables.
The volume-preserving split gives their configuration and Euclidean forms. -/
import UnifiedTheory.Audit.KFCausalEuclideanClockSplit
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockTransverseProducts
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit

def pairFunction (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (z : ℝ × TailSpace) : ℂ := g z.1*ψ z.2
def productFunction (g : ℝ → ℂ) (ψ : TailSpace → ℂ) : Space → ℂ := pairFunction g ψ ∘ euclideanSplit
def configurationProduct (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (x : Configuration) : ℂ :=
  g x.1*ψ (transverseCoordinates x.2)

theorem product_apply (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (x : Space) :
    productFunction g ψ x = g (x 0)*ψ (tail x) := rfl

theorem product_flatten (g : ℝ → ℂ) (ψ : TailSpace → ℂ) :
    configurationProduct g ψ ∘ split = productFunction g ψ := rfl

theorem pair_integrable (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hg : Integrable g) (hψ : Integrable ψ) :
    Integrable (pairFunction g ψ) := hg.mul_prod hψ

theorem pair_memLp (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    MemLp (pairFunction g ψ) 2 := by
  have hm : AEStronglyMeasurable (pairFunction g ψ) volume :=
    hg.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hψ2 := (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ
  simpa only [pairFunction,norm_mul,mul_pow] using hg2.mul_prod hψ2

theorem product_integrable (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hg : Integrable g) (hψ : Integrable ψ) :
    Integrable (productFunction g ψ) :=
  euclideanSplit_preserves_volume.integrable_comp_of_integrable (pair_integrable g ψ hg hψ)

theorem product_memLp (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    MemLp (productFunction g ψ) 2 :=
  (pair_memLp g ψ hg hψ).comp_measurePreserving euclideanSplit_preserves_volume

theorem configuration_integrable (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : Integrable g) (hψ : Integrable ψ) : Integrable (configurationProduct g ψ) :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod transverse_preserves_volume).integrable_comp_of_integrable
    (pair_integrable g ψ hg hψ)

theorem configuration_memLp (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) : MemLp (configurationProduct g ψ) 2 :=
  (pair_memLp g ψ hg hψ).comp_measurePreserving
    ((MeasurePreserving.id (volume : Measure ℝ)).prod transverse_preserves_volume)

theorem product_square_integral (g : ℝ → ℂ) (ψ : TailSpace → ℂ) :
    (∫ x, ‖productFunction g ψ x‖^2) = (∫ q, ‖g q‖^2)*(∫ y, ‖ψ y‖^2) := by
  have he := euclideanSplit_preserves_volume.integral_comp'
    (fun z : ℝ × TailSpace => ‖g z.1‖^2*‖ψ z.2‖^2)
  have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure TailSpace))
    (fun q => ‖g q‖^2) (fun y => ‖ψ y‖^2)
  simpa only [productFunction,pairFunction,Function.comp_apply,norm_mul,mul_pow] using he.trans hp

#print axioms product_apply
#print axioms product_flatten
#print axioms pair_integrable
#print axioms pair_memLp
#print axioms product_integrable
#print axioms product_memLp
#print axioms configuration_integrable
#print axioms configuration_memLp
#print axioms product_square_integral

end
end UnifiedTheory.Audit.KFCausalClockTransverseProducts
