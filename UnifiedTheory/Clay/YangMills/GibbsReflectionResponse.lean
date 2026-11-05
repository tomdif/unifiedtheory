/- Reflection-equivariant elimination of compact Gibbs variables.
The exact mixed-product input remains explicit. These identities do not
prove a positive reflected norm or any continuum estimate. -/
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsReflectionResponse
noncomputable section
open MeasureTheory GibbsMarginalTower GibbsCrossCovariance

section Transport
variable {B X : Type*} [MeasurableSpace X] (μX : Measure X)
  (σB : B → B) (σX : X ≃ᵐ X) (hσ : MeasurePreserving σX μX μX)
  (A : B × X → ℝ) (hA : ∀ b x, A (σB b, σX x) = A (b, x))

include hσ hA

theorem fiberMass_reflection (b : B) : fiberMass μX A (σB b) = fiberMass μX A b := by
  unfold fiberMass
  rw [← hσ.integral_comp' (fun x => Real.exp (-A (σB b, x)))]
  simp only [hA]

theorem response_reflection (F : B × X → ℝ) (b : B) :
    response μX A F (σB b) =
      response μX A (fun p => F (σB p.1, σX p.2)) b := by
  unfold response
  rw [fiberMass_reflection μX σB σX hσ A hA b]
  rw [← hσ.integral_comp' (fun x => Real.exp (-A (σB b, x)) * F (σB b, x))]
  simp only [hA]

theorem removed_reflection (F : B × X → ℝ) (p : B × X) :
    removed μX A F (σB p.1, σX p.2) =
      removed μX A (fun q => F (σB q.1, σX q.2)) p := by
  unfold removed
  rw [response_reflection μX σB σX hσ A hA F p.1]
end Transport

variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]
  (σB : B → B) (σX : X ≃ᵐ X) (hσ : MeasurePreserving σX μX μX)
  (A : B × X → ℝ) (hcA : Continuous A)
  (hA : ∀ b x, A (σB b, σX x) = A (b, x))

include hσ hcA hA

theorem reflected_product_preserved (F G : B × X → ℝ) (hG : Continuous G)
    (hFσ : Continuous (fun p : B × X => F (σB p.1, σX p.2)))
    (hprod : ∀ b, response μX A (fun p => F (σB p.1, σX p.2) * G p) b =
      response μX A (fun p => F (σB p.1, σX p.2)) b * response μX A G b) :
    (∫ p, F (σB p.1, σX p.2) * G p ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ b, response μX A F (σB b) * response μX A G b ∂marginal μB μX A := by
  rw [product_preserved μB μX A _ G hcA hFσ hG hprod]
  simp only [response_reflection μX σB σX hσ A hA]

theorem reflected_covariance_preserved (F G : B × X → ℝ) (hG : Continuous G)
    (hFσ : Continuous (fun p : B × X => F (σB p.1, σX p.2)))
    (hprod : ∀ b, response μX A (fun p => F (σB p.1, σX p.2) * G p) b =
      response μX A (fun p => F (σB p.1, σX p.2)) b * response μX A G b) :
    covariance (CompactGibbsContinuity.law (μB.prod μX) A)
      (fun p => F (σB p.1, σX p.2)) G =
      covariance (marginal μB μX A)
        (fun b => response μX A F (σB b)) (response μX A G) := by
  rw [covariance_preserved μB μX A _ G hcA hFσ hG hprod]
  simp only [response_reflection μX σB σX hσ A hA]

/-- This is a reflected zero-pairing statement. Interpreting it as nullity
in a particular OS Hilbert space also requires the appropriate support. -/
theorem removed_reflected_zero (F G : B × X → ℝ) (hG : Continuous G)
    (hFσ : Continuous (fun p : B × X => F (σB p.1, σX p.2)))
    (hprod : ∀ b, response μX A (fun p => F (σB p.1, σX p.2) * G p) b =
      response μX A (fun p => F (σB p.1, σX p.2)) b * response μX A G b) :
    (∫ p, removed μX A F (σB p.1, σX p.2) * removed μX A G p
      ∂CompactGibbsContinuity.law (μB.prod μX) A) = 0 := by
  simp only [removed_reflection μX σB σX hσ A hA]
  exact GibbsCrossCovariance.removed_product_zero μB μX A _ G hcA hFσ hG hprod

end
end UnifiedTheory.Clay.YangMills.GibbsReflectionResponse
