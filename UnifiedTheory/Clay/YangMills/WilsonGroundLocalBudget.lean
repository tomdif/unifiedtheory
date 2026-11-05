/- Local physical sources constrain every global ground-law factorization
constant. Only links in the source support can contribute heat-bath energy. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundLocalBudget
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHaarLinkResponse WilsonGroundVarianceBudget

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- A coordinate outside the source support has exactly zero conditional energy. -/
theorem heatBathEnergy_zero (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hsupport : ∀ u v : Slice n, (∀ j ∈ T, u j = v j) → f u = f v)
    (e : SpatialVertex n × Fin 3) (he : e ∉ T) :
    heatBathEnergy n β hβ {e} f = 0 := by
  have hf (r : Outside n {e}) (a b : Inside n {e}) :
      f (WilsonBlockMarginal.assemble {e} (r, a)) =
        f (WilsonBlockMarginal.assemble {e} (r, b)) := by
    apply hsupport
    intro j hj
    have hje : j ∉ ({e} : Finset _) := by
      simp only [Finset.mem_singleton]
      intro h
      exact he (h ▸ hj)
    rw [WilsonBlockMarginal.assemble_outside {e} _ j hje,
      WilsonBlockMarginal.assemble_outside {e} _ j hje]
  have hd (r : Outside n {e}) (a b : Inside n {e}) :
      f (WilsonBlockMarginal.assemble {e} (r, a)) -
        f (WilsonBlockMarginal.assemble {e} (r, b)) = 0 := sub_eq_zero.mpr (hf r a b)
  simp only [heatBathEnergy, hd, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero]

theorem supported_total_le (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hsupport : ∀ u v : Slice n, (∀ j ∈ T, u j = v j) → f u = f v) :
    totalConditionalVariance n β hβ f ≤ (T.card : ℝ) * variance n β hβ f := by
  have he : (∑ e ∈ T, heatBathEnergy n β hβ {e} f) =
      totalConditionalVariance n β hβ f :=
    Finset.sum_subset (Finset.subset_univ T)
      (fun e _ he => heatBathEnergy_zero n β hβ T f hsupport e he)
  rw [← he]
  calc
    _ ≤ ∑ _e ∈ T, variance n β hβ f :=
      Finset.sum_le_sum (fun e _ => heatBathEnergy_le_variance n β hβ {e} f)
    _ = _ := by simp

def plaquetteSupport (x : SpatialVertex n) (i j : Fin 3) :
    Finset (SpatialVertex n × Fin 3) :=
  {(x, i), (spatialStep n x i, j), (spatialStep n x j, i), (x, j)}

omit [NeZero n] in
theorem plaquetteSupport_card (x : SpatialVertex n) (i j : Fin 3) :
    (plaquetteSupport n x i j).card ≤ 4 := Finset.card_le_four

omit [NeZero n] in
theorem plaquette_supported (x : SpatialVertex n) (i j : Fin 3) (u v : Slice n)
    (h : ∀ e ∈ plaquetteSupport n x i j, u e = v e) :
    WilsonPlaquetteTransport.plaquette n x i j u =
      WilsonPlaquetteTransport.plaquette n x i j v := by
  have h1 := h (x, i) (by simp [plaquetteSupport])
  have h2 := h (spatialStep n x i, j) (by simp [plaquetteSupport])
  have h3 := h (spatialStep n x j, i) (by simp [plaquetteSupport])
  have h4 := h (x, j) (by simp [plaquetteSupport])
  change (WilsonSingleLinkStaples.character (spatialHolonomy u x i j)).re =
    (WilsonSingleLinkStaples.character (spatialHolonomy v x i j)).re
  simp only [spatialHolonomy, h1, h2, h3, h4]

theorem plaquette_total_le (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (i j : Fin 3) :
    totalConditionalVariance n β hβ (WilsonPlaquetteTransport.plaquette n x i j) ≤
      4 * variance n β hβ (WilsonPlaquetteTransport.plaquette n x i j) := by
  have hc : ((plaquetteSupport n x i j).card : ℝ) ≤ 4 := by
    exact_mod_cast plaquetteSupport_card n x i j
  exact (supported_total_le n β hβ (plaquetteSupport n x i j) _
    (plaquette_supported n x i j)).trans
      (mul_le_mul_of_nonneg_right hc (variance_nonneg n β hβ _))

variable [Fact (1 < n)]

/-- A nonconstant four-link physical source forces A >= 1/4, independently of volume. -/
theorem factorization_budget (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n β hβ f ≤ A * totalConditionalVariance n β hβ f) :
    1 ≤ 4*A := by
  let f := WilsonPlaquetteTransport.plaquette n 0 0 1
  have hv := plaquette_variance_positive n β hβ 0 0 1 (by decide)
  have hf := hfactor f (WilsonPlaquetteTransport.plaquette_gauge n 0 0 1)
  have ht := mul_le_mul_of_nonneg_left (plaquette_total_le n β hβ 0 0 1) hA
  dsimp only [f] at hf
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonGroundLocalBudget
