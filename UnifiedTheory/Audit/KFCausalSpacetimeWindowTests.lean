/- A time cutoff equal to one on the physical window makes each local
momentum test an admissible spacetime test. This identifies the whole-window
force response without discarding possible escaped momentum mass. -/
import UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
noncomputable section
open MeasureTheory BoundedContinuousFunction
open scoped ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (Square pullback)
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
open UnifiedTheory.Audit.KFCausalFiniteKernelInterval

theorem exists_time_cutoff (b c : ℝ) : ∃ χ : Spectrum →ᵇ ℂ,
    (∀ t ∈ Set.Icc b c, χ (KFCausalCompactifiedForceMeasure.embed t) = 1) ∧
    (∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0) := by
  have hi : IsOpen KFCausalLocalForceMeasure.interior :=
    isOpen_Ioo.preimage continuous_subtype_val
  have hk : IsClosed (KFCausalCompactifiedForceMeasure.embed '' Set.Icc b c) :=
    (isCompact_Icc.image KFCausalCompactifiedForceMeasure.embed_continuous).isClosed
  have hd : Disjoint KFCausalLocalForceMeasure.interiorᶜ
      (KFCausalCompactifiedForceMeasure.embed '' Set.Icc b c) := by
    apply Set.disjoint_left.mpr
    intro x hx hK
    rcases hK with ⟨t,_,rfl⟩
    exact hx (KFCausalVanishingForceTests.embed_interior t)
  obtain ⟨f,hzero,hone,_⟩ := exists_continuous_zero_one_of_isClosed hi.isClosed_compl hk hd
  let χ : Spectrum →ᵇ ℂ := mkOfCompact ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  refine ⟨χ,?_,?_⟩
  · intro t ht
    change (f (KFCausalCompactifiedForceMeasure.embed t):ℂ) = 1
    rw [hone ⟨t,ht,rfl⟩]
    norm_num
  · intro x hx
    change (f x:ℂ) = 0
    rw [hzero hx]
    norm_num

def liftTest (χ : Spectrum →ᵇ ℂ) (f : C₀(ℝ,ℂ)) : Square →ᵇ ℂ :=
  χ.compContinuous ⟨Prod.fst,continuous_fst⟩ *
    (KFCausalVanishingForceTests.extension f).compContinuous ⟨Prod.snd,continuous_snd⟩

theorem liftTest_boundary (χ : Spectrum →ᵇ ℂ)
    (hχ : ∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0)
    (f : C₀(ℝ,ℂ)) (z : Square) (hz : z ∉ KFCausalLocalSpacetimeTests.interior) :
    liftTest χ f z = 0 := by
  change χ z.1 * KFCausalVanishingForceTests.extension f z.2 = 0
  by_cases ht : z.1 ∈ KFCausalLocalForceMeasure.interior
  · have hp : z.2 ∉ KFCausalLocalForceMeasure.interior := fun h => hz ⟨ht,h⟩
    rw [KFCausalVanishingForceTests.extension_boundary f z.2 hp,mul_zero]
  · rw [hχ z.1 ht,zero_mul]

theorem liftTest_on_window (b c : ℝ) (χ : Spectrum →ᵇ ℂ)
    (hχ : ∀ t ∈ Set.Icc b c, χ (KFCausalCompactifiedForceMeasure.embed t) = 1)
    (f : C₀(ℝ,ℂ)) (t p : ℝ) (ht : t ∈ Set.Icc b c) :
    pullback (liftTest χ f) (t,p) = f p := by
  change χ (KFCausalCompactifiedForceMeasure.embed t) *
    KFCausalVanishingForceTests.extension f (KFCausalCompactifiedForceMeasure.embed p) = _
  rw [hχ t ht,one_mul]
  exact congrArg (fun q : ℝ →ᵇ ℂ => q p) (KFCausalVanishingForceTests.extension_pullback f)

theorem fromCurve_window_test {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : ℝ) (w : Fin 8 → ℂ) (y : ℝ → Lp KFCausalNeutralTranslationOutput.Outputs 2 μ)
    (hy : Continuous y) (b c : ℝ) (χ : Spectrum →ᵇ ℂ)
    (hχ : ∀ t ∈ Set.Icc b c, χ (KFCausalCompactifiedForceMeasure.embed t) = 1)
    (f : C₀(ℝ,ℂ)) :
    (fromCurve μ h w y hy b c).evaluate (pullback (liftTest χ f)) =
      (intervalPair μ h w y hy b c).evaluate f.toBCF := by
  simp only [Pair.evaluate,fromCurve_positive_test,fromCurve_negative_test,
    FluxPair.evaluate,intervalPair]
  rw [integrated_test _ (positive_mass_continuous μ h w y hy),
    integrated_test _ (negative_mass_continuous μ h w y hy)]
  apply congrArg₂ (fun a b : ℂ => (a-b)/2)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => liftTest_on_window b c χ hχ f t p ht)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => liftTest_on_window b c χ hχ f t p ht)

#print axioms exists_time_cutoff
#print axioms liftTest_boundary
#print axioms liftTest_on_window
#print axioms fromCurve_window_test
end
end UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
