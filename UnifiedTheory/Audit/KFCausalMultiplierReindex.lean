/- Maximal multiplier equations are invariant under measure-preserving coordinates. -/
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMultiplierReindex
noncomputable section
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem weighted_iff (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (U : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hU : ∀ v, U v =ᵐ[μ] v ∘ e) (w : Y → ℂ) (f g : Lp ℂ 2 ν) :
    g =ᵐ[ν] (fun y => w y*f y) ↔
      U g =ᵐ[μ] (fun x => w (e x)*(U f) x) := by
  constructor
  · intro hg
    filter_upwards [hU g, hU f, he.quasiMeasurePreserving.ae hg] with x hx hy hz
    exact hx.trans (hz.trans (congrArg (fun z => w (e x)*z) hy.symm))
  · intro hg
    have ht : (fun x => g (e x)) =ᵐ[μ] fun x => w (e x)*f (e x) := by
      filter_upwards [hU g, hU f, hg] with x hx hy hz
      exact hx.symm.trans (hz.trans (congrArg (fun z => w (e x)*z) hy))
    simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using
      he.symm.quasiMeasurePreserving.ae ht

#print axioms weighted_iff
end
end UnifiedTheory.Audit.KFCausalMultiplierReindex
