/- A measure-preserving measurable equivalence gives an actual complex
L2 unitary, with its representative formula valid for every L2 vector. -/
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
noncomputable section
open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def pull (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ e he

theorem pull_coe (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 ν) :
    pull e he f =ᵐ[μ] f ∘ e := Lp.coeFn_compMeasurePreserving f he

theorem pull_reverse (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 ν) :
    pull e.symm he.symm (pull e he f) = f := by
  apply Lp.ext
  filter_upwards [pull_coe e.symm he.symm (pull e he f),
    he.symm.quasiMeasurePreserving.ae (pull_coe e he f)] with y hy hf
  simpa only [Function.comp_apply,MeasurableEquiv.apply_symm_apply] using hy.trans hf

def unitaryPullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { toLinearMap := (pull e he).toLinearMap
      invFun := pull e.symm he.symm
      left_inv := pull_reverse e he
      right_inv := pull_reverse e.symm he.symm }
  norm_map' := (pull e he).norm_map

theorem unitaryPullback_coe (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 ν) :
    unitaryPullback e he f =ᵐ[μ] f ∘ e := pull_coe e he f

theorem unitaryPullback_symm_coe (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 μ) :
    (unitaryPullback e he).symm f =ᵐ[ν] f ∘ e.symm := pull_coe e.symm he.symm f

#print axioms pull_reverse
#print axioms unitaryPullback
#print axioms unitaryPullback_coe
#print axioms unitaryPullback_symm_coe

end
end UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
