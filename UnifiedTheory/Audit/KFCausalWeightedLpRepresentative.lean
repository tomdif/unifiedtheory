/- Weighted representative identities extend from a dense set to all L2
vectors. Two subsequences and a proved preservation of null sets control
the exceptional sets; no boundedness of the pointwise weight is assumed. -/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem weighted_representative_limit (e : Y → X) (he : Measure.QuasiMeasurePreserving e ν μ)
    (w : Y → ℂ) (f : ℕ → Lp ℂ 2 μ) (g : ℕ → Lp ℂ 2 ν)
    (f₀ : Lp ℂ 2 μ) (g₀ : Lp ℂ 2 ν)
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hr : ∀ n, (g n : Y → ℂ) =ᵐ[ν] fun y => w y*(f n) (e y)) :
    (g₀ : Y → ℂ) =ᵐ[ν] fun y => w y*f₀ (e y) := by
  obtain ⟨σ,hσ,hfa⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨τ,hτ,hga⟩ := (tendstoInMeasure_of_tendsto_Lp (hg.comp hσ.tendsto_atTop)).exists_seq_tendsto_ae
  have hseq : ∀ n : ℕ, (g (σ (τ n)) : Y → ℂ) =ᵐ[ν]
      fun y => w y*(f (σ (τ n))) (e y) := fun n => hr (σ (τ n))
  filter_upwards [he.ae hfa,hga,ae_all_iff.mpr hseq] with y hfy hgy hry
  have hp : Tendsto (fun n => w y*(f (σ (τ n))) (e y)) atTop (𝓝 (w y*f₀ (e y))) :=
    tendsto_const_nhds.mul (hfy.comp hτ.tendsto_atTop)
  have hh : Tendsto (fun n => (g (σ (τ n))) y) atTop (𝓝 (w y*f₀ (e y))) := by
    simpa only [hry] using hp
  exact tendsto_nhds_unique hgy hh

theorem dense_weighted_representative {D : Type*} (j : D → Lp ℂ 2 μ) (hj : DenseRange j)
    (U : Lp ℂ 2 μ → Lp ℂ 2 ν) (hU : Continuous U)
    (e : Y → X) (he : Measure.QuasiMeasurePreserving e ν μ) (w : Y → ℂ)
    (hr : ∀ d : D, (U (j d) : Y → ℂ) =ᵐ[ν] fun y => w y*(j d) (e y))
    (f : Lp ℂ 2 μ) : (U f : Y → ℂ) =ᵐ[ν] fun y => w y*f (e y) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp (hj f)
  choose d hd using hv
  have hseq : Tendsto (fun n => j (d n)) atTop (𝓝 f) := by
    simpa only [hd] using hlim
  exact weighted_representative_limit e he w (fun n => j (d n)) (fun n => U (j (d n)))
    f (U f) hseq ((hU.tendsto f).comp hseq) (fun n => hr (d n))

theorem inverse_weighted_representative (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (e : Y ≃ᵐ X) (hi : Measure.QuasiMeasurePreserving e.symm μ ν)
    (w : Y → ℂ) (hw : ∀ y, w y ≠ 0)
    (hr : ∀ f : Lp ℂ 2 μ, (U f : Y → ℂ) =ᵐ[ν] fun y => w y*f (e y))
    (g : Lp ℂ 2 ν) :
    (U.symm g : X → ℂ) =ᵐ[μ] fun x => (w (e.symm x))⁻¹*g (e.symm x) := by
  filter_upwards [hi.ae (hr (U.symm g))] with x hx
  rw [U.apply_symm_apply,e.apply_symm_apply] at hx
  rw [hx,← mul_assoc,inv_mul_cancel₀ (hw (e.symm x)),one_mul]

#print axioms weighted_representative_limit
#print axioms dense_weighted_representative
#print axioms inverse_weighted_representative

end
end UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
