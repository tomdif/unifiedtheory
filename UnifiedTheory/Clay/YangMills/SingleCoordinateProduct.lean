/- Exact product-measure splitting at one finite coordinate. -/
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Logic.Equiv.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SingleCoordinateProduct
noncomputable section
open MeasureTheory

variable {I G : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace G]

abbrev Outside (e : I) := {i : I // i ≠ e} → G

def assemble (e : I) : Outside (G := G) e × G ≃ᵐ (I → G) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => G)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : I => G) (Equiv.optionSubtypeNe e))

@[simp] theorem assemble_self (e : I) (z : Outside (G := G) e × G) :
    assemble e z e = z.2 := by
  change (MeasurableEquiv.piCongrLeft (fun _ : I => G) (Equiv.optionSubtypeNe e)
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => G)).symm z))
      (Equiv.optionSubtypeNe e none) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp] theorem assemble_other (e i : I) (hi : i ≠ e) (z : Outside (G := G) e × G) :
    assemble e z i = z.1 ⟨i, hi⟩ := by
  change (MeasurableEquiv.piCongrLeft (fun _ : I => G) (Equiv.optionSubtypeNe e)
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => G)).symm z))
      (Equiv.optionSubtypeNe e (some ⟨i, hi⟩)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem assemble_continuous [TopologicalSpace G] (e : I) : Continuous (assemble (G := G) e) := by
  apply continuous_pi
  intro i
  by_cases hi : i = e
  · subst i
    simpa only [assemble_self] using (continuous_snd : Continuous (fun z : Outside (G := G) e × G => z.2))
  · simpa only [assemble_other e i hi] using
      ((continuous_apply (⟨i, hi⟩ : {j : I // j ≠ e})).comp continuous_fst :
        Continuous (fun z : Outside (G := G) e × G => z.1 ⟨i, hi⟩))

theorem assemble_preserving (e : I) (μ : Measure G) [SigmaFinite μ] :
    MeasurePreserving (assemble e) ((Measure.pi (fun _ : {i : I // i ≠ e} => μ)).prod μ)
      (Measure.pi (fun _ : I => μ)) := by
  have hopt : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => G)).symm
      ((Measure.pi (fun _ : {i : I // i ≠ e} => μ)).prod μ)
      (Measure.pi (fun _ : Option {i : I // i ≠ e} => μ)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => μ)⟩
  exact (measurePreserving_piCongrLeft (fun _ : I => μ) (Equiv.optionSubtypeNe e)).comp hopt

end
end UnifiedTheory.Clay.YangMills.SingleCoordinateProduct
