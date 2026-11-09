/- Finite complex combinations of actual L2 representatives. -/
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives
noncomputable section
open MeasureTheory

theorem sum_coe {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (∑ i ∈ s, f i : Lp ℂ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 μ
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j),ih] with x hx hs
      rw [hx,Pi.add_apply,hs,Finset.sum_insert hi]

theorem weighted_sum_coe {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    (μ : Measure X) (d : ι → ℂ) (f : ι → Lp ℂ 2 μ) (F : ι → X → ℂ)
    (hF : ∀ i, f i =ᵐ[μ] F i) :
    (∑ i, d i • f i : Lp ℂ 2 μ) =ᵐ[μ] fun x => ∑ i, d i*F i x := by
  have he : ∀ᵐ x ∂μ, ∀ i, (d i • f i : Lp ℂ 2 μ) x = d i*F i x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (d i) (f i),hF i] with x hx hf
    simp only [hx,Pi.smul_apply,smul_eq_mul,hf]
  filter_upwards [sum_coe μ Finset.univ (fun i => d i • f i),he] with x hx he
  rw [hx]
  exact Finset.sum_congr rfl (fun i _ => he i)

#print axioms sum_coe
#print axioms weighted_sum_coe
end
end UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives
