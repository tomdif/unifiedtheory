/- The actual maximal field-square multiplication operator, and its
domain on the complex-shifted physical products. The signed linear-field
energy is also derived from the quadratic-domain condition. -/
import UnifiedTheory.Audit.KFCausalShiftedFieldEnergy
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseFieldSquare
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalShiftedFieldEnergy

def fieldSquare (l : Transverse →L[ℝ] ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  positiveMultiplier (fun z : Configuration => (l z.2)^2)
    ((l.continuous.comp continuous_snd).pow 2).measurable (fun _ => sq_nonneg _)

theorem fieldSquare_selfAdjoint (l : Transverse →L[ℝ] ℝ) : IsSelfAdjoint (fieldSquare l) :=
  multiplier_selfAdjoint _ _ _

theorem fieldSquare_graph (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) :
    (f,g) ∈ (fieldSquare l).graph ↔ g =ᵐ[volume] fun z : Configuration => (l z.2:ℂ)^2*f z := by
  simpa only [Complex.ofReal_pow] using multiplier_graph_iff
    (fun z : Configuration => (l z.2)^2) ((l.continuous.comp continuous_snd).pow 2).measurable
    (fun _ => sq_nonneg _) f g

theorem fieldSquare_domain (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ (fieldSquare l).domain ↔ MemLp (fun z : Configuration => (l z.2:ℂ)^2*f z) 2 := by
  simpa only [Complex.ofReal_pow] using multiplier_domain_iff
    (fun z : Configuration => (l z.2)^2) ((l.continuous.comp continuous_snd).pow 2).measurable
    (fun _ => sq_nonneg _) f

theorem fieldSquare_linear_energy (l : Transverse →L[ℝ] ℝ) (f : Hilbert)
    (hf : f ∈ (fieldSquare l).domain) : MemLp (fun z : Configuration => (l z.2:ℂ)*f z) 2 :=
  linear_field_memLp_of_quadratic f l (Lp.memLp f) ((fieldSquare_domain l f).mp hf)

theorem shiftedState_fieldSquare_domain (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    shiftedState ε a p y hε ha hy ψ (ψ.memLp 2 volume) ∈ (fieldSquare l).domain := by
  apply (fieldSquare_domain l _).mpr
  apply (quadraticFunction_memLp ε a p y hε ha hy ψ l).ae_eq
  filter_upwards [shiftedState_coe ε a p y hε ha hy ψ (ψ.memLp 2 volume)] with z hz
  change (l z.2:ℂ)^2*shiftedFunction ε a p y hε ψ z = _
  rw [hz]

theorem shiftedState_fieldSquare_coe (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    fieldSquare l ⟨shiftedState ε a p y hε ha hy ψ (ψ.memLp 2 volume),
      shiftedState_fieldSquare_domain ε a p y hε ha hy ψ l⟩ =ᵐ[volume]
      quadraticFunction ε a p y hε ψ l := by
  have hg := (fieldSquare_graph l _ _).mp ((fieldSquare l).mem_graph
    ⟨shiftedState ε a p y hε ha hy ψ (ψ.memLp 2 volume),
      shiftedState_fieldSquare_domain ε a p y hε ha hy ψ l⟩)
  filter_upwards [hg,shiftedState_coe ε a p y hε ha hy ψ (ψ.memLp 2 volume)] with z hz hs
  rw [hz,hs]
  rfl

#print axioms fieldSquare_selfAdjoint
#print axioms fieldSquare_graph
#print axioms fieldSquare_domain
#print axioms fieldSquare_linear_energy
#print axioms shiftedState_fieldSquare_domain
#print axioms shiftedState_fieldSquare_coe

end
end UnifiedTheory.Audit.KFCausalTransverseFieldSquare
