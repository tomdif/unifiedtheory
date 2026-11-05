/- The cyclic time-translation representation on ordinary L2 of the actual
finite Wilson law. These are measure-preserving pullbacks; they are not
operators on the Osterwalder--Schrader quotient and provide no OS generator. -/
import UnifiedTheory.Clay.YangMills.PeriodicTimeTranslation
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTranslationUnitary
noncomputable section
open MeasureTheory PeriodicLattice4 PeriodicTimeTranslation

variable (N : ℕ) [NeZero N] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)

abbrev StateSpace := Lp ℂ 2 (wilsonLaw N G χ β c)

def shiftL2 (s : ZMod N) : StateSpace N G χ β c →ₗᵢ[ℂ] StateSpace N G χ β c :=
  Lp.compMeasurePreservingₗᵢ ℂ (shiftConfiguration N G s)
    (wilsonLaw_preserves_shift N G χ hcχ β c s)

theorem shiftL2_ae (s : ZMod N) (f : StateSpace N G χ β c) :
    shiftL2 N G χ hcχ β c s f =ᵐ[wilsonLaw N G χ β c] f ∘ shiftConfiguration N G s :=
  Lp.coeFn_compMeasurePreserving f (wilsonLaw_preserves_shift N G χ hcχ β c s)

@[simp] theorem shiftL2_zero (f : StateSpace N G χ β c) : shiftL2 N G χ hcχ β c 0 f = f := by
  apply Lp.ext
  filter_upwards [shiftL2_ae N G χ hcχ β c 0 f] with U hU
  simpa only [Function.comp_apply, shiftConfiguration_zero] using hU

theorem shiftL2_add (s t : ZMod N) (f : StateSpace N G χ β c) :
    shiftL2 N G χ hcχ β c s (shiftL2 N G χ hcχ β c t f) =
      shiftL2 N G χ hcχ β c (s + t) f := by
  apply Lp.ext
  have hp := (wilsonLaw_preserves_shift N G χ hcχ β c s).quasiMeasurePreserving.ae
    (shiftL2_ae N G χ hcχ β c t f)
  filter_upwards [shiftL2_ae N G χ hcχ β c s (shiftL2 N G χ hcχ β c t f), hp,
    shiftL2_ae N G χ hcχ β c (s + t) f] with U h₁ h₂ h₃
  simp only [Function.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, shiftConfiguration_add, add_comm t s, h₃]

def shiftUnitary (s : ZMod N) : StateSpace N G χ β c ≃ₗᵢ[ℂ] StateSpace N G χ β c where
  toLinearEquiv :=
    { (shiftL2 N G χ hcχ β c s).toLinearMap with
      invFun := shiftL2 N G χ hcχ β c (-s)
      left_inv f := by
        change shiftL2 N G χ hcχ β c (-s) (shiftL2 N G χ hcχ β c s f) = f
        rw [shiftL2_add, neg_add_cancel, shiftL2_zero]
      right_inv f := by
        change shiftL2 N G χ hcχ β c s (shiftL2 N G χ hcχ β c (-s) f) = f
        rw [shiftL2_add, add_neg_cancel, shiftL2_zero] }
  norm_map' f := (shiftL2 N G χ hcχ β c s).norm_map f

@[simp] theorem shiftUnitary_apply (s : ZMod N) (f : StateSpace N G χ β c) :
    shiftUnitary N G χ hcχ β c s f = shiftL2 N G χ hcχ β c s f := rfl

theorem shiftUnitary_inner (s : ZMod N) (f g : StateSpace N G χ β c) :
    inner ℂ (shiftUnitary N G χ hcχ β c s f) (shiftUnitary N G χ hcχ β c s g) = inner ℂ f g :=
  (shiftUnitary N G χ hcχ β c s).inner_map_map f g

/-- A genuine group homomorphism from the finite cyclic time-translation group. -/
def cyclicRepresentation : Multiplicative (ZMod N) →*
    (StateSpace N G χ β c ≃ₗᵢ[ℂ] StateSpace N G χ β c) where
  toFun s := shiftUnitary N G χ hcχ β c s.toAdd
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    exact shiftL2_zero N G χ hcχ β c f
  map_mul' s t := by
    apply LinearIsometryEquiv.ext
    intro f
    exact (shiftL2_add N G χ hcχ β c s.toAdd t.toAdd f).symm

end
end UnifiedTheory.Clay.YangMills.WilsonTranslationUnitary
