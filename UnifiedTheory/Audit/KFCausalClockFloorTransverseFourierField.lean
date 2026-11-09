/- The actual physical transverse Fourier unitary preserves and reflects
all powers of the physical point field. Its straightened symbol depends
only on spectator coordinates, as derived from the original clock shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorMultiplicationRelations
import UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierField
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block split)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square modeIsometry)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorMultiplicationRelations (symbol straightening_relation)
open UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph (action straightening_action)
open UnifiedTheory.Audit.KFCausalTransverseFourierClock (transverse_relation)

variable (ε : ℝ) (hε : 0 < ε)

def fieldSymbol (y : Block 4) : ℂ :=
  ((y 3+2*scale*(3*Real.exp ((chartIso ε hε).symm (y 0)/2)-2)*y 2:ℝ):ℂ)

theorem fieldSymbol_measurable : Measurable (fieldSymbol ε hε) := by
  have hc : Continuous ((chartIso ε hε).symm : ℝ → ℝ) := (chartIso ε hε).symm.toHomeomorph.continuous
  unfold fieldSymbol
  fun_prop

theorem fieldSymbol_physical (x : Space) :
    fieldSymbol ε hε (split 2 4 (modeIsometry x)).2 =
      symbol ε hε (fun z => (pointField z.2:ℂ)) x := by
  change ((x 5+2*scale*(3*Real.exp ((chartIso ε hε).symm (x 0)/2)-2)*
    (scale*(x 3+x 4)):ℝ):ℂ) =
    ((Real.exp ((chartIso ε hε).symm (x 0)/2)*x 3+
      Real.exp ((chartIso ε hε).symm (x 0)/2)*x 4+
      (x 5+2*(Real.exp ((chartIso ε hε).symm (x 0)/2)-1)*(x 3+x 4)):ℝ):ℂ)
  congr 1
  ring_nf
  rw [scale_square]
  ring

theorem field_power_straightening (j : ℕ) (f g : Hilbert) :
    (g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) ↔
      KFCausalClockFloorDefectCoordinates.straightening ε hε g =ᵐ[volume] fun x =>
        (fieldSymbol ε hε (split 2 4 (modeIsometry x)).2)^j*
          (KFCausalClockFloorDefectCoordinates.straightening ε hε f) x := by
  rw [straightening_relation ε hε (fun x => (pointField x.2:ℂ)^j)]
  simp only [fieldSymbol_physical,symbol]

theorem action_field_power (j : ℕ) (f g : Hilbert) :
    (g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) ↔
      action ε hε g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*(action ε hε f) x := by
  rw [field_power_straightening ε hε,field_power_straightening ε hε,
    straightening_action,straightening_action]
  exact transverse_relation (fun y => (fieldSymbol ε hε y)^j)
    ((fieldSymbol_measurable ε hε).pow_const j) _ _

theorem inverse_action_field_power (j : ℕ) (f g : Hilbert) :
    (g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) ↔
      (action ε hε).symm g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*((action ε hε).symm f) x := by
  have he := action_field_power ε hε j ((action ε hε).symm f) ((action ε hε).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm

#print axioms fieldSymbol_measurable
#print axioms fieldSymbol_physical
#print axioms field_power_straightening
#print axioms action_field_power
#print axioms inverse_action_field_power

end
end UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierField
