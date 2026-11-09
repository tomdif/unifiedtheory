/- Joint L1 integrability of the full sheared Gaussian follows from the
proved L2 bound with halved widths. Volume-preserving regrouping puts the
same functions into Euclidean clock/transverse coordinates. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
import UnifiedTheory.Audit.KFCausalEuclideanClockSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianL1
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit

theorem clockFactor_half_square (a : ℝ) (q : ℂ) :
    (clockFactor (a/2) q)^2 = clockFactor a q := by
  rw [clockFactor,← Complex.exp_nat_mul]
  unfold clockFactor
  congr 1
  push_cast
  ring

theorem packet_half_square (α β : ℝ) (z : ℂ) (x : Grouped) :
    (packet (α/2) (β/2) z x)^2 = packet α β z x := by
  rw [packet,← Complex.exp_nat_mul]
  unfold packet quadratic
  congr 1
  push_cast
  ring

theorem line_half_square (ε a α β y : ℝ) (z : ℝ × Grouped) :
    (line ε (a/2) (α/2) (β/2) y z)^2 = line ε a α β y z := by
  simp only [line,trial,mul_pow,clockFactor_half_square,packet_half_square]

theorem line_integrable (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (line ε a α β y) := by
  have hp := line_memLp ε (a/2) (α/2) (β/2) y hε (by positivity) (by positivity)
    (by positivity) (by linarith) hy
  have hi := (memLp_two_iff_integrable_sq_norm hp.1).mp hp
  apply (integrable_norm_iff (line_continuous ε a α β y hε hy).aestronglyMeasurable).mp
  convert hi using 1
  funext z
  rw [← line_half_square ε a α β y z,norm_pow]

def tailGrouping : TailSpace ≃ᵐ Grouped := transverseCoordinates.symm.trans transverseGrouping

theorem tailGrouping_apply (y : TailSpace) :
    tailGrouping y = (fun i : Fin 4 => y i.castSucc,y 4) := by
  exact transverseGrouping_apply _

theorem tailGrouping_continuous : Continuous tailGrouping := by
  change Continuous (fun y : TailSpace => transverseGrouping (transverseCoordinates.symm y))
  simp only [transverseGrouping_apply]
  change Continuous (fun y : TailSpace => (fun i : Fin 4 => y i.castSucc,y 4))
  fun_prop

theorem tailGrouping_preserves_volume : MeasurePreserving tailGrouping :=
  transverseGrouping_preserves_volume.comp transverse_preserves_volume.symm

def pairGrouping : (ℝ × TailSpace) ≃ᵐ (ℝ × Grouped) :=
  (MeasurableEquiv.refl ℝ).prodCongr tailGrouping

theorem pairGrouping_preserves_volume : MeasurePreserving pairGrouping :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod tailGrouping_preserves_volume

theorem pairGrouping_euclideanSplit (x : KFCausalEuclideanConfiguration.Space) :
    pairGrouping (euclideanSplit x) = grouping (KFCausalEuclideanConfiguration.split x) := rfl

def euclideanLine (ε a α β y : ℝ) (z : ℝ × TailSpace) : ℂ :=
  line ε a α β y (pairGrouping z)

theorem euclideanLine_continuous (ε a α β y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (euclideanLine ε a α β y) :=
  (line_continuous ε a α β y hε hy).comp
    (continuous_fst.prodMk (tailGrouping_continuous.comp continuous_snd))

theorem euclideanLine_integrable (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (euclideanLine ε a α β y) :=
  pairGrouping_preserves_volume.integrable_comp_of_integrable
    (line_integrable ε a α β y hε ha hα hβ hw hy)

theorem euclideanLine_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (euclideanLine ε a α β y) 2 :=
  (line_memLp ε a α β y hε ha hα hβ hw hy).comp_measurePreserving pairGrouping_preserves_volume

#print axioms clockFactor_half_square
#print axioms packet_half_square
#print axioms line_half_square
#print axioms line_integrable
#print axioms tailGrouping_apply
#print axioms tailGrouping_continuous
#print axioms tailGrouping_preserves_volume
#print axioms pairGrouping_preserves_volume
#print axioms pairGrouping_euclideanSplit
#print axioms euclideanLine_continuous
#print axioms euclideanLine_integrable
#print axioms euclideanLine_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianL1
