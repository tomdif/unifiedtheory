/- The fixed transverse coordinate attachment for actual mixed-strip
multipliers. It preserves the clock coordinate and yields Hilbert equality
from the actual mixed-coordinate multiplication representative. -/
import UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph
import UnifiedTheory.Audit.KFCausalPhysicalReciprocalNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalMixedStripTailAttachment
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalEuclideanProductCoordinates (Joint split split_preserves_volume)
open KFCausalPairedModeCoordinates (modeIsometry mode_preserves_volume)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorDefectCoordinates (straightening)

def tailPoint (z : TailSpace) : Joint 2 4 :=
  modeIsometry (WithLp.toLp 2 ![0,z 0,z 1,z 2,z 3,z 4])

theorem tailPoint_continuous : Continuous tailPoint := by
  unfold tailPoint
  apply modeIsometry.continuous.comp
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) 0
  · exact PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) 1
  · exact PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) 2
  · exact PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) 3
  · exact PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) 4

theorem normalize_tail (α w c : ℝ) (x : Space) :
    KFCausalPhysicalReciprocalNormalization.normalize α w c (tailPoint (tail x)) =
      KFCausalPhysicalReciprocalNormalization.normalize α w c (modeIsometry x) := by
  ext i
  fin_cases i <;> rfl

def family (G : ℂ → Joint 2 4 → ℂ) (q : ℂ) (z : TailSpace) : ℂ := G q (tailPoint z)

theorem family_horizontal_continuous (G : ℂ → Joint 2 4 → ℂ) (d : ℝ)
    (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × Joint 2 4 => G ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2)) :
    ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => family G ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2) := by
  intro y hy
  exact (hC y hy).comp (continuous_fst.prodMk (tailPoint_continuous.comp continuous_snd))

theorem action_of_clockMixed (ε : ℝ) (hε : 0 < ε)
    (G : ℂ → Joint 2 4 → ℂ) (d M : ℝ)
    (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => family G ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
    (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖family G q z‖ ≤ M)
    (hG : ∀ q x, G q (tailPoint (tail x))=G q (modeIsometry x))
    (h0 : |(0:ℝ)| ≤ d) (f g : Hilbert)
    (hfg : clockMixed ε hε g =ᵐ[volume] fun x =>
      G (x.2 0:ℂ) ((split 2 4).symm x)*(clockMixed ε hε f) x) :
    KFCausalMixedStripExponentialGraph.action ε hε (family G) d M hC hM hB 0 h0 f=g := by
  apply (KFCausalMixedStripExponentialGraph.unitary ε hε).injective
  apply (straightening ε hε).injective
  apply Lp.ext
  have hp := ((split_preserves_volume 2 4).comp mode_preserves_volume).quasiMeasurePreserving.ae hfg
  filter_upwards [KFCausalMixedStripExponentialGraph.action_coe ε hε (family G) d M hC hM hB 0 h0 f,
    KFCausalMixedStripExponentialGraph.unitary_straightening_coe ε hε f,
    KFCausalMixedStripExponentialGraph.unitary_straightening_coe ε hε g,hp] with x hx hf hg hp
  simp only [Function.comp_apply] at hp
  rw [hx,hf,hg,hp]
  simp only [KFCausalStripFamilyExponentialGraph.symbol,family,Complex.ofReal_zero,
    zero_mul,add_zero,hG,MeasurableEquiv.symm_apply_apply]
  rfl

#print axioms tailPoint_continuous
#print axioms normalize_tail
#print axioms family_horizontal_continuous
#print axioms action_of_clockMixed
end
end UnifiedTheory.Audit.KFCausalMixedStripTailAttachment
