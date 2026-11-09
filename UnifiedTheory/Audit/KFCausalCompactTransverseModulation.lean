/- Countably many compact smooth transverse packets cover the whole tail
space. Their frequency modulations remain actual Schwartz functions. -/
import UnifiedTheory.Audit.KFCausalEuclideanClockSplit
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCompactTransverseModulation
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit

def bump (n : ℕ) : ContDiffBump (0 : TailSpace) where
  rIn := (n:ℝ)+1
  rOut := (n:ℝ)+2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def base (n : ℕ) (y : TailSpace) : ℂ := (bump n y : ℝ)

theorem base_compact (n : ℕ) : HasCompactSupport (base n) :=
  (bump n).hasCompactSupport.comp_left (show Complex.ofReal 0=0 from rfl)

theorem base_smooth (n : ℕ) : ContDiff ℝ ∞ (base n) :=
  Complex.ofRealCLM.contDiff.comp (bump n).contDiff

def packet (n : ℕ) : SchwartzMap TailSpace ℂ :=
  (base_compact n).toSchwartzMap (base_smooth n)

theorem packet_cover (y : TailSpace) : ∃ n : ℕ, packet n y = 1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt ‖y‖
  refine ⟨n,?_⟩
  change (bump n y : ℂ)=1
  rw [(bump n).one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall,dist_zero_right,bump] using
      (show ‖y‖ ≤ (n:ℝ)+1 by linarith)

def phase (k y : TailSpace) : ℂ := Real.fourierChar (inner ℝ y k)

theorem phase_smooth (k : TailSpace) : ContDiff ℝ ∞ (phase k) := by
  change ContDiff ℝ ∞ (fun y : TailSpace => (Real.fourierChar (inner ℝ y k):ℂ))
  simp only [Real.fourierChar_apply]
  have hi : ContDiff ℝ ∞ (fun y : TailSpace => 2*Real.pi*inner ℝ y k) :=
    contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)
  exact ((Complex.ofRealCLM.contDiff.comp hi).mul contDiff_const).cexp

def modulatedPacket (n : ℕ) (k : TailSpace) : SchwartzMap TailSpace ℂ :=
  ((base_compact n).mul_left (f := phase k)).toSchwartzMap
    ((phase_smooth k).mul (base_smooth n))

theorem modulatedPacket_apply (n : ℕ) (k y : TailSpace) :
    modulatedPacket n k y = (Real.fourierChar (inner ℝ y k):ℂ)*packet n y := rfl

#print axioms base_compact
#print axioms base_smooth
#print axioms packet_cover
#print axioms phase_smooth
#print axioms modulatedPacket_apply

end
end UnifiedTheory.Audit.KFCausalCompactTransverseModulation
