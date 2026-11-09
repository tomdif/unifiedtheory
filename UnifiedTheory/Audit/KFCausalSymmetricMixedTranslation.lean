/- The two original symmetric physical translations pulled back through
the actual mixed clock chart. The second direction retains its neutral part. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
import UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricMixedTranslation
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint Block split)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalSymmetricMomentumCoordinates (rightVector symmetricBlock symmetricVector)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorMixedCoordinates (mixedWeight)
open KFCausalClockFloorPairedStraightening (clockInverse dilation)
open KFCausalClockFloorSpectatorChart (backward changeClock flow)

def rate (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℝ :=
  Real.exp (-((chartIso ε hε).symm q)/2)

def block (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (q : ℝ) : Block 4 := WithLp.toLp 2
  (![![0,2*scale*rate ε hε q,0,0],![0,0,2*scale*rate ε hε q,4*rate ε hε q-3]] i)

def velocity (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (q : ℝ) : Joint 2 4 :=
  rightVector (block ε hε i q)

theorem velocity_clock (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (q : ℝ) :
    velocity ε hε i q (.inr 0)=0 := by fin_cases i <;> rfl

theorem clock_translate (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (q t : ℝ) (x : Joint 2 4) :
    (x+t • velocity ε hε i q) (.inr 0)=x (.inr 0) := by
  simp [PiLp.add_apply,PiLp.smul_apply,velocity_clock]

theorem mixedWeight_translate (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (q t : ℝ) (x : Joint 2 4) :
    mixedWeight ε hε (split 2 4 (x+t • velocity ε hε i q))=mixedWeight ε hε (split 2 4 x) := by
  unfold mixedWeight clockInverse
  change (Real.sqrt (Real.exp ((chartIso ε hε).symm ((x+t • velocity ε hε i q) (.inr 0)))+ε):ℂ)⁻¹=_
  rw [clock_translate]
  rfl

theorem mixedMap_translate (ε : ℝ) (hε : 0 < ε) (i : Fin 2) (t : ℝ) (x : Joint 2 4) :
    (split 2 4).symm (mixedMap ε hε (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))))=
      (split 2 4).symm (mixedMap ε hε (split 2 4 x))+t • symmetricVector i := by
  have hc : (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))).2 0=(split 2 4 x).2 0 :=
    clock_translate ε hε i (x (.inr 0)) t x
  have he : Real.exp (((chartIso ε hε).symm (x (.inr 0)))/2)*rate ε hε (x (.inr 0))=1 := by
    rw [rate,← Real.exp_add,show (chartIso ε hε).symm (x (.inr 0))/2+
      (-(chartIso ε hε).symm (x (.inr 0))/2)=0 by ring,Real.exp_zero]
  ext j
  rcases j with j | j
  · change (dilation ε hε (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))).2)⁻¹*
      (x+t • velocity ε hε i (x (.inr 0))) (.inl j)=
        (dilation ε hε (split 2 4 x).2)⁻¹*x (.inl j)+t*symmetricVector i (.inl j)
    have hd : dilation ε hε (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))).2=
      dilation ε hε (split 2 4 x).2 := by unfold dilation clockInverse; rw [hc]
    rw [hd]
    simp [velocity,rightVector,symmetricVector]
  · change backward ε hε (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))).2 j=
      backward ε hε (split 2 4 x).2 j+t*symmetricBlock i j
    unfold backward changeClock flow
    simp only [hc]
    fin_cases i <;> fin_cases j
    all_goals dsimp [velocity,rightVector,block,symmetricBlock]
    all_goals simp only [KFCausalEuclideanProductCoordinates.split_snd,PiLp.add_apply,PiLp.smul_apply]
    all_goals try dsimp
    all_goals ring_nf at he ⊢
    all_goals try linear_combination (2*scale*t)*he
    all_goals rw [scale_square]
    all_goals linear_combination (4*t)*he

#print axioms velocity_clock
#print axioms clock_translate
#print axioms mixedWeight_translate
#print axioms mixedMap_translate
end
end UnifiedTheory.Audit.KFCausalSymmetricMixedTranslation
