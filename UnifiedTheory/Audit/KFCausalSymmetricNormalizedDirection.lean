/- Symmetric physical derivatives become constant directions in the
normalized Gaussian variables, including the full neutral contribution. -/
import UnifiedTheory.Audit.KFCausalSymmetricMixedTranslation
import UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricNormalizedDirection
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalComplexClockInverse (complexInverse complexInverse_real)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalSymmetricMixedTranslation (rate block velocity)
open KFCausalSymmetricMomentumCoordinates (rightVector)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalTwoShearClockQuotient (shift)

def direction (α w : ℝ) (i : Fin 2) : Space := WithLp.toLp 2
  (![![0,0,((2*scale*Real.sqrt (α/w):ℝ):ℂ),0,0],
     ![0,0,0,((2*scale*Real.sqrt (α*w):ℝ):ℂ),((Real.sqrt (α/32):ℝ):ℂ)]] i)

def targetDirection (ε h α w θ : ℝ) (i : Fin 2) (q : ℂ) : Space :=
  rotatedFlow (rotationIsometry θ) (coupling α w)
    (complexInverse ε (shift h q)-complexInverse ε q) (direction α w i)

private theorem flow_affine (σ : ℝ) (z t : ℂ) (x v : Space) :
    flow σ z (x+t • v)=flow σ z x+t • flow σ z v := by
  ext i
  fin_cases i <;> simp [flow] <;> ring

private theorem normalize_affine (α w c t : ℝ) (x v : Joint 2 4) :
    KFCausalPhysicalReciprocalNormalization.normalize α w c (x+t • v)=
      KFCausalPhysicalReciprocalNormalization.normalize α w c x+
        (t:ℂ) • KFCausalPhysicalReciprocalNormalization.normalize α w c v := by
  ext i
  fin_cases i <;> simp [KFCausalPhysicalReciprocalNormalization.normalize] <;> ring

theorem baselineVector_velocity (ε : ℝ) (hε : 0 < ε) (α w c : ℝ) (i : Fin 2) (q : ℝ)
    (hα : 0 < α) (hw : 0 < w) :
    baselineVector ε α w c (q:ℂ) (velocity ε hε i q)=direction α w i := by
  have hn : (Real.sqrt (α*w):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have he : Complex.exp (((chartIso ε hε).symm q:ℂ)/2)*(rate ε hε q:ℂ)=1 := by
    rw [show ((chartIso ε hε).symm q:ℂ)/2=(((chartIso ε hε).symm q/2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp,← Complex.ofReal_mul]
    have hr : Real.exp ((chartIso ε hε).symm q/2)*rate ε hε q=1 := by
      rw [rate,← Real.exp_add,show (chartIso ε hε).symm q/2+(-(chartIso ε hε).symm q/2)=0 by ring,
        Real.exp_zero]
    rw [hr,Complex.ofReal_one]
  have hs : (scale:ℂ)^2=1/2 := by rw [← Complex.ofReal_pow,scale_square]; norm_num
  rw [baselineVector,complexInverse_real ε hε]
  fin_cases i <;> ext j <;> fin_cases j
  all_goals dsimp [flow,KFCausalPhysicalReciprocalNormalization.normalize,velocity,rightVector,
    block,direction,coupling]
  all_goals push_cast
  all_goals try field_simp [hn]
  all_goals ring_nf at he ⊢
  all_goals try rw [hs]
  all_goals rw [he]
  all_goals ring

theorem baselineVector_affine (ε : ℝ) (hε : 0 < ε) (α w c : ℝ) (i : Fin 2)
    (q t : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    baselineVector ε α w c (q:ℂ) (x+t • velocity ε hε i q)=
      baselineVector ε α w c (q:ℂ) x+(t:ℂ) • direction α w i := by
  unfold baselineVector
  rw [normalize_affine,flow_affine]
  rw [show flow (coupling α w) (complexInverse ε (q:ℂ))
    (KFCausalPhysicalReciprocalNormalization.normalize α w c (velocity ε hε i q))=
      direction α w i from baselineVector_velocity ε hε α w c i q hα hw]

theorem targetVector_affine (ε : ℝ) (hε : 0 < ε) (h α w c θ : ℝ) (i : Fin 2)
    (q t : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    targetVector ε h α w c θ (q:ℂ) (x+t • velocity ε hε i q)=
      targetVector ε h α w c θ (q:ℂ) x+(t:ℂ) • targetDirection ε h α w θ i (q:ℂ) := by
  rw [targetVector,baselineVector_affine ε hε α w c i q t x hα hw]
  simp only [rotatedFlow,map_add,map_smul,flow_affine]
  rfl

#print axioms baselineVector_velocity
#print axioms baselineVector_affine
#print axioms targetVector_affine
end
end UnifiedTheory.Audit.KFCausalSymmetricNormalizedDirection
