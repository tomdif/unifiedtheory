/- Identify the existing complex-shifted Gaussian state with a physical
Gaussian profile whose relative transverse scale is bounded. All L2 and
quadratic-moment hypotheses come from the existing Gaussian estimates. -/
import UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
import UnifiedTheory.Audit.KFCausalRelativeGaussianShearDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter (gaussianState_quadratic_memLp)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile)

def clockAmplitude (ε a p y s : ℝ) : ℂ :=
  (amplitude ε s:ℂ)*clockPhase p (inverse ε y s)*clockFactor a (argument ε y s)

theorem clockAmplitude_smooth (ε a p y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (clockAmplitude ε a p y) := by
  have ha : ContDiff ℝ 1 (amplitude ε) := by
    unfold amplitude
    exact (((contDiff_id.exp).add contDiff_const).sqrt (fun s => ne_of_gt (by positivity))).mul
      contDiff_id.neg.exp
  have hp : ContDiff ℝ 1 (fun s => clockPhase p (inverse ε y s)) :=
    (contDiff_const.mul (inverse_smooth ε y hε hy)).cexp
  have hg : ContDiff ℝ 1 (fun s => clockFactor a (argument ε y s)) := by
    unfold clockFactor
    exact (contDiff_const.mul ((argument_smooth ε y).pow 2)).cexp
  exact ((Complex.ofRealCLM.contDiff.comp ha).mul hp).mul hg

theorem quadratic_positions (α β : ℝ) (z : ℂ) (x : KFCausalClockFloorShearBounds.Grouped) :
    KFCausalClockFloorShearBounds.quadratic α β z x.1 x.2 =
      ∑ i, (widths α β i:ℂ)*(KFCausalClockFloorCoherentBounds.position z x i)^2 := by
  simp only [widths,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    KFCausalClockFloorCoherentBounds.position,Matrix.cons_val_zero,Matrix.cons_val_succ,
    KFCausalClockFloorShearBounds.quadratic,KFCausalClockFloorShearBounds.squared,
    KFCausalClockFloorCoherentBounds.neutral]
  rw [← KFCausalClockFloorShearBounds.complexScale_square]
  push_cast
  ring

theorem recentered_packet (α β : ℝ) (b : Fin 5 → ℂ) (z : ℂ) (s : ℝ) (q : Transverse) :
    KFCausalClockFloorCoherentBounds.coherentPacket α β b z
      (KFCausalClockFloorDisplacedShiftPhase.grouped (flow (-s) q)) =
      Complex.exp (KFCausalRelativeGaussianDifferential.exponent α β b
        (KFCausalClockFloorShearBounds.complexScale (z-(s:ℂ))) q) := by
  have hp (i : Fin 5) := KFCausalClockFloorDisplacedShiftPhase.position_recenter z s q i
  simp only [Complex.ofReal_add] at hp
  change ∀ i, _ = KFCausalRelativeGaussianDifferential.position
    (KFCausalClockFloorShearBounds.complexScale (z-(s:ℂ))) q i at hp
  simp only [KFCausalClockFloorCoherentBounds.coherentPacket,KFCausalClockFloorShearBounds.packet,
    ← Complex.exp_add,KFCausalClockFloorCoherentBounds.source,quadratic_positions,hp,
    KFCausalRelativeGaussianDifferential.exponent,sub_eq_add_neg]

theorem physical_profile (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε) (x : Configuration) :
    weightedFunction ε hε (configurationLine ε a α β p b y) x =
      profile (clockAmplitude ε a p y) (scale ε y) α β b x := by
  have hg (q : Transverse) : KFCausalClockFloorGroupedCoordinates.transverseGrouping q =
      KFCausalClockFloorDisplacedShiftPhase.grouped q := by
    rw [KFCausalClockFloorGroupedCoordinates.transverseGrouping_apply]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  change (amplitude ε x.1:ℂ)*
    (clockPhase p (inverse ε y x.1)*clockFactor a (argument ε y x.1)*
      KFCausalClockFloorCoherentBounds.coherentPacket α β b (inverse ε y x.1)
        (KFCausalClockFloorGroupedCoordinates.transverseGrouping (flow (-x.1) x.2))) = _
  rw [hg,recentered_packet]
  unfold profile clockAmplitude scale relative
  ring

theorem gaussianState_profile (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy =ᵐ[volume]
      profile (clockAmplitude ε a p y) (scale ε y) α β b := by
  filter_upwards [gaussianState_coe ε a α β p b y hε ha hα hβ hw hy] with x hx
  exact hx.trans (physical_profile ε a α β p y b hε x)

theorem profile_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (profile (clockAmplitude ε a p y) (scale ε y) α β b) 2 volume :=
  (Lp.memLp (gaussianState ε a α β p b y hε ha hα hβ hw hy)).ae_eq
    (gaussianState_profile ε a α β p y b hε ha hα hβ hw hy)

theorem profile_quadratic_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (i : Fin 5) :
    MemLp (fun x => (x.2 i:ℂ)^2*profile (clockAmplitude ε a p y) (scale ε y) α β b x) 2 volume := by
  let l : Transverse →L[ℝ] ℝ := ContinuousLinearMap.proj i
  apply (gaussianState_quadratic_memLp ε a α β p b y hε ha hα hβ hw hy l).ae_eq
  filter_upwards [gaussianState_profile ε a α β p y b hε ha hα hβ hw hy] with x hx
  change (x.2 i:ℂ)^2*_ = _
  rw [hx]

#print axioms clockAmplitude_smooth
#print axioms quadratic_positions
#print axioms recentered_packet
#print axioms physical_profile
#print axioms gaussianState_profile
#print axioms profile_memLp
#print axioms profile_quadratic_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
