/- The second kinetic output has an actual pure-clock domain. Its
transverse quadratic polynomial does not change the clock derivative. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondPureClockDomain
import UnifiedTheory.Audit.KFCausalGaussianKineticSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalKineticSecondPureDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRadialMultipliers
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalRelativeGaussianDifferential (profile position exponent)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalDirectionalGaussianStates (linearForm)
open KFCausalGaussianSecondMomentum (direction second secondOutput)
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

def polynomial (α β : ℝ) (v q : Transverse) : ℂ :=
  (linearForm (direction α β v) q:ℂ)^2+(linearForm (direction α β v) v:ℂ)

theorem polynomial_controlled (α β : ℝ) (v : Transverse) :
    Controlled (fun x => polynomial α β v x.2) := by
  have hl : Controlled (fun x : Configuration => (linearForm (direction α β v) x.2:ℂ)) := by
    simp only [linearForm,Complex.ofReal_sum,Complex.ofReal_mul]
    exact controlled_sum Finset.univ _ (fun i _ =>
      controlled_mul _ _ (controlled_const (direction α β v i:ℂ)) (controlled_coordinate i))
  exact controlled_add _ _ (controlled_pow _ hl 2) (controlled_const _)

theorem polynomial_differentiable (α β : ℝ) (v : Transverse) :
    Differentiable ℝ (fun x : Configuration => polynomial α β v x.2) := by
  have hl : Differentiable ℝ (fun x : Configuration => linearForm (direction α β v) x.2) := by
    unfold linearForm
    apply Differentiable.fun_sum
    intro i _
    fun_prop
  exact ((Complex.ofRealCLM.differentiable.comp hl).pow 2).add_const _

theorem base_profile (ε a α β : ℝ) (hε : 0 < ε) (x : Configuration) :
    profile (clockAmplitude ε a 0 0) (scale ε 0) α β 0 x =
      dampedClockFunction ε a x.1*KFCausalClockFloorShearBounds.physicalGaussian α β x.2 := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hr : KFCausalClockFloorRelativeShift.relative ε 0 x.1 = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa using KFCausalClockFloorRelativeShift.relative_bound ε 0 x.1 hε hy)
      (norm_nonneg _))
  have hs : scale ε 0 x.1 = 1 := by
    simp [scale,KFCausalClockFloorShearBounds.complexScale,hr]
  have ha : clockAmplitude ε a 0 0 x.1 = dampedClockFunction ε a x.1 := by
    unfold clockAmplitude dampedClockFunction
    rw [KFCausalClockFloorChargeTrialBridge.clockFunction_factor ε a x.1 hε]
    have hn : (Real.sqrt (Real.exp x.1+ε):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,zero_mul,
      Complex.exp_zero,mul_one,KFCausalClockFloorRelativeShift.argument,add_zero]
    field_simp
  have hp (i : Fin 5) : position (1:ℂ) x.2 i = (x.2 i:ℂ) := by
    by_cases hi : i=4 <;> simp [position,hi]
  rw [profile,ha,hs]
  congr 1
  simp only [exponent,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_sub,hp,
    KFCausalClockFloorShearBounds.physicalGaussian,
    KFCausalPhysicalGaussianMoments.widths,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  congr 1
  push_cast
  ring

theorem second_profile (ε a α β : ℝ) (hε : 0 < ε) (v : Transverse) (x : Configuration) :
    second α β (dampedClockFunction ε a) v x =
      polynomial α β v x.2*profile (clockAmplitude ε a 0 0) (scale ε 0) α β 0 x := by
  rw [base_profile ε a α β hε]
  unfold second polynomial
  ring

theorem second_differential (ε a α β : ℝ) (hε : 0 < ε) (v : Transverse) (x : Configuration) :
    differential ε (second α β (dampedClockFunction ε a) v) x =
      polynomial α β v x.2*differential ε
        (profile (clockAmplitude ε a 0 0) (scale ε 0) α β 0) x := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  let F := profile (clockAmplitude ε a 0 0) (scale ε 0) α β 0
  have hs := KFCausalRelativeGaussianDifferential.profile_smooth _ _
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a 0 0 hε hy)
    (KFCausalClockFloorRelativeShift.scale_smooth ε 0 hε hy) α β 0
  have hP := polynomial_differentiable α β v
  have hp := ((hP.mul (hs.differentiable (by norm_num))) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have hF := (hs.differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => F (s,x.2)) (clockDerivative F x) x.1 at hF
  change HasDerivAt (fun s => polynomial α β v x.2*F (s,x.2))
    (clockDerivative (fun x => polynomial α β v x.2*F x) x) x.1 at hp
  have he : clockDerivative (fun x => polynomial α β v x.2*F x) x = polynomial α β v x.2*clockDerivative F x :=
    hp.unique (hF.const_mul _)
  rw [funext (second_profile ε a α β hε v)]
  unfold differential
  rw [he]
  ring

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (v : Transverse)
include hw hh

theorem second_domain :
    secondOutput α β hα hβ (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) h v ∈
      (pureMomentum ε hε h).domain := by
  apply (pureMomentum ε hε h).domain.smul_mem
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hd : MemLp (differential ε (second α β (dampedClockFunction ε a) v)) 2 volume := by
    rw [funext (second_differential ε a α β hε v)]
    exact KFCausalMixedFieldPureClockDomain.weightedGaussian_differential_memLp ε a α β 0 0 0 hε ha hα hβ hw hy
      _ (polynomial_controlled α β v)
  apply KFCausalClockFloorPureClockDifferential.differential_domain ε hε h hh _ _ hd
  rw [funext (second_profile ε a α β hε v)]
  have hP := polynomial_differentiable α β v
  exact hP.mul ((KFCausalRelativeGaussianDifferential.profile_smooth _ _
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a 0 0 hε hy)
    (KFCausalClockFloorRelativeShift.scale_smooth ε 0 hε hy) α β 0).differentiable (by norm_num))

theorem square_domain :
    KFCausalGaussianKineticSquare.squareOutput ε a α β hε ha hα hβ h v ∈ (pureMomentum ε hε h).domain :=
  KFCausalClockFloorPureClockInverseHalf.inverse_momentum_domain ε hε h hh _
    (second_domain ε a α β hε ha hα hβ hw h hh v)

#print axioms polynomial_controlled
#print axioms polynomial_differentiable
#print axioms base_profile
#print axioms second_profile
#print axioms second_differential
#print axioms second_domain
#print axioms square_domain
end
end UnifiedTheory.Audit.KFCausalKineticSecondPureDomain
