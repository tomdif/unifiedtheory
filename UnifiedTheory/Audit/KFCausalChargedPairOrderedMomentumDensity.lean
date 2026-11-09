/- Exact representatives of the paired state's three ordered momentum
outputs. The common complex clock slope survives directional source
integration and polarization as an unbounded multiplication relation. -/
import UnifiedTheory.Audit.KFCausalChargedPairClockMomentum
import UnifiedTheory.Audit.KFCausalChargedPairOrderedOutputs
import UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalUnboundedMultiplierIntegral
  (relation relation_iff_bounded relation_integral relation_smul)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope clockSlope_continuous source_relation)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalDirectionalGaussianCoefficients
  (sourceCurve sourceBound sourceCurve_continuous sourceCurve_bound)
open KFCausalSourceCircleCoefficients
open KFCausalDirectionalClockMomentum (factorCurve factorCurve_continuous)
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalChargedPairDomain (combine directions)
open KFCausalChargedPairOrderedOutputs (pairedShifted)

theorem relation_combine (w : KFCausalCoupledLongitudinalFlow.Configuration → ℂ)
    (hw : Measurable w) (f g : Fin 4 → Hilbert) (hg : ∀ i, relation w (f i) (g i)) :
    relation w (combine f) (combine g) := by
  apply (relation_iff_bounded w hw _ _).mpr
  have he (i : Fin 4) := (relation_iff_bounded w hw _ _).mp (hg i)
  simp only [combine,map_smul,map_add,map_sub]
  rw [he 0,he 1,he 2,he 3]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem directional_relation (C : ℂ) (p : ℝ) (d : Transverse) (k : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (clockSlope ε a h p)
      (KFCausalDirectionalGaussianDomain.output ε a h hε ha hh C p d k hb v l (index n))
      (KFCausalDirectionalClockMomentum.factor ε a h hε ha hh p d C hb k v l (index n)) := by
  let F : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw (weight k θ) p (sourceCurve d θ) h hb v l (index n)
  let G := factorCurve ε a h hε ha hh p d hb k v l (index n)
  have hF : Continuous F :=
    KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb |p| (sourceBound d)
      (weight k) (fun _ => p) (sourceCurve d) (weight_continuous k) continuous_const
      (sourceCurve_continuous d) (fun θ => (weight_norm k θ).le) (fun _ => le_rfl)
      (sourceCurve_bound d) v l (index n)
  have hG : Continuous G := factorCurve_continuous ε a h hε ha hh p d hb k v l (index n)
  have he : relation (clockSlope ε a h p) (∫ θ, F θ ∂angleMeasure) (∫ θ, G θ ∂angleMeasure) :=
    relation_integral _ (clockSlope_continuous ε a h hε hb p).measurable F G
      ((continuous_angle_memLp F hF).integrable (by norm_num))
      ((continuous_angle_memLp G hG).integrable (by norm_num))
      (Filter.Eventually.of_forall (fun θ =>
        source_relation ε a h hε ha hh hb (weight k θ) p (sourceCurve d θ) v l n))
  exact relation_smul _ (clockSlope_continuous ε a h hε hb p).measurable _ _ he (C*normalization k)

theorem paired_relation (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (clockSlope ε a h 0)
      (KFCausalChargedPairDomain.output ε a h hε ha hh hb v l (index n))
      (KFCausalChargedPairClockMomentum.factor ε a h hε ha hh hb v l (index n)) :=
  relation_combine _ (clockSlope_continuous ε a h hε hb 0).measurable _ _
    (fun i => directional_relation ε a h hε ha hh hb 1 0 (directions i) 2 v l n)

theorem momentum_density (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    KFCausalChargedPairClockMomentum.factor ε a h hε ha hh hb v l (index n) =ᵐ[volume]
      fun x => clockSlope ε a h 0 x*pairedShifted ε a h l n x := by
  filter_upwards [paired_relation ε a h hε ha hh hb v l n,
    KFCausalChargedPairOrderedOutputs.output_coe ε a h hε ha hh hb v l n] with x hm hu
  rw [hm,hu]

include hε ha hh hb in
theorem momentum_density_memLp (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    MemLp (fun x => clockSlope ε a h 0 x*pairedShifted ε a h l n x) 2 volume :=
  (Lp.memLp (KFCausalChargedPairClockMomentum.factor ε a h hε ha hh hb
    KFCausalPhysicalEnergyFactors.modelDirections l (index n))).ae_eq
    (momentum_density ε a h hε ha hh hb KFCausalPhysicalEnergyFactors.modelDirections l n)

#print axioms relation_combine
#print axioms directional_relation
#print axioms paired_relation
#print axioms momentum_density
#print axioms momentum_density_memLp
end
end UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity
