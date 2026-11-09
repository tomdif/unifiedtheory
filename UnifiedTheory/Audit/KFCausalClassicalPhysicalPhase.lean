/- Exact continuous coordinate correspondence between the original
configuration/momentum phase space used by quantum characteristic tests and
the paired canonical phase space used by the full classical dynamics. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterFlow
import UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q p q_apply p_apply)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry modeEquiv forward)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (PhaseSpace clockAxis)
open UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents (clockShift)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (positionBasis momentumBasis)

abbrev Paired := KFCausalPairedRotation.Space
abbrev Euclidean := KFCausalEuclideanConfiguration.Space

def flatten (x : Configuration) : Euclidean := WithLp.toLp 2 (Fin.cons x.1 x.2)

theorem split_flatten (x : Configuration) : KFCausalEuclideanConfiguration.split (flatten x) = x := by
  rfl

theorem flatten_split (x : Euclidean) : flatten (KFCausalEuclideanConfiguration.split x) = x := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem flatten_continuous : Continuous flatten := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

def toPaired (x : Configuration) : Paired := modeIsometry (flatten x)
def fromPaired (x : Paired) : Configuration := KFCausalEuclideanConfiguration.split (modeIsometry.symm x)

theorem toPaired_continuous : Continuous toPaired := modeIsometry.continuous.comp flatten_continuous

theorem fromPaired_continuous : Continuous fromPaired := by
  change Continuous (fun x : Paired => ((modeIsometry.symm x) 0,fun i : Fin 5 => (modeIsometry.symm x) i.succ))
  exact ((PiLp.continuous_apply 2 _ 0).comp modeIsometry.symm.continuous).prodMk
    (continuous_pi (fun i => (PiLp.continuous_apply 2 _ i.succ).comp modeIsometry.symm.continuous))

def configurationEquiv : Configuration ≃ₜ Paired where
  toFun := toPaired
  invFun := fromPaired
  left_inv x := by simp only [toPaired,fromPaired,LinearIsometryEquiv.symm_apply_apply,split_flatten]
  right_inv x := by simp only [toPaired,fromPaired,flatten_split,LinearIsometryEquiv.apply_symm_apply]
  continuous_toFun := toPaired_continuous
  continuous_invFun := fromPaired_continuous

def phaseEquiv : PhaseSpace ≃ₜ Phase := configurationEquiv.prodCongr configurationEquiv

theorem paired_clock (x : Configuration) : toPaired x (.inr 0) = x.1 := rfl

def initialEmbedding (τ : ℝ) (x : PhaseSpace) : TimePhase := (τ,phaseEquiv x)

theorem initialEmbedding_continuous (τ : ℝ) : Continuous (initialEmbedding τ) :=
  continuous_const.prodMk phaseEquiv.continuous

theorem initialEmbedding_clock (τ : ℝ) (x : PhaseSpace) :
    q (.inr 0) (initialEmbedding τ x).2 = x.1.1 ∧
      p (.inr 0) (initialEmbedding τ x).2 = x.2.1 := by
  exact ⟨paired_clock x.1,paired_clock x.2⟩

theorem initialEmbedding_axis (τ s : ℝ) :
    initialEmbedding τ (clockAxis s) = (τ,clockShift s 0 (0:Phase)) := by
  apply congrArg (fun z : Phase => (τ,z))
  apply Prod.ext <;> apply PiLp.ext <;> intro i <;> rcases i with i | i <;> fin_cases i <;>
    simp [phaseEquiv,configurationEquiv,toPaired,flatten,modeIsometry,modeEquiv,
      forward,clockAxis,clockShift,positionBasis,momentumBasis,PiLp.basisFun_apply,Fin.cons,Fin.cases]
  all_goals norm_num [Fin.induction,Fin.induction.go]

#print axioms split_flatten
#print axioms flatten_split
#print axioms flatten_continuous
#print axioms toPaired_continuous
#print axioms fromPaired_continuous
#print axioms configurationEquiv
#print axioms phaseEquiv
#print axioms paired_clock
#print axioms initialEmbedding_continuous
#print axioms initialEmbedding_clock
#print axioms initialEmbedding_axis

end
end UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase

