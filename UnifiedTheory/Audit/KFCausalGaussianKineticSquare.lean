/- Second kinetic actions of physical Gaussian packets, with all four
physical directions allowed. This proves actual reverse-factor graphs. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondMomentum
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
import UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalGaussianKineticSquare
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorSourcedClockMomentum (state dampedState dampedState_coe dampedState_eq_inverseAction)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorKineticSquare (square square_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α)
local notation "g" => dampedClockFunction ε a
local notation "hg" => dampedClockFunction_memLp ε a hε ha
local notation "S" => state ε a α β hε ha hα hβ hw 1 0 0

theorem damped_eq :
    inverseL ε hε S = KFCausalGaussianSecondMomentum.state α β hα hβ g hg := by
  change KFCausalClockFloorClockHalf.inverseAction ε hε S = _
  rw [← dampedState_eq_inverseAction ε a α β hε ha hα hβ hw 1 0 0]
  apply Lp.ext
  filter_upwards [dampedState_coe ε a α β hε ha hα hβ hw 1 0 0,
    (KFCausalGaussianSecondMomentum.profile_memLp α β hα hβ g hg).coeFn_toLp] with x hx hy
  change KFCausalGaussianSecondMomentum.state α β hα hβ g hg x =
    KFCausalGaussianSecondMomentum.profile α β g x at hy
  rw [hx,hy]
  simp only [KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,one_mul,KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul,KFCausalGaussianSecondMomentum.profile]

def squareOutput (h : ℝ) (v : Transverse) : Hilbert :=
  inverseL ε hε (KFCausalGaussianSecondMomentum.secondOutput α β hα hβ g hg h v)

theorem squareOutput_graph (h : ℝ) (v : Transverse) :
    (S,squareOutput ε a α β hε ha hα hβ h v) ∈ (square ε h v).graph := by
  apply (square_graph ε hε h v S _).mpr
  refine ⟨_,_,?_,KFCausalGaussianSecondMomentum.second_graph α β hα hβ g hg h v,rfl⟩
  rw [damped_eq ε a α β hε ha hα hβ hw]
  exact KFCausalGaussianSecondMomentum.first_graph α β hα hβ g hg h v

theorem state_square_domain (h : ℝ) (v : Transverse) : S ∈ (square ε h v).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (squareOutput_graph ε a α β hε ha hα hβ hw h v)

#print axioms damped_eq
#print axioms squareOutput_graph
#print axioms state_square_domain
end
end UnifiedTheory.Audit.KFCausalGaussianKineticSquare
