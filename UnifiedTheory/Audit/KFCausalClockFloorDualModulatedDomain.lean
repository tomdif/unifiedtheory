/- Every Fourier modulation of the exact nonvanishing dual Gaussian is
an actual vector of the full interacting averaged form. The witnesses are
clock-preserving displaced physical trial states, with their normalization
removed exactly. No density or operator-core conclusion is assumed here. -/
import UnifiedTheory.Audit.KFCausalChargeDualDisplacement
import UnifiedTheory.Audit.KFCausalClockFloorDualGaussian
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain
import UnifiedTheory.Audit.KFCausalModulatedLpTotality

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDualModulatedDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalChargeDualDisplacement
open KFCausalClockFloorInvariantTrial (trialState trialState_ne_zero)
open KFCausalClockFloorDisplacedStates (rawState state_normalization)
open KFCausalClockFloorDisplacedAveragedDomain (averagedVector averagedVector_embedding)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEnergy
open KFCausalClockFloorDualGaussian (weight weight_memLp weight_coe)
open KFCausalFourierTranslation (phaseAction_coe phase)
open KFCausalEuclideanFourierUniqueness (modulate)

private theorem rescaled_embedding {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (v : X) (n : ℝ) (r : Y) (hn : n ≠ 0)
    (he : T v = n⁻¹ • r) : T ((n : ℂ) • v) = r := by
  rw [map_smul,he,smul_comm,← smul_assoc,Complex.real_smul,← Complex.ofReal_mul,
    inv_mul_cancel₀ hn,Complex.ofReal_one,one_smul]

private theorem phase_state (f : KFCausalEuclideanProductCoordinates.JointHilbert 5 1)
    (w : Joint 5 1 → ℂ) (hw : MemLp w 2) (hf : f =ᵐ[volume] w) (k : Joint 5 1) :
    KFCausalFourierTranslation.phaseAction k f = KFCausalModulatedLpTotality.state w hw k := by
  apply Lp.ext
  filter_upwards [phaseAction_coe k f,hf,KFCausalModulatedLpTotality.state_coe w hw k]
    with x hp hx hs
  rw [hp,hx,hs]
  unfold phase modulate
  rw [real_inner_comm]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ)
local notation "V" => AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g κ t
local notation "J" => embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ t

def formVector (k : Joint 5 1) : V :=
  (‖trialState ε a h hε ha hh‖ : ℂ) •
    averagedVector ε a h hε ha hh hb m g κ t
      (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k)

theorem formVector_embedding (k : Joint 5 1) :
    J (formVector ε a h hε ha hh hb m g κ t k) =
      rawState ε a h hε ha hh (displacementParameter h k) (clockParameter k) := by
  exact rescaled_embedding J
    (averagedVector ε a h hε ha hh hb m g κ t
      (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k))
    ‖trialState ε a h hε ha hh‖ _
    (norm_ne_zero_iff.mpr (trialState_ne_zero ε a h hε ha hh))
    ((averagedVector_embedding ε a h hε ha hh hb m g κ t
      (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k)).trans
      (state_normalization ε a h hε ha hh (displacementParameter h k) (clockParameter k)))

theorem formVector_dual (k : Joint 5 1) :
    dualPhysical (J (formVector ε a h hε ha hh hb m g κ t k)) =
      KFCausalModulatedLpTotality.state (weight ε a h) (weight_memLp ε a h hε ha hh) k := by
  exact (congrArg dualPhysical (formVector_embedding ε a h hε ha hh hb m g κ t k)).trans
    ((dualPhysical_operator h hh k (trialState ε a h hε ha hh)).trans
      (phase_state _ (weight ε a h) (weight_memLp ε a h hε ha hh)
        (weight_coe ε a h hε ha hh) k))

theorem formVector_dual_coe (k : Joint 5 1) :
    dualPhysical (J (formVector ε a h hε ha hh hb m g κ t k)) =ᵐ[volume]
      modulate k (weight ε a h) := by
  rw [formVector_dual]
  exact KFCausalModulatedLpTotality.state_coe (weight ε a h) (weight_memLp ε a h hε ha hh) k

theorem modulated_source_mem_energy_domain (k : Joint 5 1) :
    dualPhysical.symm (KFCausalModulatedLpTotality.state (weight ε a h)
      (weight_memLp ε a h hε ha hh) k) ∈
      (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain := by
  apply (energy_domain ε hε h (hamiltonian_bound ε h hb) hh m g κ t _).mpr
  refine ⟨formVector ε a h hε ha hh hb m g κ t k,?_⟩
  exact dualPhysical.eq_symm_apply.mpr (formVector_dual ε a h hε ha hh hb m g κ t k)

#print axioms formVector_embedding
#print axioms formVector_dual
#print axioms formVector_dual_coe
#print axioms modulated_source_mem_energy_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorDualModulatedDomain
