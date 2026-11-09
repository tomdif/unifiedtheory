/- Doubled vacuum outputs on the original physical packet and its
actual pure-clock momentum. Only the exponential parameter is doubled;
charged widths, neutral widths and the physical momentum are fixed. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumParameter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralDoubleVacuum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalReciprocalNeutralPackets (state momentum)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalGaussianVacuumSquare (double_strip)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hb : |h| ≤ Real.pi*ε/3)
local notation "hh₂" => mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hh
local notation "hb₂" => double_strip ε h hb
local notation "S" => state ε a h w hε ha hh hw C p b P
local notation "B" => momentum ε a h w hε ha hh hw C p b P

def output : Hilbert :=
  KFCausalReciprocalNeutralVacuumParameter.output ε a h w hε ha hh hw C p b P (2*h) hb₂

def momentumOutput : Hilbert := (1/2:ℂ) •
  KFCausalReciprocalNeutralVacuumParameter.momentumOutput ε a h w hε ha hh hw C p b P (2*h) hb₂

theorem momentum_scaling :
    KFCausalReciprocalNeutralVacuumParameter.momentum ε a h w hε ha hh hw C p b P (2*h) = (2:ℂ) • B :=
  (pureMomentum ε hε (2*h)).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralVacuumParameter.momentum_graph ε a h w hε ha hh hw C p b P (2*h) hh₂)
    (KFCausalVacuumParameterRescale.pure_graph_scale ε hε h 2 S B
      (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b P)) rfl

theorem output_graph : (S,output ε a h w hε ha hh hw C p b P hb) ∈
    (orderedExponential ε hε (2*h)).graph :=
  KFCausalReciprocalNeutralVacuumParameter.output_graph ε a h w hε ha hh hw C p b P (2*h) hb₂

theorem momentumOutput_graph : (B,momentumOutput ε a h w hε ha hh hw C p b P hb) ∈
    (orderedExponential ε hε (2*h)).graph := by
  have hg := (orderedExponential ε hε (2*h)).graph.smul_mem (1/2:ℂ)
    (KFCausalReciprocalNeutralVacuumParameter.momentumOutput_graph ε a h w hε ha hh hw C p b P (2*h) hh₂ hb₂)
  rw [momentum_scaling,Prod.smul_mk,smul_smul,show (1/2:ℂ)*2=1 by norm_num,one_smul] at hg
  exact hg

theorem output_coe : output ε a h w hε ha hh hw C p b P hb =ᵐ[volume]
    shiftedProfile ε a (groundWidth h) (neutralWidth h) (2*h) w C p b P :=
  KFCausalReciprocalNeutralVacuumParameter.output_coe ε a h w hε ha hh hw C p b P (2*h) hb₂

theorem momentumOutput_coe : momentumOutput ε a h w hε ha hh hw C p b P hb =ᵐ[volume]
    fun x => (1/2:ℂ)*clockSlope ε a (2*h) p x*
      shiftedProfile ε a (groundWidth h) (neutralWidth h) (2*h) w C p b P x := by
  filter_upwards [Lp.coeFn_smul (1/2:ℂ)
    (KFCausalReciprocalNeutralVacuumParameter.momentumOutput ε a h w hε ha hh hw C p b P (2*h) hb₂),
    KFCausalReciprocalNeutralVacuumParameter.momentumOutput_coe ε a h w hε ha hh hw C p b P (2*h) hh₂ hb₂] with x hs hx
  change ((1/2:ℂ) • KFCausalReciprocalNeutralVacuumParameter.momentumOutput ε a h w hε ha hh hw C p b P (2*h) hb₂) x = _
  rw [hs,Pi.smul_apply,smul_eq_mul,hx,mul_assoc]

#print axioms momentum_scaling
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms output_coe
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralDoubleVacuum
