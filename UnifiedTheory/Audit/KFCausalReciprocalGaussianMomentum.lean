/- Both the reciprocal Gaussian and its actual pure-clock momentum have
all eight natural factor graphs. The width range is w >= 1. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianDomain
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalSqueezeEnergy (factorScale factor_graph)
open KFCausalReciprocalGaussianDomain
open KFCausalClockFloorPureClockMomentum (pureMomentum graph_fourier)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

theorem pure_graph_transport (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (t : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    (transport t f,transport t g) ∈ (pureMomentum ε hε h).graph := by
  rw [graph_fourier ε hε h hh] at hfg ⊢
  rw [← KFCausalReciprocalSqueezeClockCommutation.pure_inverse_coordinates,
    ← KFCausalReciprocalSqueezeClockCommutation.pure_inverse_coordinates]
  filter_upwards [KFCausalReciprocalSqueezeFourier.fourier_coe t
      ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm f),
    KFCausalReciprocalSqueezeFourier.fourier_coe t
      ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm g),
    (KFCausalFourierLinearChange.dual_quasiMeasurePreserving
      (KFCausalReciprocalSqueezeEuclidean.linearFlow t)).ae hfg] with k hf hg he
  rw [hg,hf,he]
  simp only [KFCausalClockFloorFourierMultiplier.symbol,KFCausalReciprocalSqueezeEuclidean.dual_clock]
  ring

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "ψ" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "b" => (Real.exp (-t/2):ℂ)

theorem state_eq_transport : ψ = b • transport (-t) (baseState ε a h hε ha hh t ht) := by
  have he : Real.exp (2*t) = w := by
    rw [show 2*t=Real.log w by ring,Real.exp_log (by linarith)]
  simpa only [he] using state_transport ε a h hε ha hh t ht

def momentum : Hilbert := b • transport (-t)
  (KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hbw 1 0 0 h)

theorem momentum_graph : (ψ,momentum ε a h w hε ha hh hw) ∈ (pureMomentum ε hε h).graph := by
  rw [state_eq_transport ε a h w hε ha hh hw]
  exact (pureMomentum ε hε h).graph.smul_mem b
    (pure_graph_transport ε hε h hh (-t) _ _
      (KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hbw 1 0 0 h hh))

theorem momentum_zeroSector : momentum ε a h w hε ha hh hw ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h w hε ha hh hw)
    (KFCausalReciprocalGaussianCharge.state_zeroSector ε a h w hε ha hh (by linarith))

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (j : Fin 8) : Hilbert :=
  b • (factorScale (-t) j • transport (-t)
    (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hbw
      1 0 0 h hb modelDirections pointField j))

def momentumOutput (j : Fin 8) : Hilbert :=
  b • (factorScale (-t) j • transport (-t)
    (KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hbw
      1 0 0 h hb modelDirections pointField j))

theorem output_graph (j : Fin 8) :
    (ψ,output ε a h w hε ha hh hw hb j) ∈ (energyFactor ε hε h modelDirections pointField j).graph := by
  rw [state_eq_transport ε a h w hε ha hh hw]
  exact (energyFactor ε hε h modelDirections pointField j).graph.smul_mem b
    (factor_graph ε hε h (-t) j _ _
      (KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hbw
        1 0 0 h hb modelDirections pointField j))

theorem momentumOutput_graph (j : Fin 8) :
    (momentum ε a h w hε ha hh hw,momentumOutput ε a h w hε ha hh hw hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.smul_mem b
    (factor_graph ε hε h (-t) j _ _
      (KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hbw
        1 0 0 h hh hb modelDirections pointField j))

include hb in
theorem momentum_commonEnergyDomain :
    momentum ε a h w hε ha hh hw ∈ commonEnergyDomain ε hε h modelDirections pointField :=
  (commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr
    (fun j => LinearPMap.mem_domain_of_mem_graph
      (momentumOutput_graph ε a h w hε ha hh hw hb j))

#print axioms pure_graph_transport
#print axioms state_eq_transport
#print axioms momentum_graph
#print axioms momentum_zeroSector
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms momentum_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum
