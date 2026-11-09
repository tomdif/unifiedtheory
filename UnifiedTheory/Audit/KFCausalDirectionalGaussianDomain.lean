/- Every real directional power of the centered physical packet belongs
to all eight natural energy-factor domains. The graph witnesses are
constructed by integrating bounded continuous sourced packets. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianCoefficients
import UnifiedTheory.Audit.KFCausalSourcedCurveDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalDirectionalGaussianCoefficients
open KFCausalSourceCircleCoefficients
open KFCausalSourcedCurveDomain (meanFactor meanFactor_graph)
open KFCausalClockFloorCommonDomain
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound clockFunction clockFunction_memLp clockFunction_continuous)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
variable (C : ℂ) (p : ℝ) (d : Transverse) (n : ℕ)

def input : Hilbert :=
  coefficientState α β hα hβ hw C p (clockFunction ε a) (clockFunction_memLp ε a hε ha) d n

def output (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  (C*normalization n) • meanFactor ε a h hε ha hh hb (weight n) (fun _ => p) (sourceCurve d) v l j

theorem input_coe :
    input ε a h hε ha hh C p d n =ᵐ[volume]
      KFCausalDirectionalGaussianStates.profile C p α β (clockFunction ε a) d n :=
  coefficientState_coe α β hα hβ hw C p (clockFunction ε a)
    (clockFunction_memLp ε a hε ha) (clockFunction_continuous ε a) d n

theorem output_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (input ε a h hε ha hh C p d n,output ε a h hε ha hh C p d n hb v l j) ∈
      (energyFactor ε hε h v l j).graph :=
  (energyFactor ε hε h v l j).graph.smul_mem (C*normalization n)
    (meanFactor_graph ε a h hε ha hh hb |p| (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
      (weight_continuous n) continuous_const (sourceCurve_continuous d)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (sourceCurve_bound d) v l j)

theorem input_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    input ε a h hε ha hh C p d n ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph
    (output_graph ε a h hε ha hh C p d n hb v l j)

#print axioms input_coe
#print axioms output_graph
#print axioms input_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain
