/- Every directional polynomial Gaussian has an actual pure-clock momentum
whose eight energy-factor outputs are constructed by closed graph
integration. The real transverse direction and polynomial degree are
arbitrary, so charged directions are included. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain
import UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalDirectionalClockMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalDirectionalGaussianCoefficients
  (sourceCurve sourceBound sourceCurve_continuous sourceCurve_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain (input)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
variable (p : ℝ) (d : Transverse)

def pureCurve (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (sourceCurve d θ) h

def factorCurve (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (sourceCurve d θ) h hb v l j

theorem pureCurve_continuous (n : ℕ) :
    Continuous (pureCurve ε a h hε ha hh p d n) := by
  have hc := KFCausalSourcedCurveDomain.state_continuous ε a h hε ha hh
    (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
    (weight_continuous n) continuous_const (sourceCurve_continuous d)
    (fun θ => (weight_norm n θ).le) (sourceCurve_bound d)
  have hd := KFCausalSourcedCurveDomain.state_continuous ε (a/2) h hε (by positivity) hh
    (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
    (weight_continuous n) continuous_const (sourceCurve_continuous d)
    (fun θ => (weight_norm n θ).le) (sourceCurve_bound d)
  exact KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha p _ _ hc hd

theorem factorCurve_continuous (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (factorCurve ε a h hε ha hh p d hb n v l j) := by
  have hc := KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb
    |p| (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
    (weight_continuous n) continuous_const (sourceCurve_continuous d)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (sourceCurve_bound d) v l j
  have hd := KFCausalSourcedCurveDomain.factor_continuous ε (a/2) h hε (by positivity) hh hb
    |p| (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
    (weight_continuous n) continuous_const (sourceCurve_continuous d)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (sourceCurve_bound d) v l j
  unfold factorCurve KFCausalSourcedMomentumFactors.factorOutput
  by_cases hj : j.val < 5
  · simp only [hj,ite_true]
    exact KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha p _ _ hc hd
  · simp only [hj,ite_false]
    exact KFCausalCoherentMomentumOutputReduction.reducedOutput_continuous ε a h hε ha hb p _ _ hc hd

variable (C : ℂ)

def momentum (n : ℕ) : Hilbert :=
  (C*normalization n) • (∫ θ, pureCurve ε a h hε ha hh p d n θ ∂angleMeasure)

def factor (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  (C*normalization n) • (∫ θ, factorCurve ε a h hε ha hh p d hb n v l j θ ∂angleMeasure)

theorem momentum_graph (n : ℕ) :
    (input ε a h hε ha hh C p d n,momentum ε a h hε ha hh p d C n) ∈
      (pureMomentum ε hε h).graph := by
  exact (pureMomentum ε hε h).graph.smul_mem (C*normalization n)
    (integral_closed_graph _ (pure_closed ε hε h hh) _ _
    (KFCausalSourcedCurveDomain.state_continuous ε a h hε ha hh
      (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
      (weight_continuous n) continuous_const (sourceCurve_continuous d)
      (fun θ => (weight_norm n θ).le) (sourceCurve_bound d))
    (pureCurve_continuous ε a h hε ha hh p d n)
    (fun θ => KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (sourceCurve d θ) h hh))

theorem factor_graph (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a h hε ha hh p d C n,
      factor ε a h hε ha hh p d C hb n v l j) ∈ (energyFactor ε hε h v l j).graph := by
  exact (energyFactor ε hε h v l j).graph.smul_mem (C*normalization n)
    (KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε v l
    (pureCurve ε a h hε ha hh p d n) (factorCurve ε a h hε ha hh p d hb n v l)
    (pureCurve_continuous ε a h hε ha hh p d n)
    (factorCurve_continuous ε a h hε ha hh p d hb n v l)
    (fun θ j => KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (sourceCurve d θ) h hh hb v l j) j)

theorem momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    momentum ε a h hε ha hh p d C n ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr (fun j => LinearPMap.mem_domain_of_mem_graph
    (factor_graph ε a h hε ha hh p d C hb n v l j))

theorem actual_momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (k : Hilbert)
    (hk : (input ε a h hε ha hh C p d n,k) ∈ (pureMomentum ε hε h).graph) :
    k ∈ commonEnergyDomain ε hε h v l := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hk
    (momentum_graph ε a h hε ha hh p d C n) rfl
  dsimp only at he
  rw [he]
  exact momentum_commonEnergyDomain ε a h hε ha hh p d C hb n v l

#print axioms pureCurve_continuous
#print axioms factorCurve_continuous
#print axioms momentum_graph
#print axioms factor_graph
#print axioms momentum_commonEnergyDomain
#print axioms actual_momentum_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalDirectionalClockMomentum
