/- Polynomial Gaussian packets and their actual pure-clock momenta
belong to every natural energy-factor domain. Both momentum and factor
outputs are constructed by closed graph integration, not assumed. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain
import UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (input powerInput powerInput_coefficient)
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
variable (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)

def pureCurve (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (circleSource b i θ) h

def factorCurve (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (circleSource b i θ) h hb v l j

theorem pureCurve_continuous (n : ℕ) :
    Continuous (pureCurve ε a h hε ha hh p b i n) := by
  have hc := KFCausalSourcedCurveDomain.state_continuous ε a h hε ha hh
    (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i)
  have hd := KFCausalSourcedCurveDomain.state_continuous ε (a/2) h hε (by positivity) hh
    (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i)
  exact KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha p _ _ hc hd

theorem factorCurve_continuous (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (factorCurve ε a h hε ha hh p b i hb n v l j) := by
  have hc := KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb
    |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j
  have hd := KFCausalSourcedCurveDomain.factor_continuous ε (a/2) h hε (by positivity) hh hb
    |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j
  unfold factorCurve KFCausalSourcedMomentumFactors.factorOutput
  by_cases hj : j.val < 5
  · simp only [hj,ite_true]
    exact KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha p _ _ hc hd
  · simp only [hj,ite_false]
    exact KFCausalCoherentMomentumOutputReduction.reducedOutput_continuous ε a h hε ha hb p _ _ hc hd

variable (C : ℂ)

def powerMomentum (n : ℕ) : Hilbert :=
  (C*normalization n) • (∫ θ, pureCurve ε a h hε ha hh p b i n θ ∂angleMeasure)

def powerMomentumFactor (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  (C*normalization n) • (∫ θ, factorCurve ε a h hε ha hh p b i hb n v l j θ ∂angleMeasure)

theorem powerMomentum_graph (n : ℕ) :
    (powerInput ε a h hε ha hh C p b i n,powerMomentum ε a h hε ha hh p b i C n) ∈
      (pureMomentum ε hε h).graph := by
  rw [powerInput_coefficient]
  exact (pureMomentum ε hε h).graph.smul_mem (C*normalization n)
    (integral_closed_graph _ (pure_closed ε hε h hh) _ _
    (KFCausalSourcedCurveDomain.state_continuous ε a h hε ha hh
      (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i))
    (pureCurve_continuous ε a h hε ha hh p b i n)
    (fun θ => KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh))

theorem powerMomentumFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (powerMomentum ε a h hε ha hh p b i C n,
      powerMomentumFactor ε a h hε ha hh p b i C hb n v l j) ∈ (energyFactor ε hε h v l j).graph := by
  exact (energyFactor ε hε h v l j).graph.smul_mem (C*normalization n)
    (KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε v l
    (pureCurve ε a h hε ha hh p b i n) (factorCurve ε a h hε ha hh p b i hb n v l)
    (pureCurve_continuous ε a h hε ha hh p b i n)
    (factorCurve_continuous ε a h hε ha hh p b i hb n v l)
    (fun θ j => KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh hb v l j) j)

def momentum (P : Polynomial ℂ) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerMomentum ε a h hε ha hh p b i C n

def momentumFactor (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerMomentumFactor ε a h hε ha hh p b i C hb n v l j

theorem momentum_graph (P : Polynomial ℂ) :
    (input ε a h hε ha hh C p b i P,momentum ε a h hε ha hh p b i C P) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (pureMomentum ε hε h).graph.smul_mem (P.coeff n)
      (powerMomentum_graph ε a h hε ha hh p b i C n))
  simpa only [input,momentum,Prod.smul_mk,← prod_mk_sum] using hs

theorem momentumFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a h hε ha hh p b i C P,momentumFactor ε a h hε ha hh p b i C hb P v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hs := (energyFactor ε hε h v l j).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (energyFactor ε hε h v l j).graph.smul_mem (P.coeff n)
      (powerMomentumFactor_graph ε a h hε ha hh p b i C hb n v l j))
  simpa only [momentum,momentumFactor,Prod.smul_mk,← prod_mk_sum] using hs

theorem momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    momentum ε a h hε ha hh p b i C P ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr (fun j => LinearPMap.mem_domain_of_mem_graph
    (momentumFactor_graph ε a h hε ha hh p b i C hb P v l j))

theorem actual_momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (k : Hilbert)
    (hk : (input ε a h hε ha hh C p b i P,k) ∈ (pureMomentum ε hε h).graph) :
    k ∈ commonEnergyDomain ε hε h v l := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hk (momentum_graph ε a h hε ha hh p b i C P) rfl
  dsimp only at he
  rw [he]
  exact momentum_commonEnergyDomain ε a h hε ha hh p b i C hb P v l

#print axioms pureCurve_continuous
#print axioms factorCurve_continuous
#print axioms powerMomentum_graph
#print axioms powerMomentumFactor_graph
#print axioms momentum_graph
#print axioms momentumFactor_graph
#print axioms momentum_commonEnergyDomain
#print axioms actual_momentum_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
