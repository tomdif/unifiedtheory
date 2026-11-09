/- Polynomial Gaussian packets and their actual pure-clock momenta
belong to every natural energy-factor domain. Both momentum and factor
outputs are constructed by closed graph integration, not assumed. -/
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain
import UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain (input powerInput powerInput_coefficient)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0)
variable (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)

def pureCurve (n : ℕ) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (circleSource b i θ) h

def factorCurve (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) (θ : ℝ) : Hilbert :=
  KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw
    (weight n θ) p (circleSource b i θ) h hb v l j

theorem pureCurve_continuous (n : ℕ) :
    Continuous (pureCurve ε a α β hε ha hα hβ hw h p b i n) := by
  have hc := KFCausalVariableWidthSourceCurves.state_continuous ε a α β hε ha hα hβ hw
    (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i)
  have hd := KFCausalVariableWidthSourceCurves.state_continuous ε (a/2) α β hε (by positivity) hα hβ hw
    (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i)
  exact KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha p _ _ hc hd

theorem factorCurve_continuous (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (factorCurve ε a α β hε ha hα hβ hw h p b i hb n v l j) := by
  have hc := KFCausalVariableWidthSourceCurves.factor_continuous ε a α β hε ha hα hβ hw h hb
    |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j
  have hd := KFCausalVariableWidthSourceCurves.factor_continuous ε (a/2) α β hε (by positivity) hα hβ hw h hb
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
  (C*normalization n) • (∫ θ, pureCurve ε a α β hε ha hα hβ hw h p b i n θ ∂angleMeasure)

def powerMomentumFactor (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  (C*normalization n) • (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb n v l j θ ∂angleMeasure)

include hh in
theorem powerMomentum_graph (n : ℕ) :
    (powerInput ε a α β hε ha hα hβ hw C p b i n,powerMomentum ε a α β hε ha hα hβ hw h p b i C n) ∈
      (pureMomentum ε hε h).graph := by
  rw [powerInput_coefficient]
  exact (pureMomentum ε hε h).graph.smul_mem (C*normalization n)
    (integral_closed_graph _ (pure_closed ε hε h hh) _ _
    (KFCausalVariableWidthSourceCurves.state_continuous ε a α β hε ha hα hβ hw
      (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i))
    (pureCurve_continuous ε a α β hε ha hα hβ hw h p b i n)
    (fun θ => KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh))

include hh in
theorem powerMomentumFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (powerMomentum ε a α β hε ha hα hβ hw h p b i C n,
      powerMomentumFactor ε a α β hε ha hα hβ hw h p b i C hb n v l j) ∈ (energyFactor ε hε h v l j).graph := by
  exact (energyFactor ε hε h v l j).graph.smul_mem (C*normalization n)
    (KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε v l
    (pureCurve ε a α β hε ha hα hβ hw h p b i n) (factorCurve ε a α β hε ha hα hβ hw h p b i hb n v l)
    (pureCurve_continuous ε a α β hε ha hα hβ hw h p b i n)
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb n v l)
    (fun θ j => KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh hb v l j) j)

def momentum (P : Polynomial ℂ) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerMomentum ε a α β hε ha hα hβ hw h p b i C n

def momentumFactor (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerMomentumFactor ε a α β hε ha hα hβ hw h p b i C hb n v l j

include hh in
theorem momentum_graph (P : Polynomial ℂ) :
    (input ε a α β hε ha hα hβ hw C p b i P,momentum ε a α β hε ha hα hβ hw h p b i C P) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (pureMomentum ε hε h).graph.smul_mem (P.coeff n)
      (powerMomentum_graph ε a α β hε ha hα hβ hw h hh p b i C n))
  simpa only [input,momentum,Prod.smul_mk,← prod_mk_sum] using hs

include hh in
theorem momentumFactor_graph (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a α β hε ha hα hβ hw h p b i C P,momentumFactor ε a α β hε ha hα hβ hw h p b i C hb P v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hs := (energyFactor ε hε h v l j).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (energyFactor ε hε h v l j).graph.smul_mem (P.coeff n)
      (powerMomentumFactor_graph ε a α β hε ha hα hβ hw h hh p b i C hb n v l j))
  simpa only [momentum,momentumFactor,Prod.smul_mk,← prod_mk_sum] using hs

include hh in
theorem momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    momentum ε a α β hε ha hα hβ hw h p b i C P ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr (fun j => LinearPMap.mem_domain_of_mem_graph
    (momentumFactor_graph ε a α β hε ha hα hβ hw h hh p b i C hb P v l j))

include hh in
theorem actual_momentum_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (k : Hilbert)
    (hk : (input ε a α β hε ha hα hβ hw C p b i P,k) ∈ (pureMomentum ε hε h).graph) :
    k ∈ commonEnergyDomain ε hε h v l := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hk (momentum_graph ε a α β hε ha hα hβ hw h hh p b i C P) rfl
  dsimp only at he
  rw [he]
  exact momentum_commonEnergyDomain ε a α β hε ha hα hβ hw h hh p b i C hb P v l

#print axioms pureCurve_continuous
#print axioms factorCurve_continuous
#print axioms powerMomentum_graph
#print axioms powerMomentumFactor_graph
#print axioms momentum_graph
#print axioms momentumFactor_graph
#print axioms momentum_commonEnergyDomain
#print axioms actual_momentum_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum
