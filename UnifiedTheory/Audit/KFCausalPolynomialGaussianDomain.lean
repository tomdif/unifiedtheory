/- Arbitrary physical coordinate powers, and finite complex polynomials,
of sourced Gaussian packets lie in all eight natural ordered energy
domains. This is a domain theorem, not a signed response estimate. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
import UnifiedTheory.Audit.KFCausalSourcedCurveDomain
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalSourcedCurveDomain (meanFactor meanFactor_graph meanState)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound clockFunction clockFunction_memLp clockFunction_continuous)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
variable (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)

def powerInput (n : ℕ) : Hilbert :=
  polynomialState α β hα hβ hw C p b (clockFunction ε a) (clockFunction_memLp ε a hε ha) i n

def powerOutput (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  (C*normalization n) • meanFactor ε a h hε ha hh hb (weight n) (fun _ => p) (circleSource b i) v l j

theorem powerInput_coe (n : ℕ) :
    powerInput ε a h hε ha hh C p b i n =ᵐ[volume]
      polynomialProfile C p α β b (clockFunction ε a) i n :=
  polynomialState_coe α β hα hβ hw C p b (clockFunction ε a) (clockFunction_memLp ε a hε ha) i n

theorem powerInput_coefficient (n : ℕ) :
    powerInput ε a h hε ha hh C p b i n =
      (C*normalization n) • meanState ε a h hε ha hh (weight n) (fun _ => p) (circleSource b i) :=
  (coefficient_eq α β hα hβ hw C p b (clockFunction ε a)
    (clockFunction_memLp ε a hε ha) (clockFunction_continuous ε a) i n).symm

theorem powerOutput_graph (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (powerInput ε a h hε ha hh C p b i n,powerOutput ε a h hε ha hh C p b i hb n v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  rw [powerInput_coefficient]
  exact (energyFactor ε hε h v l j).graph.smul_mem (C*normalization n)
    (meanFactor_graph ε a h hε ha hh hb |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j)

theorem powerInput_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    powerInput ε a h hε ha hh C p b i n ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph (powerOutput_graph ε a h hε ha hh C p b i hb n v l j)

def input (P : Polynomial ℂ) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerInput ε a h hε ha hh C p b i n

def output (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerOutput ε a h hε ha hh C p b i hb n v l j

theorem output_graph (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (input ε a h hε ha hh C p b i P,output ε a h hε ha hh C p b i hb P v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hs := (energyFactor ε hε h v l j).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (energyFactor ε hε h v l j).graph.smul_mem (P.coeff n)
      (powerOutput_graph ε a h hε ha hh C p b i hb n v l j))
  simpa only [input,output,Prod.smul_mk,← prod_mk_sum] using hs

theorem input_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    input ε a h hε ha hh C p b i P ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph (output_graph ε a h hε ha hh C p b i hb P v l j)

theorem input_coe (P : Polynomial ℂ) :
    input ε a h hε ha hh C p b i P =ᵐ[volume] fun x : Configuration =>
      P.eval (x.2 i:ℂ)*KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a) x := by
  have hs (s : Finset ℕ) :
      (∑ n ∈ s, P.coeff n • powerInput ε a h hε ha hh C p b i n : Hilbert) =ᵐ[volume]
        fun x : Configuration => (∑ n ∈ s, P.coeff n*(x.2 i:ℂ)^n)*
          KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a) x := by
    induction s using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 volume : (0:Hilbert) =ᵐ[volume] 0)
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      filter_upwards [Lp.coeFn_add (P.coeff n • powerInput ε a h hε ha hh C p b i n)
        (∑ k ∈ s, P.coeff k • powerInput ε a h hε ha hh C p b i k),
        Lp.coeFn_smul (P.coeff n) (powerInput ε a h hε ha hh C p b i n),
        powerInput_coe ε a h hε ha hh C p b i n,ih] with x hx hy hz ht
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx hy
      rw [hx,hy,hz,ht]
      unfold polynomialProfile
      ring
  simpa only [input,Polynomial.eval_eq_sum,Polynomial.sum] using hs P.support

#print axioms powerInput_coe
#print axioms powerInput_coefficient
#print axioms powerOutput_graph
#print axioms powerInput_commonEnergyDomain
#print axioms output_graph
#print axioms input_commonEnergyDomain
#print axioms input_coe
end
end UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain
