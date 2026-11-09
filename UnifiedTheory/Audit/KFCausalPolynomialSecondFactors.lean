/- All eight actual reverse-factor graphs for sourced polynomial
packets. Source-circle integration gives each monomial and finite
linearity gives arbitrary complex polynomials, without degree bounds. -/
import UnifiedTheory.Audit.KFCausalCoherentSecondCurves
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalPolynomialSecondFactors
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients
open KFCausalVariableWidthPolynomialDomain (input output powerOutput output_graph)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "hb₀" => original_strip ε h hε hb

def powerSecond (n : ℕ) (j : Fin 8) : Hilbert := (C*normalization n) •
  KFCausalCoherentSecondCurves.meanSecond ε a α β hε ha hα hβ hw h hb
    (weight n) (fun _ => p) (circleSource b i) j

theorem power_reverse_graph (n : ℕ) (j : Fin 8) :
    (powerOutput ε a α β hε ha hα hβ hw h C p b i hb₀ n modelDirections pointField j,
      powerSecond ε a α β hε ha hα hβ hw h hb C p b i n j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph :=
  (reverseFactor ε hε h modelDirections pointField j).graph.smul_mem (C*normalization n)
    (KFCausalCoherentSecondCurves.mean_reverse_graph ε a α β hε ha hα hβ hw h hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) j)

def second (P : Polynomial ℂ) (j : Fin 8) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerSecond ε a α β hε ha hα hβ hw h hb C p b i n j

theorem reverse_graph (P : Polynomial ℂ) (j : Fin 8) :
    (output ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField j,
      second ε a α β hε ha hα hβ hw h hb C p b i P j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (reverseFactor ε hε h modelDirections pointField j).graph.smul_mem (P.coeff n)
      (power_reverse_graph ε a α β hε ha hα hβ hw h hb C p b i n j))
  simpa only [output,second,Prod.smul_mk,← prod_mk_sum] using hs

theorem second_graph (P : Polynomial ℂ) (j : Fin 8) :
    (input ε a α β hε ha hα hβ hw C p b i P,
      second ε a α β hε ha hα hβ hw h hb C p b i P j) ∈
        (composition (reverseFactor ε hε h modelDirections pointField j)
          (energyFactor ε hε h modelDirections pointField j)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,output_graph ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField j,
      reverse_graph ε a α β hε ha hα hβ hw h hb C p b i P j⟩

#print axioms power_reverse_graph
#print axioms reverse_graph
#print axioms second_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialSecondFactors
