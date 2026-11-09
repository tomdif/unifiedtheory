/- All eight second actions for the existing actual clock momentum of
an arbitrary sourced polynomial packet. Circle coefficients and finite
linearity retain the full polynomial, with no degree cutoff. -/
import UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondCurves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondFactors
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalSourceCircleCoefficients (normalization)
open KFCausalVariableWidthPolynomialMomentum (momentum momentumFactor powerMomentumFactor momentumFactor_graph)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
  (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5) (C : ℂ)
local notation "hb₀" => original_strip ε h hε hb

def powerSecond (n : ℕ) (j : Fin 8) : Hilbert := (C*normalization n) •
  KFCausalPolynomialMomentumSecondCurves.meanSecond ε a α β hε ha hα hβ hw h hb p b i n j

include hh in
theorem power_reverse_graph (n : ℕ) (j : Fin 8) :
    (powerMomentumFactor ε a α β hε ha hα hβ hw h p b i C hb₀ n modelDirections pointField j,
      powerSecond ε a α β hε ha hα hβ hw h hb p b i C n j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph :=
  (reverseFactor ε hε h modelDirections pointField j).graph.smul_mem (C*normalization n)
    (KFCausalPolynomialMomentumSecondCurves.mean_reverse_graph ε a α β hε ha hα hβ hw h hh hb p b i n j)

def second (P : Polynomial ℂ) (j : Fin 8) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerSecond ε a α β hε ha hα hβ hw h hb p b i C n j

include hh in
theorem reverse_graph (P : Polynomial ℂ) (j : Fin 8) :
    (momentumFactor ε a α β hε ha hα hβ hw h p b i C hb₀ P modelDirections pointField j,
      second ε a α β hε ha hα hβ hw h hb p b i C P j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (reverseFactor ε hε h modelDirections pointField j).graph.smul_mem (P.coeff n)
      (power_reverse_graph ε a α β hε ha hα hβ hw h hh hb p b i C n j))
  simpa only [momentumFactor,second,Prod.smul_mk,← prod_mk_sum] using hs

include hh in
theorem second_graph (P : Polynomial ℂ) (j : Fin 8) :
    (momentum ε a α β hε ha hα hβ hw h p b i C P,
      second ε a α β hε ha hα hβ hw h hb p b i C P j) ∈
        (composition (reverseFactor ε hε h modelDirections pointField j)
          (energyFactor ε hε h modelDirections pointField j)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,momentumFactor_graph ε a α β hε ha hα hβ hw h hh p b i C hb₀ P modelDirections pointField j,
      reverse_graph ε a α β hε ha hα hβ hw h hh hb p b i C P j⟩

#print axioms power_reverse_graph
#print axioms reverse_graph
#print axioms second_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondFactors
