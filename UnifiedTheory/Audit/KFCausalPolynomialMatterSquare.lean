/- Both second matter actions for arbitrary finite complex polynomials
of a sourced physical Gaussian. The source-circle representation and
integrated intermediate graphs discharge every reverse-domain premise. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterCurve
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients
open KFCausalVariableWidthPolynomialDomain (input output powerOutput output_graph)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "hb₀" => original_strip ε h hε hb

def powerSecond (n : ℕ) (j : Fin 2) : Hilbert := (C*normalization n) •
  KFCausalCoherentMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb
    (weight n) (fun _ => p) (circleSource b i) j

theorem power_linear_reverse_graph (n : ℕ) :
    (powerOutput ε a α β hε ha hα hβ hw h C p b i hb₀ n modelDirections pointField 5,
      powerSecond ε a α β hε ha hα hβ hw h hb C p b i n 0) ∈
        (reversedMatterFactor ε hε h (physicalField pointField)).graph :=
  (reversedMatterFactor ε hε h (physicalField pointField)).graph.smul_mem (C*normalization n)
    (KFCausalCoherentMatterCurve.linear_reverse_graph ε a α β hε ha hα hβ hw h hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i))

theorem power_quadratic_reverse_graph (n : ℕ) :
    (powerOutput ε a α β hε ha hα hβ hw h C p b i hb₀ n modelDirections pointField 6,
      powerSecond ε a α β hε ha hα hβ hw h hb C p b i n 1) ∈
        (reversedMatterFactor ε hε h (fieldSquare pointField)).graph :=
  (reversedMatterFactor ε hε h (fieldSquare pointField)).graph.smul_mem (C*normalization n)
    (KFCausalCoherentMatterCurve.quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i))

def second (P : Polynomial ℂ) (j : Fin 2) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerSecond ε a α β hε ha hα hβ hw h hb C p b i n j

theorem linear_reverse_graph (P : Polynomial ℂ) :
    (output ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField 5,
      second ε a α β hε ha hα hβ hw h hb C p b i P 0) ∈
        (reversedMatterFactor ε hε h (physicalField pointField)).graph := by
  have hs := (reversedMatterFactor ε hε h (physicalField pointField)).graph.sum_mem
    (fun n (_ : n ∈ P.support) =>
      (reversedMatterFactor ε hε h (physicalField pointField)).graph.smul_mem (P.coeff n)
        (power_linear_reverse_graph ε a α β hε ha hα hβ hw h hb C p b i n))
  simpa only [output,second,Prod.smul_mk,← prod_mk_sum] using hs

theorem quadratic_reverse_graph (P : Polynomial ℂ) :
    (output ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField 6,
      second ε a α β hε ha hα hβ hw h hb C p b i P 1) ∈
        (reversedMatterFactor ε hε h (fieldSquare pointField)).graph := by
  have hs := (reversedMatterFactor ε hε h (fieldSquare pointField)).graph.sum_mem
    (fun n (_ : n ∈ P.support) =>
      (reversedMatterFactor ε hε h (fieldSquare pointField)).graph.smul_mem (P.coeff n)
        (power_quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb C p b i n))
  simpa only [output,second,Prod.smul_mk,← prod_mk_sum] using hs

theorem linear_square_graph (P : Polynomial ℂ) :
    (input ε a α β hε ha hα hβ hw C p b i P,
      second ε a α β hε ha hα hβ hw h hb C p b i P 0) ∈
        (composition (reversedMatterFactor ε hε h (physicalField pointField))
          (matterFactor ε hε h (physicalField pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,output_graph ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField 5,
      linear_reverse_graph ε a α β hε ha hα hβ hw h hb C p b i P⟩

theorem quadratic_square_graph (P : Polynomial ℂ) :
    (input ε a α β hε ha hα hβ hw C p b i P,
      second ε a α β hε ha hα hβ hw h hb C p b i P 1) ∈
        (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
          (matterFactor ε hε h (fieldSquare pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,output_graph ε a α β hε ha hα hβ hw h C p b i hb₀ P modelDirections pointField 6,
      quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb C p b i P⟩

#print axioms power_linear_reverse_graph
#print axioms power_quadratic_reverse_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
#print axioms linear_square_graph
#print axioms quadratic_square_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialMatterSquare
