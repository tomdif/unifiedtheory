/- All four natural second kinetic actions exist on the previously
constructed physical state and its actual pure-clock momentum. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumKineticLimit
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalKineticSeconds
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalCorrelatedClusteredInputProfiles (amplitudes inputAmplitude_continuous inputAmplitude_memLp)
open KFCausalCorrelatedClusteredMomentumAmplitudes (amplitude_continuous amplitude_memLp)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "c" => amplitudes ε a p
local notation "hc" => fun i => inputAmplitude_continuous ε (a i) (p i)
local notation "hc2" => fun i => inputAmplitude_memLp ε (a i) (p i) hε (ha i)
local notation "d" => KFCausalCorrelatedClusteredMomentumAmplitudes.amplitudes ε a p
local notation "hd" => fun i => amplitude_continuous ε (a i) (p i) hε
local notation "hd2" => fun i => amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "K" => KFCausalCorrelatedClusteredInputKineticLimit.limitingOutput f ε h a p hε hh ha
local notation "L" => KFCausalCorrelatedClusteredMomentumKineticLimit.limitingOutput f ε h a p hε hh ha

theorem reverseFactor_kinetic (j : Fin 4) :
    reverseFactor ε hε h modelDirections pointField (kineticIndex j) =
      KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j) := by
  fin_cases j <;> rfl

def inputSecond (j : Fin 4) : Hilbert :=
  KFCausalCorrelatedClusteredKineticSecondLimit.limitingOutput f c α β ε h hα hβ hε hc hc2 j

def momentumSecond (j : Fin 4) : Hilbert := (-Complex.I*(h:ℂ)) •
  KFCausalCorrelatedClusteredKineticSecondLimit.limitingOutput f d α β ε h hα hβ hε hd hd2 j

theorem input_reverse_graph (j : Fin 4) :
    (K j,inputSecond f ε h a p hε hh ha j) ∈ (reverseFactor ε hε h modelDirections pointField (kineticIndex j)).graph := by
  rw [reverseFactor_kinetic ε h hε j]
  exact KFCausalCorrelatedClusteredKineticSecondLimit.limiting_reverse_graph f c α β ε h hα hβ hε hc hc2 j

theorem momentum_reverse_graph (j : Fin 4) :
    (L j,momentumSecond f ε h a p hε hh ha j) ∈ (reverseFactor ε hε h modelDirections pointField (kineticIndex j)).graph := by
  rw [reverseFactor_kinetic ε h hε j]
  exact (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).graph.smul_mem (-Complex.I*(h:ℂ))
    (KFCausalCorrelatedClusteredKineticSecondLimit.limiting_reverse_graph f d α β ε h hα hβ hε hd hd2 j)

theorem input_second_graph (j : Fin 4) :
    (ψ,inputSecond f ε h a p hε hh ha j) ∈
      (composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
        (energyFactor ε hε h modelDirections pointField (kineticIndex j))).graph :=
  (composition_graph _ _ _ _).mpr ⟨K j,
    KFCausalCorrelatedClusteredInputKineticLimit.limiting_graph f ε h a p hε hh ha j,
    input_reverse_graph f ε h a p hε hh ha j⟩

theorem momentum_second_graph (j : Fin 4) :
    (b,momentumSecond f ε h a p hε hh ha j) ∈
      (composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
        (energyFactor ε hε h modelDirections pointField (kineticIndex j))).graph :=
  (composition_graph _ _ _ _).mpr ⟨L j,
    KFCausalCorrelatedClusteredMomentumKineticLimit.limiting_graph f ε h a p hε hh ha j,
    momentum_reverse_graph f ε h a p hε hh ha j⟩

theorem second_domains (j : Fin 4) :
    ψ ∈ (composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
        (energyFactor ε hε h modelDirections pointField (kineticIndex j))).domain ∧
      b ∈ (composition (reverseFactor ε hε h modelDirections pointField (kineticIndex j))
        (energyFactor ε hε h modelDirections pointField (kineticIndex j))).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (input_second_graph f ε h a p hε hh ha j),
   LinearPMap.mem_domain_of_mem_graph (momentum_second_graph f ε h a p hε hh ha j)⟩

theorem input_form_pairing (j : Fin 4) (q r : Hilbert)
    (hqr : (q,r) ∈ (energyFactor ε hε h modelDirections pointField (kineticIndex j)).graph) :
    inner ℂ (K j) r = inner ℂ (inputSecond f ε h a p hε hh ha j) q :=
  KFCausalEnergyReverseFactors.factor_pairing ε hε h modelDirections pointField (kineticIndex j) _ _ q r
    (input_reverse_graph f ε h a p hε hh ha j) hqr

theorem momentum_form_pairing (j : Fin 4) (q r : Hilbert)
    (hqr : (q,r) ∈ (energyFactor ε hε h modelDirections pointField (kineticIndex j)).graph) :
    inner ℂ (L j) r = inner ℂ (momentumSecond f ε h a p hε hh ha j) q :=
  KFCausalEnergyReverseFactors.factor_pairing ε hε h modelDirections pointField (kineticIndex j) _ _ q r
    (momentum_reverse_graph f ε h a p hε hh ha j) hqr

#print axioms reverseFactor_kinetic
#print axioms input_reverse_graph
#print axioms momentum_reverse_graph
#print axioms input_second_graph
#print axioms momentum_second_graph
#print axioms second_domains
#print axioms input_form_pairing
#print axioms momentum_form_pairing
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalKineticSeconds
