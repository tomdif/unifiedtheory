/- All eight second actions for the actual reciprocal neutral
exponential-polynomial packet, with both squeeze factors retained. -/
import UnifiedTheory.Audit.KFCausalPolynomialSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalSecondFactorTransport
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralSecondFactors
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalSqueezeEnergy (factorScale)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalNeutralPackets (state output output_graph rescaledPolynomial)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "d" => neutralSource ((Real.exp (-t):ℂ)*b)
local notation "Q" => rescaledPolynomial t P
local notation "c" => (Real.exp (-t/2):ℂ)
local notation "hb₀" => original_strip ε h hε hb

def second (j : Fin 8) : Hilbert := c • (factorScale (-t) j^2 • transport (-t)
  (KFCausalPolynomialSecondFactors.second ε a α β hε ha hα hβ hbw h hb C p d 4 Q j))

theorem second_graph (j : Fin 8) :
    (state ε a h w hε ha hh hw C p b P,second ε a h w hε ha hh hw hb C p b P j) ∈
      (composition (reverseFactor ε hε h modelDirections pointField j)
        (energyFactor ε hε h modelDirections pointField j)).graph :=
  (composition (reverseFactor ε hε h modelDirections pointField j)
    (energyFactor ε hε h modelDirections pointField j)).graph.smul_mem c
      (KFCausalReciprocalSecondFactorTransport.second_graph_transport ε hε h (-t) j _ _
        (KFCausalPolynomialSecondFactors.second_graph ε a α β hε ha hα hβ hbw h hb C p d 4 Q j))

theorem reverse_graph (j : Fin 8) :
    (output ε a h w hε ha hh hw C p b P hb₀ j,second ε a h w hε ha hh hw hb C p b P j) ∈
      (reverseFactor ε hε h modelDirections pointField j).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp
    (second_graph ε a h w hε ha hh hw hb C p b P j)
  have he := (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj' hu
    (output_graph ε a h w hε ha hh hw C p b P hb₀ j) rfl
  dsimp only at he
  rwa [he] at hz

#print axioms second_graph
#print axioms reverse_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralSecondFactors
