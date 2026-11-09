/- Identify all three growing energy factors with the field-weighted
Gaussian outputs used in whole-clock response transport. The index order
is vacuum, linear field, quadratic field. Actual operator graphs determine
the outputs uniquely; no factor identification is assumed. -/
import UnifiedTheory.Audit.KFCausalGaussianResponsePairing
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalGaussianResponsePairing (weighted weighted_density weighted_zero weighted_field_graph)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain (shiftedOutput_fieldSquare_domain)
open UnifiedTheory.Audit.KFCausalSourcedMomentumOutput (reduced_square_domain)
open UnifiedTheory.Audit.KFCausalGaussianResponseDensities (amplitude momentum amplitude_density momentum_density)

def index : Fin 3 → Fin 8 := ![7,5,6]

theorem weighted_factor_graph (ε h : ℝ) (hε : 0 < ε) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (f g : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hf : g ∈ (fieldSquare l).domain) :
    (f,weighted l n g hf) ∈ (energyFactor ε hε h v l (index n)).graph := by
  fin_cases n
  · change (f,weighted l 0 g hf) ∈ (orderedExponential ε hε h).graph
    rw [weighted_zero]
    exact hg
  · exact (composition_graph _ _ _ _).mpr ⟨g,hg,weighted_field_graph l 0 g hf⟩
  · exact (composition_graph _ _ _ _).mpr ⟨g,hg,weighted_field_graph l 1 g hf⟩

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "S" => KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "H" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "TB" => reducedOutput ε a h hε ha hb p G H
local notation "BF" => KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw C p b h
local notation "U" => KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)
local notation "V" => KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)

theorem input_factor_eq : U =
    weighted l n G (shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l) :=
  (energyFactor ε hε h v l (index n)).mem_graph_snd_inj'
    (KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hw C p b h hb v l (index n))
    (weighted_factor_graph ε h hε v l n S G
      (state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb)
      (shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l)) rfl

include hh in
theorem momentum_factor_eq : V =
    weighted l n TB (reduced_square_domain ε a α β hε ha hα hβ hw C p b h hb l) :=
  (energyFactor ε hε h v l (index n)).mem_graph_snd_inj'
    (KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb v l (index n))
    (weighted_factor_graph ε h hε v l n BF TB
      (KFCausalSourcedMomentumOutput.reduced_graph ε a α β hε ha hα hβ hw C p b h hh hb BF
        (KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw C p b h hh))
      (reduced_square_domain ε a α β hε ha hα hβ hw C p b h hb l)) rfl

theorem input_factor_density : U =ᵐ[volume] amplitude ε a α β p (-h/2) b C l n := by
  rw [input_factor_eq]
  exact (weighted_density l n G _).trans (amplitude_density ε a α β hε ha hα hβ hw C p b h hb l n)

include hh in
theorem momentum_factor_density : V =ᵐ[volume] momentum ε a α β p (-h/2) h b C l n := by
  rw [momentum_factor_eq ε a α β hε ha hα hβ hw C p b h hh hb v l n]
  exact (weighted_density l n TB _).trans (momentum_density ε a α β hε ha hα hβ hw C p b h hb l n)

#print axioms weighted_factor_graph
#print axioms input_factor_eq
#print axioms momentum_factor_eq
#print axioms input_factor_density
#print axioms momentum_factor_density
end
end UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge
