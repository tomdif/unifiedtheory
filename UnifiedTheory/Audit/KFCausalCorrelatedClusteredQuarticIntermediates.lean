/- Actual finite field-square intermediates extracted from the proved
natural reverse matter graphs. Their representatives are the fourth
field power of the original shifted correlated packets, on psi and B psi. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldLimits
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputPotentialProfiles
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredOriginalKineticSeconds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticIntermediates
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles (finiteMomentumOutput)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finite_reverse_graph finiteMomentum_reverse_graph)
open KFCausalCorrelatedClusteredMixedFieldLimits (field_zero_shift momentumAmplitudes)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "F" => finiteOutput f ε h a p hε hh hb₀ ha
local notation "G" => finiteMomentumOutput f ε h a p hε hh hb₀ ha
local notation "α" => groundWidth h
local notation "β" => neutralWidth h

theorem finite_domain (δ : ℝ) (hδ : 0 < δ) : F δ 6 ∈ (fieldSquare pointField).domain := by
  obtain ⟨u,hu,_⟩ := (composition_graph _ _ _ _).mp
    (finite_reverse_graph f ε h a p hε hh ha hb δ hδ 6)
  exact LinearPMap.mem_domain_of_mem_graph hu

theorem finiteMomentum_domain (δ : ℝ) (hδ : 0 < δ) : G δ 6 ∈ (fieldSquare pointField).domain := by
  obtain ⟨u,hu,_⟩ := (composition_graph _ _ _ _).mp
    (finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ 6)
  exact LinearPMap.mem_domain_of_mem_graph hu

def finiteQuartic (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  fieldSquare pointField ⟨F δ 6,finite_domain f ε h a p hε hh ha hb δ hδ⟩ else 0

def finiteMomentumQuartic (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  fieldSquare pointField ⟨G δ 6,finiteMomentum_domain f ε h a p hε hh ha hb δ hδ⟩ else 0

theorem finite_graph (δ : ℝ) (hδ : 0 < δ) :
    (F δ 6,finiteQuartic f ε h a p hε hh ha hb δ) ∈ (fieldSquare pointField).graph := by
  rw [finiteQuartic,dif_pos hδ]
  exact (fieldSquare pointField).mem_graph ⟨F δ 6,finite_domain f ε h a p hε hh ha hb δ hδ⟩

theorem finiteMomentum_graph (δ : ℝ) (hδ : 0 < δ) :
    (G δ 6,finiteMomentumQuartic f ε h a p hε hh ha hb δ) ∈ (fieldSquare pointField).graph := by
  rw [finiteMomentumQuartic,dif_pos hδ]
  exact (fieldSquare pointField).mem_graph ⟨G δ 6,finiteMomentum_domain f ε h a p hε hh ha hb δ hδ⟩

theorem finiteQuartic_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteQuartic f ε h a p hε hh ha hb δ =ᵐ[volume]
      fieldProfile f (amplitudes ε (-h/2) a p) α β ε (-h/2) 0 4 δ := by
  have hg := (fieldSquare_graph pointField _ _).mp (finite_graph f ε h a p hε hh ha hb δ hδ)
  have hp := KFCausalCorrelatedClusteredInputPotentialProfiles.finiteOutput_coe f ε h a p hε hh hb₀ ha δ hδ 2
  filter_upwards [hg,hp] with x hg hp
  change F δ 6 x = _ at hp
  rw [hg,hp,fieldProfile,field_zero_shift ε x.1 hε]
  change (pointField x.2:ℂ)^2*((pointField x.2:ℂ)^2*_)= (pointField x.2:ℂ)^4*_
  ring

theorem finiteMomentumQuartic_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentumQuartic f ε h a p hε hh ha hb δ =ᵐ[volume]
      fieldProfile f (momentumAmplitudes ε (-h/2) a p h) α β ε (-h/2) 0 4 δ := by
  have hg := (fieldSquare_graph pointField _ _).mp (finiteMomentum_graph f ε h a p hε hh ha hb δ hδ)
  have hp := KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput_coe f ε h a p hε hh hb₀ ha δ hδ 2
  filter_upwards [hg,hp] with x hg hp
  change G δ 6 x = _ at hp
  rw [hg,hp,fieldProfile,field_zero_shift ε x.1 hε]
  change (pointField x.2:ℂ)^2*((pointField x.2:ℂ)^2*
    KFCausalCorrelatedClusteredPhysicalTransfer.represented f (momentumAmplitudes ε (-h/2) a p h) α β ε (-h/2) δ x) =
      (pointField x.2:ℂ)^4*KFCausalCorrelatedClusteredPhysicalTransfer.represented f
        (momentumAmplitudes ε (-h/2) a p h) α β ε (-h/2) δ x
  ring

#print axioms finite_domain
#print axioms finiteMomentum_domain
#print axioms finite_graph
#print axioms finiteMomentum_graph
#print axioms finiteQuartic_coe
#print axioms finiteMomentumQuartic_coe
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticIntermediates
