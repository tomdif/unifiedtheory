/- The mass-shell construction instantiated with the actual interacting
resolvent's probability law. This transfers proved spectral data to a new
field-theory one-particle space; it does not identify that new space with
the original configuration space or prove relativistic locality. -/
import UnifiedTheory.Audit.KFCausalInteractingMassMeasure
import UnifiedTheory.Audit.KFCausalMassShellTwoPoint
import UnifiedTheory.Audit.KFCausalBosonicOneParticle

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingMassShell
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalInteractingMassMeasure KFCausalRelativisticMassShell

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ) (z : Hilbert)
local notation "ρ" => physicalMassLaw ε hε h hpos hb m g k t z

abbrev ParticleSpace := OneParticle ρ (ε/2)

def energy : ParticleSpace ε hε h hpos hb m g k t z →ₗ.[ℂ]
    ParticleSpace ε hε h hpos hb m g k t z := energyOperator ρ (ε/2)

theorem energy_selfAdjoint : IsSelfAdjoint (energy ε hε h hpos hb m g k t z) :=
  KFCausalRelativisticMassShell.energy_selfAdjoint ρ (ε/2)

theorem energy_lower (f : (energy ε hε h hpos hb m g k t z).domain) :
    (ε/2)*‖(f : ParticleSpace ε hε h hpos hb m g k t z)‖^2 ≤
      (inner ℂ (energy ε hε h hpos hb m g k t z f)
        (f : ParticleSpace ε hε h hpos hb m g k t z)).re :=
  energy_floor ρ (ε/2) (by positivity) f

theorem mass_shell_equation (hk : 0 < k) (hz : z ≠ 0) :
    ∀ᵐ x ∂shellMeasure ρ (ε/2), (frequency (ε/2) x)^2 - ‖x.2‖^2 = x.1 :=
  shell_equation ρ (ε/2) (by positivity)
    (physicalMassLaw_threshold ε hε h hpos hb m g k t hk z hz)

def testVector : KFCausalMassShellSchwartzRestriction.Test →L[ℂ]
    ParticleSpace ε hε h hpos hb m g k t z :=
  KFCausalMassShellTwoPoint.testVector ρ (ε/2) (by positivity)

theorem twoPoint_continuous : Continuous
    (fun p : KFCausalMassShellSchwartzRestriction.Test ×
      KFCausalMassShellSchwartzRestriction.Test =>
      inner ℂ (testVector ε hε h hpos hb m g k t z p.1)
        (testVector ε hε h hpos hb m g k t z p.2)) :=
  KFCausalMassShellTwoPoint.twoPoint_continuous ρ (ε/2) (by positivity)

theorem twoPoint_positive {J : Type*} (S : Finset J)
    (F : J → KFCausalMassShellSchwartzRestriction.Test) (c : J → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, starRingEnd ℂ (c i) * c j *
      inner ℂ (testVector ε hε h hpos hb m g k t z (F i))
        (testVector ε hε h hpos hb m g k t z (F j))).re :=
  KFCausalMassShellTwoPoint.twoPoint_positive ρ (ε/2) (by positivity) S F c

def bosonicInjection : ParticleSpace ε hε h hpos hb m g k t z →ₗᵢ[ℂ]
    KFCausalBosonicOneParticle.BosonicSpace
      (ParticleSpace ε hε h hpos hb m g k t z) :=
  KFCausalBosonicOneParticle.oneParticle _

theorem bosonicInjection_injective :
    Function.Injective (bosonicInjection ε hε h hpos hb m g k t z) :=
  (bosonicInjection ε hε h hpos hb m g k t z).injective

end
end UnifiedTheory.Audit.KFCausalInteractingMassShell
