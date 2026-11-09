/- Assemble the proved field-space and mass-kernel constructions with the
actual interacting operator. This is a foundation for the two analytical
field models, not a construction of their remaining unbounded Hamiltonian,
Wightman distribution, or relativistic locality theorem. -/
import UnifiedTheory.Audit.KFCausalInteractingMassMeasure
import UnifiedTheory.Audit.KFCausalMassEuclideanKernel
import UnifiedTheory.Audit.KFCausalBosonicOneParticle

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInteractingFieldExtension
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalInteractingMassMeasure KFCausalBosonicOneParticle
open KFCausalBosonicOccupationSpace KFCausalMassEuclideanKernel

abbrev EnlargedSpace := BosonicSpace Hilbert
def enlargedVacuum : EnlargedSpace := vacuum
def oneParticleEmbedding : Hilbert →ₗᵢ[ℂ] EnlargedSpace := oneParticle Hilbert

theorem enlargedVacuum_norm : ‖enlargedVacuum‖ = 1 := vacuum_norm
theorem oneParticleEmbedding_norm (z : Hilbert) : ‖oneParticleEmbedding z‖ = ‖z‖ :=
  oneParticle_norm Hilbert z
theorem oneParticleEmbedding_orthogonal (z : Hilbert) :
    inner ℂ enlargedVacuum (oneParticleEmbedding z) = 0 :=
  oneParticle_vacuum_orthogonal Hilbert z

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ) (z : Hilbert)
local notation "ρ" => physicalMassLaw ε hε h hpos hb m g k t z
local notation "hδ" => (half_pos hε)

theorem normalizedSeed_lift_norm (hz : z ≠ 0) :
    ‖oneParticleEmbedding (normalizedSeed ε hε h hpos hb m g k t z)‖ = 1 := by
  rw [oneParticleEmbedding_norm, normalizedSeed_norm ε hε h hpos hb m g k t z hz]

/-- The actual resolvent-range seed can be the mode created from the vacuum. -/
theorem exists_seed_field (hz : z ≠ 0) :
    ∃ (w : Set Hilbert) (b : HilbertBasis w ℂ Hilbert) (i : w),
      b i = normalizedSeed ε hε h hpos hb m g k t z ∧
      embed (KFCausalBosonicCCR.field i vacuumCore) =
        basedOneParticle Hilbert b (normalizedSeed ε hε h hpos hb m g k t z) := by
  obtain ⟨w, b, i, hi⟩ := exists_basis_with_vector Hilbert
    (normalizedSeed ε hε h hpos hb m g k t z)
    (normalizedSeed_norm ε hε h hpos hb m g k t z hz)
  refine ⟨w, b, i, hi, ?_⟩
  rw [← hi]
  exact (basedOneParticle_basis Hilbert b i).symm

def euclideanKernel (q : ℝ) (a b : ℝ≥0) : ℂ := kernel ρ (ε/2) hδ q a b

theorem euclideanKernel_positive (q : ℝ) {J : Type*} (S : Finset J)
    (a : J → ℝ≥0) (c : J → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, starRingEnd ℂ (c i) * c j *
      euclideanKernel ε hε h hpos hb m g k t z q (a i) (a j)).re :=
  reflection_positive ρ (ε/2) hδ q S a c

/-- The actual mass law removes the auxiliary off-support clamp. -/
theorem euclideanKernel_mass_shell (hk : 0 < k) (hz : z ≠ 0)
    (q : ℝ) (a b : ℝ≥0) :
    euclideanKernel ε hε h hpos hb m g k t z q a b =
      ∫ s, ((Real.exp (-((a : ℝ)+(b : ℝ))*Real.sqrt (q^2+s)) /
        (2*Real.sqrt (q^2+s)) : ℝ) : ℂ) ∂ρ := by
  rw [euclideanKernel, kernel_integral]
  apply integral_congr_ae
  filter_upwards [energy_on_support ρ (ε/2) q
    (physicalMassLaw_threshold ε hε h hpos hb m g k t hk z hz)] with s hs
  rw [hs]

end
end UnifiedTheory.Audit.KFCausalInteractingFieldExtension
