/- The actual finite momentum matter spectral endpoints retain all correlated
terms. Their representatives have field shift -h/2 and Gaussian shift -h.
Their bounded inverse-half-clock images are the original finite seconds. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumMatterSpectral
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredDoubleVacuumProfiles
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticIntermediates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSpectralProfiles
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredDoubleVacuumProfiles (momentumAmplitudes)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalCoherentMatterSpectralProfile (multiplier field_eq)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => momentumAmplitudes ε h a p

theorem represented_sum (δ : ℝ) (j : Fin 2) (x : Configuration) :
    fieldProfile f c α β ε (-h) (-h/2) (degree j) δ x = ∑ k,
      multiplier ε h j x*((1/2:ℂ)*clockSlope ε (lift f a k) (2*h) (lift f p k) x*
        shiftedProfile ε (lift f a k) α β (2*h) (widths f δ k)
          (coefficients f δ k) (lift f p k) (sources f k) (polynomials f k) x) := by
  rw [fieldProfile,KFCausalCorrelatedClusteredDoubleVacuumProfiles.momentum_represented_sum,Finset.mul_sum]
  simp only [multiplier,field_eq]

variable (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)

def finiteSpectral (δ : ℝ) (j : Fin 2) : Hilbert := if hδ : 0 < δ then ∑ k,
  KFCausalReciprocalNeutralMomentumMatterSpectral.spectral ε (lift f a k) h (widths f δ k)
    hε (ha (index f k).1) hh (widths_admissible f δ hδ.le k) hb
    (coefficients f δ k) (lift f p k) (sources f k) (polynomials f k) j else 0

theorem finiteSpectral_coe (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    finiteSpectral f ε h a p hε hh ha hb δ j =ᵐ[volume]
      fieldProfile f c α β ε (-h) (-h/2) (degree j) δ := by
  rw [finiteSpectral,dif_pos hδ]
  have hp := ae_all_iff.mpr (fun k : Fin (count f) =>
    KFCausalReciprocalNeutralMomentumMatterSpectral.spectral_coe ε (lift f a k) h (widths f δ k)
      hε (ha (index f k).1) hh (widths_admissible f δ hδ.le k) hb
      (coefficients f δ k) (lift f p k) (sources f k) (polynomials f k) j)
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun k => KFCausalReciprocalNeutralMomentumMatterSpectral.spectral ε (lift f a k) h (widths f δ k)
      hε (ha (index f k).1) hh (widths_admissible f δ hδ.le k) hb
      (coefficients f δ k) (lift f p k) (sources f k) (polynomials f k) j),hp] with x hs hp
  rw [hs,represented_sum]
  exact Finset.sum_congr rfl (fun k _ => hp k)

theorem finiteMomentumSeconds_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds f ε h a p hε hh ha hb δ (matterIndex j) =
      inverseL ε hε (finiteSpectral f ε h a p hε hh ha hb δ j) := by
  simp only [KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds,finiteSpectral,dif_pos hδ,
    KFCausalReciprocalNeutralMomentumStrongHamiltonian.seconds,KFCausalReciprocalNeutralMomentumMatterSpectral.second_eq,map_sum]

#print axioms represented_sum
#print axioms finiteSpectral_coe
#print axioms finiteMomentumSeconds_eq
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSpectralProfiles
