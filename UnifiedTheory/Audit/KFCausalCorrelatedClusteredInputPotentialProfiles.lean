/- Physical representatives of the existing three finite potential
outputs, with all correlated terms retained before any norm estimate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputPotentialProfiles
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift amplitudes)
open KFCausalCorrelatedClusteredPhysicalCauchy (potentialIndex finiteOutput)
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε (-h/2) a p

theorem represented_sum (δ : ℝ) (k : Fin 3) (x : Configuration) :
    KFCausalCorrelatedClusteredFieldTransfer.represented f c α β ε (-h/2) k δ x =
      ∑ j, (pointField x.2:ℂ)^k.val*shiftedProfile ε (lift f a j) α β h (widths f δ j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x := by
  unfold KFCausalCorrelatedClusteredFieldTransfer.represented
    KFCausalCorrelatedClusteredPhysicalTransfer.represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  change (pointField x.2:ℂ)^k.val*(((f.amplitude (index f j).1*
    KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a (index f j).1) (p (index f j).1) (-h/2) x.1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_) = _
  unfold shiftedProfile lift coefficients
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)

theorem finiteOutput_coe (δ : ℝ) (hδ : 0 < δ) (k : Fin 3) :
    finiteOutput f ε h a p hε hh hb ha δ (potentialIndex k) =ᵐ[volume]
      KFCausalCorrelatedClusteredFieldTransfer.represented f c α β ε (-h/2) k δ := by
  rw [finiteOutput,dif_pos hδ]
  unfold KFCausalReciprocalNeutralSuperposition.output
  have hp : ∀ᵐ x ∂volume, ∀ j : Fin (count f),
      KFCausalReciprocalNeutralPackets.output ε (lift f a j) h (widths f δ j)
        hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb (potentialIndex k) x =
      (pointField x.2:ℂ)^k.val*shiftedProfile ε (lift f a j) α β h (widths f δ j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x :=
    ae_all_iff.mpr (fun j => KFCausalReciprocalNeutralOrderedProfile.output_coe ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb k)
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun j => KFCausalReciprocalNeutralPackets.output ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb (potentialIndex k)),hp] with x hs hp
  rw [hs,represented_sum]
  exact Finset.sum_congr rfl (fun j _ => hp j)

#print axioms represented_sum
#print axioms finiteOutput_coe
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputPotentialProfiles
