/- Exact physical representatives of the three ordered-potential
outputs of the existing finite pure-clock momentum states. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFieldTransfer
import UnifiedTheory.Audit.KFCausalShiftedMomentumClockAmplitude

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredPhysicalCauchy (potentialIndex)
open KFCausalShiftedMomentumClockAmplitude (amplitude amplitudes)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε h a p

theorem represented_sum (δ : ℝ) (k : Fin 3) (x : Configuration) :
    KFCausalCorrelatedClusteredFieldTransfer.represented f c α β ε (-h/2) k δ x =
      ∑ j, clockSlope ε (lift f a j) h (lift f p j) x*
        ((pointField x.2:ℂ)^k.val*shiftedProfile ε (lift f a j) α β h (widths f δ j)
          (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x) := by
  unfold KFCausalCorrelatedClusteredFieldTransfer.represented
    KFCausalCorrelatedClusteredPhysicalTransfer.represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  change (pointField x.2:ℂ)^k.val*(((f.amplitude (index f j).1*
    amplitude ε (a (index f j).1) (p (index f j).1) (-h/2) h x.1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_) = _
  unfold amplitude clockSlope shiftedProfile lift coefficients
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)

def finiteMomentumOutput (δ : ℝ) (j : Fin 8) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralSuperposition.momentumOutput (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun i => ha (index f i).1) hh
    (widths_admissible f δ hδ.le) hb j else 0

theorem finiteMomentumOutput_coe (δ : ℝ) (hδ : 0 < δ) (k : Fin 3) :
    finiteMomentumOutput f ε h a p hε hh hb ha δ (potentialIndex k) =ᵐ[volume]
      KFCausalCorrelatedClusteredFieldTransfer.represented f c α β ε (-h/2) k δ := by
  rw [finiteMomentumOutput,dif_pos hδ]
  unfold KFCausalReciprocalNeutralSuperposition.momentumOutput
  have hp : ∀ᵐ x ∂volume, ∀ j : Fin (count f),
      KFCausalReciprocalNeutralPackets.momentumOutput ε (lift f a j) h (widths f δ j)
        hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb (potentialIndex k) x =
      clockSlope ε (lift f a j) h (lift f p j) x*
        ((pointField x.2:ℂ)^k.val*shiftedProfile ε (lift f a j) α β h (widths f δ j)
          (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x) :=
    ae_all_iff.mpr (fun j => KFCausalReciprocalNeutralOrderedProfile.momentumOutput_coe ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb k)
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun j => KFCausalReciprocalNeutralPackets.momentumOutput ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb (potentialIndex k)),hp] with x hs hp
  rw [hs,represented_sum]
  exact Finset.sum_congr rfl (fun j _ => hp j)

theorem finiteMomentumOutput_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumOutput f ε h a p hε hh hb ha δ j) ∈
        (KFCausalClockFloorCommonDomain.energyFactor ε hε h KFCausalPhysicalEnergyFactors.modelDirections pointField j).graph := by
  rw [KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum,finiteMomentumOutput,dif_pos hδ,dif_pos hδ]
  exact KFCausalReciprocalNeutralSuperposition.momentumOutput_graph (count f) ε h (lift f a) (widths f δ)
    (lift f p) (coefficients f δ) (sources f) (polynomials f) hε (fun i => ha (index f i).1) hh
    (widths_admissible f δ hδ.le) hb j

#print axioms represented_sum
#print axioms finiteMomentumOutput_coe
#print axioms finiteMomentumOutput_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles
