/- Actual quadrupled vacuum-parameter outputs for correlated clustered packets.
Their physical representatives retain every finite interference term and
use the original widths and the original pure-clock momentum. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralQuadrupleVacuum
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumProfiles
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredPhysicalTransfer (represented)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)

theorem quadruple_shift (h : ℝ) : -(4*h)/2 = -(2*h) := by ring

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h

def inputAmplitudes (s : ℝ) (i : Fin m) : ℂ :=
  KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a i) (p i) (-(2*h)) s

def momentumAmplitudes (s : ℝ) (i : Fin m) : ℂ :=
  KFCausalShiftedMomentumClockAmplitude.amplitude ε (a i) (p i) (-(2*h)) h s

local notation "c" => inputAmplitudes ε h a p
local notation "d" => momentumAmplitudes ε h a p

theorem represented_sum (δ : ℝ) (x : Configuration) :
    represented f c α β ε (-(2*h)) δ x = ∑ j,
      shiftedProfile ε (lift f a j) α β (4*h) (widths f δ j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x := by
  unfold represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  change ((f.amplitude (index f j).1*
    KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a (index f j).1) (p (index f j).1) (-(2*h)) x.1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ = _
  unfold shiftedProfile lift coefficients
  rw [quadruple_shift]
  ring

theorem momentum_represented_sum (δ : ℝ) (x : Configuration) :
    represented f d α β ε (-(2*h)) δ x = ∑ j,
      (1/4:ℂ)*clockSlope ε (lift f a j) (4*h) (lift f p j) x*
        shiftedProfile ε (lift f a j) α β (4*h) (widths f δ j)
          (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x := by
  unfold represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  change ((f.amplitude (index f j).1*
    KFCausalShiftedMomentumClockAmplitude.amplitude ε (a (index f j).1) (p (index f j).1) (-(2*h)) h x.1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ = _
  unfold KFCausalShiftedMomentumClockAmplitude.amplitude clockSlope shiftedProfile lift coefficients
  rw [quadruple_shift]
  push_cast
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |2*h| ≤ Real.pi*ε/3)

def finiteOutput (δ : ℝ) : Hilbert := if hδ : 0 < δ then ∑ j,
  KFCausalReciprocalNeutralQuadrupleVacuum.output ε (lift f a j) h (widths f δ j)
    hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
    (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb else 0

def finiteMomentumOutput (δ : ℝ) : Hilbert := if hδ : 0 < δ then ∑ j,
  KFCausalReciprocalNeutralQuadrupleVacuum.momentumOutput ε (lift f a j) h (widths f δ j)
    hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
    (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb else 0

theorem finiteOutput_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteOutput f ε h a p hε hh ha hb δ =ᵐ[volume] represented f c α β ε (-(2*h)) δ := by
  rw [finiteOutput,dif_pos hδ]
  have hp := ae_all_iff.mpr (fun j : Fin (count f) =>
    KFCausalReciprocalNeutralQuadrupleVacuum.output_coe ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb)
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun j => KFCausalReciprocalNeutralQuadrupleVacuum.output ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb),hp] with x hs hp
  rw [hs,represented_sum]
  exact Finset.sum_congr rfl (fun j _ => hp j)

theorem finiteMomentumOutput_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentumOutput f ε h a p hε hh ha hb δ =ᵐ[volume] represented f d α β ε (-(2*h)) δ := by
  rw [finiteMomentumOutput,dif_pos hδ]
  have hp := ae_all_iff.mpr (fun j : Fin (count f) =>
    KFCausalReciprocalNeutralQuadrupleVacuum.momentumOutput_coe ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb)
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun j => KFCausalReciprocalNeutralQuadrupleVacuum.momentumOutput ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb),hp] with x hs hp
  rw [hs,momentum_represented_sum]
  exact Finset.sum_congr rfl (fun j _ => hp j)

theorem finiteOutput_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteOutput f ε h a p hε hh ha hb δ) ∈ (orderedExponential ε hε (4*h)).graph := by
  have hs := (orderedExponential ε hε (4*h)).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (count f)))) =>
      KFCausalReciprocalNeutralQuadrupleVacuum.output_graph ε (lift f a j) h (widths f δ j)
        hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb)
  simpa only [KFCausalCorrelatedClusteredInputProfiles.finiteState,finiteOutput,dif_pos hδ,
    KFCausalReciprocalNeutralSuperposition.state,← prod_mk_sum] using hs

theorem finiteMomentumOutput_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumOutput f ε h a p hε hh ha hb δ) ∈ (orderedExponential ε hε (4*h)).graph := by
  have hs := (orderedExponential ε hε (4*h)).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (count f)))) =>
      KFCausalReciprocalNeutralQuadrupleVacuum.momentumOutput_graph ε (lift f a j) h (widths f δ j)
        hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) hb)
  simpa only [KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum,finiteMomentumOutput,dif_pos hδ,
    KFCausalReciprocalNeutralSuperposition.momentum,← prod_mk_sum] using hs

#print axioms quadruple_shift
#print axioms represented_sum
#print axioms momentum_represented_sum
#print axioms finiteOutput_coe
#print axioms finiteMomentumOutput_coe
#print axioms finiteOutput_graph
#print axioms finiteMomentumOutput_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumProfiles
