/- Actual undressed input representatives and their independent clock
coefficients, connected to the zero-shift physical Gram wavefunction. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalSliceNorm
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputProfiles
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalReciprocalNeutralPhysicalSliceNorm (wave)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalReciprocalNeutralDifference (join)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorCoherentDerivative (clockMultiplier clockMultiplier_memLp)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp clockFunction_continuous neutralWidth)
open KFCausalChargeGaussianGeometry (groundWidth)

def inputAmplitude (ε a p s : ℝ) : ℂ := clockPhase p (s:ℂ)*clockFunction ε a s

theorem inputAmplitude_continuous (ε a p : ℝ) : Continuous (inputAmplitude ε a p) := by
  have hc : Continuous (fun s : ℝ => clockPhase p (s:ℂ)) := by unfold clockPhase; fun_prop
  exact hc.mul (clockFunction_continuous ε a)

theorem inputAmplitude_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (inputAmplitude ε a p) 2 volume := by
  have hm := clockMultiplier_memLp 1 p (clockFunction ε a) (clockFunction_memLp ε a hε ha)
  change MemLp (fun s : ℝ => 1*clockPhase p (s:ℂ)*clockFunction ε a s) 2 volume at hm
  simpa only [one_mul] using hm

def amplitudes {m : ℕ} (ε : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ := inputAmplitude ε (a i) (p i) s

theorem wave_difference (n m : ℕ) (α β : ℝ) (r : ℂ)
    (w : Fin n → ℝ) (c b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (w' : Fin m → ℝ) (c' b' : Fin m → ℂ) (P' : Fin m → Polynomial ℂ)
    (q : KFCausalTransverseDilationFlow.Transverse) :
    wave (n+m) α β (join w w') r (join c (fun i => -c' i)) (join b b') (join P P') q =
      wave n α β w r c b P q-wave m α β w' r c' b' P' q := by
  unfold wave
  rw [Fin.sum_univ_add]
  simp only [join,Fin.addCases_left,Fin.addCases_right,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)

def represented (δ : ℝ) (x : Configuration) : ℂ :=
  wave (count f) (groundWidth h) (neutralWidth h) (widths f δ) 1
    (coefficients (reweight f (amplitudes ε a p x.1)) δ) (sources f) (polynomials f) x.2

theorem represented_sum (δ : ℝ) (x : Configuration) : represented f ε h a p δ x =
    ∑ j, KFCausalReciprocalNeutralPackets.profile ε (lift f a j) h (widths f δ j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x := by
  unfold represented wave
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalRelativeGaussianDifferential.position,ite_true,sub_self,mul_zero,zero_mul,add_zero,
    KFCausalReciprocalGaussianCoordinates.exponent,one_pow,mul_one,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  unfold KFCausalReciprocalNeutralPackets.profile KFCausalReciprocalGaussianStates.configurationDensity
  push_cast
  have he : -(groundWidth h:ℂ)*(KFCausalReciprocalGaussianStates.quadratic (widths f δ j) x.2:ℂ)-
      (neutralWidth h:ℂ)*(x.2 4:ℂ)^2 =
      -((groundWidth h:ℂ)*(KFCausalReciprocalGaussianStates.quadratic (widths f δ j) x.2:ℂ)+
        (neutralWidth h:ℂ)*(x.2 4:ℂ)^2) := by ring
  rw [he]
  change ((f.amplitude (index f j).1*inputAmplitude ε (a (index f j).1) (p (index f j).1) x.1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ = _
  unfold inputAmplitude lift coefficients
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)

def finiteState (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralSuperposition.state (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le) else 0

theorem finiteState_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteState f ε h a p hε hh ha δ =ᵐ[volume] represented f ε h a p δ := by
  rw [finiteState,dif_pos hδ]
  unfold KFCausalReciprocalNeutralSuperposition.state
  have hp : ∀ᵐ x ∂volume, ∀ j : Fin (count f),
      KFCausalReciprocalNeutralPackets.state ε (lift f a j) h (widths f δ j)
        hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x =
      KFCausalReciprocalNeutralPackets.profile ε (lift f a j) h (widths f δ j)
        (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j) x :=
    ae_all_iff.mpr (fun j => KFCausalReciprocalNeutralPackets.state_coe ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j))
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ
    (fun j => KFCausalReciprocalNeutralPackets.state ε (lift f a j) h (widths f δ j)
      hε (ha (index f j).1) hh (widths_admissible f δ hδ.le j)
      (coefficients f δ j) (lift f p j) (sources f j) (polynomials f j)),hp] with x hs hp
  rw [hs,represented_sum]
  exact Finset.sum_congr rfl (fun j _ => hp j)

theorem difference_coe (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    (finiteState f ε h a p hε hh ha δ-finiteState f ε h a p hε hh ha η : Hilbert) =ᵐ[volume]
      fun x => represented f ε h a p δ x-represented f ε h a p η x := by
  filter_upwards [Lp.coeFn_sub (finiteState f ε h a p hε hh ha δ) (finiteState f ε h a p hε hh ha η),
    finiteState_coe f ε h a p hε hh ha δ hδ,finiteState_coe f ε h a p hε hh ha η hη] with x hs h1 h2
  simp only [hs,Pi.sub_apply,h1,h2]

include hε hh ha in
theorem difference_integrable (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    Integrable (fun x => ‖represented f ε h a p δ x-represented f ε h a p η x‖^2) := by
  have hm := (Lp.memLp (finiteState f ε h a p hε hh ha δ-finiteState f ε h a p hε hh ha η)).ae_eq
    (difference_coe f ε h a p hε hh ha δ η hδ hη)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem norm_difference_integral (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖finiteState f ε h a p hε hh ha δ-finiteState f ε h a p hε hh ha η‖^2 =
      ∫ x, ‖represented f ε h a p δ x-represented f ε h a p η x‖^2 := by
  rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [difference_coe f ε h a p hε hh ha δ η hδ hη] with x hx
  rw [hx]

#print axioms inputAmplitude_continuous
#print axioms inputAmplitude_memLp
#print axioms wave_difference
#print axioms represented_sum
#print axioms finiteState_coe
#print axioms difference_coe
#print axioms difference_integrable
#print axioms norm_difference_integral
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputProfiles
