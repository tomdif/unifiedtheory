/- Full-clock limits of the existing ordered-potential energy and
response, with an independent clock width and frequency in each block.
These are limits of actual finite-packet quantities, not Hamiltonian
graph convergence or evolution claims. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredReducedClock
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalClockLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredWholeClock (energy transport limitEnergy limitTransport)
open KFCausalCorrelatedClusteredReducedClock (reduced limitReduced)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorRelativeShift (scale)

variable {m : ℕ} (f : Family m)

def lift (a : Fin m → ℝ) (j : Fin (count f)) : ℝ := a (index f j).1
def amplitudes (ε y : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ :=
  KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a i) (p i) y s

theorem amplitudes_continuous (ε y : ℝ) (a p : Fin m → ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (i : Fin m) : Continuous (fun s => amplitudes ε y a p s i) :=
  (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε (a i) (p i) y hε hy).continuous

theorem amplitudes_memLp (ε y : ℝ) (a p : Fin m → ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (ha : ∀ i, 0 < a i) (i : Fin m) : MemLp (fun s => amplitudes ε y a p s i) 2 volume :=
  KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε (a i) (p i) y hε (ha i) hy

theorem coefficient_identity (ε h δ s : ℝ) (a p : Fin m → ℝ) :
    KFCausalReciprocalNeutralPositiveEnergy.coefficients (count f) ε h (lift f a) (lift f p) (coefficients f δ) s =
      coefficients (reweight f (amplitudes ε (-h/2) a p s)) δ := by
  funext j
  change (f.amplitude (index f j).1*KFCausalClusteredWidthProfiles.coefficients
    (f.degree (index f j).1) δ (index f j).2)*
      KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a (index f j).1) (p (index f j).1) (-h/2) s =
    (f.amplitude (index f j).1*KFCausalShiftedGaussianPhysicalProfile.clockAmplitude
      ε (a (index f j).1) (p (index f j).1) (-h/2) s)*
        KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2
  ring

theorem slice_energy (ε h δ s : ℝ) (a p : Fin m → ℝ) :
    KFCausalReciprocalNeutralPositiveEnergy.positiveSlice (count f) ε h (lift f a) (widths f δ)
      (lift f p) (coefficients f δ) (sources f) (polynomials f) s =
    Real.pi/4*∫ q, energy f (amplitudes ε (-h/2) a p) (groundWidth h) (neutralWidth h) ε (-h/2) δ (s,q) ∂jointMeasure := by
  unfold KFCausalReciprocalNeutralPositiveEnergy.positiveSlice energy KFCausalCorrelatedClusteredDensity.density
  rw [coefficient_identity]
  rfl

variable (ε h : ℝ) (a p : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε (-h/2) a p

include hb in
theorem shift_bound : |(-h/2:ℝ)| ≤ Real.pi*ε/3 := by
  rw [abs_div,abs_neg]
  norm_num
  linarith

include hε hh hb in
theorem slice_transport (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.transportResponse (count f) ε h (lift f a) (widths f δ)
      (lift f p) (coefficients f δ) (sources f) (polynomials f) s =
      Real.pi/4*∫ q, transport f c α β ε (-h/2) δ (s,q) ∂jointMeasure := by
  rw [KFCausalReciprocalNeutralWholeClock.transport_frozen_derivative _ _ _ _ _ _ _ _ _
    hε hh (widths_admissible f δ hδ.le) hb,coefficient_identity]
  exact KFCausalCorrelatedClusteredResponseLimit.actual_totalResponse_integral (reweight f (c s)) α β ε (-h/2)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    hε (shift_bound ε h hb) δ hδ s

include hε hh hb in
theorem slice_reduced (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.reducedResponse (count f) ε h (lift f a) (widths f δ)
      (lift f p) (coefficients f δ) (sources f) (polynomials f) s =
      Real.pi/4*∫ q, reduced f c α β ε (-h/2) δ (s,q) ∂jointMeasure := by
  have hy := shift_bound ε h hb
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε (-h/2) s
    (groundWidth_positive h hh) (neutralWidth_positive h hh).le (neutralWidth_bound h) hε hy
  obtain ⟨hC,hA⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β (groundWidth_positive h hh) _ hp
  obtain ⟨hE,hR,_,_⟩ := KFCausalCorrelatedClusteredIntegrals.integrability (reweight f (c s)) α β δ hδ
    (scale ε (-h/2) s) (deriv (scale ε (-h/2)) s) (neutralWidth_positive h hh) hA hC
  unfold KFCausalReciprocalNeutralWholeClock.reducedResponse
  rw [slice_energy,slice_transport f ε h a p hε hh hb δ hδ s]
  unfold reduced energy transport
  dsimp only
  rw [integral_sub (hE.const_mul (KFCausalClockResponseTransport.coefficient ε (-h/2) s))
    (hR.div_const (KFCausalClockResponseTransport.clock ε s)),integral_const_mul,integral_div]
  ring

def finiteEnergy (δ : ℝ) : ℝ := if hδ : 0 < δ then
  KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le) hb else 0

def finiteResponse (δ : ℝ) : ℝ := if hδ : 0 < δ then
  KFCausalReciprocalNeutralPotentialTransport.potentialResponse (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le) hb else 0

def limitingEnergy : ℝ := ∫ s, Real.pi/4*∫ q, limitEnergy f c α β ε (-h/2) (s,q) ∂jointMeasure
def limitingResponse : ℝ := ∫ s, Real.pi/4*∫ q, limitReduced f c α β ε (-h/2) (s,q) ∂jointMeasure

theorem finiteEnergy_integral (δ : ℝ) (hδ : 0 < δ) :
    finiteEnergy f ε h a p hε hh hb ha δ =
      ∫ s, Real.pi/4*∫ q, energy f c α β ε (-h/2) δ (s,q) ∂jointMeasure := by
  rw [finiteEnergy,dif_pos hδ,KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy_positive_integral]
  simp_rw [slice_energy]

theorem finiteResponse_integral (δ : ℝ) (hδ : 0 < δ) :
    finiteResponse f ε h a p hε hh hb ha δ =
      ∫ s, Real.pi/4*∫ q, reduced f c α β ε (-h/2) δ (s,q) ∂jointMeasure := by
  rw [finiteResponse,dif_pos hδ,KFCausalReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral]
  simp_rw [slice_reduced f ε h a p hε hh hb δ hδ]

theorem potentialEnergy_tendsto :
    Tendsto (finiteEnergy f ε h a p hε hh hb ha) (𝓝[>] 0) (𝓝 (limitingEnergy f ε h a p)) := by
  have hy := shift_bound ε h hb
  apply Tendsto.congr' _ (KFCausalCorrelatedClusteredWholeClock.full_clock_energy_tendsto f c α β ε (-h/2)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (amplitudes_continuous ε (-h/2) a p hε hy) (amplitudes_memLp ε (-h/2) a p hε hy ha))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteEnergy_integral f ε h a p hε hh hb ha δ hδ).symm

theorem potentialResponse_tendsto :
    Tendsto (finiteResponse f ε h a p hε hh hb ha) (𝓝[>] 0) (𝓝 (limitingResponse f ε h a p)) := by
  have hy := shift_bound ε h hb
  apply Tendsto.congr' _ (KFCausalCorrelatedClusteredReducedClock.full_clock_reduced_tendsto f c α β ε (-h/2)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (amplitudes_continuous ε (-h/2) a p hε hy) (amplitudes_memLp ε (-h/2) a p hε hy ha))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteResponse_integral f ε h a p hε hh hb ha δ hδ).symm

#print axioms amplitudes_continuous
#print axioms amplitudes_memLp
#print axioms coefficient_identity
#print axioms slice_energy
#print axioms shift_bound
#print axioms slice_transport
#print axioms slice_reduced
#print axioms finiteEnergy_integral
#print axioms finiteResponse_integral
#print axioms potentialEnergy_tendsto
#print axioms potentialResponse_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalClockLimit
