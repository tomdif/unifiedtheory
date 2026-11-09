/- The full correlated finite slice Fourier integrals are representatives
of the actual unitary mixedCoordinates transform. The existing L2 bounds
discharge the general fiber formula, with no separation of clock widths. -/
import UnifiedTheory.Audit.KFCausalPartialFourierFiberFormula
import UnifiedTheory.Audit.KFCausalNarrowFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Limit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierOperatorBridge
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierGeneralCoordinates
open KFCausalNarrowFourierCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalShiftedNarrowFourierGeometry (reconstruct)
open KFCausalShiftedNarrowJointGaussian (narrow spectator)
open KFCausalCorrelatedClusteredPotentialFourierClock (fourierProfile)
open KFCausalCorrelatedClusteredJointFourierL2Limit (finiteInput limitingInput)
open KFCausalPartialFourierFiberFormula (sliceFourier)

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
local notation "c" => amplitudes ε y a p
local notation "F" => fieldProfile f c α β ε y z k

def pairedProfile (δ : ℝ) (x : Product) : ℂ := F δ (x.2 0,reconstruct x.1 x.2)
def frequencyProfile (δ : ℝ) (x : Product) : ℂ := fourierProfile f α β ε y z a p k δ (x.2 0) x.1 x.2

theorem sliceFourier_eq (δ : ℝ) :
    sliceFourier 2 4 (pairedProfile f α β ε y z a p k δ) = frequencyProfile f α β ε y z a p k δ := rfl

theorem frequency_pullback (δ : ℝ) (x : Configuration) :
    frequencyProfile f α β ε y z a p k δ (frequencyChart x) =
      fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
  rw [frequencyChart_apply]
  rfl

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (ha : ∀ i, 0 < a i)

include hα hε hy in
theorem slice_integrable (δ : ℝ) (hδ : 0 < δ) (v : Block 4) :
    Integrable (fun u => pairedProfile f α β ε y z a p k δ (u,v)) := by
  have he : (fun u => pairedProfile f α β ε y z a p k δ (u,v)) =
      KFCausalCorrelatedClusteredShiftedNarrowProfiles.slice f (c (v 0)) α β
        (KFCausalClockFloorRelativeShift.scale ε y (v 0))
        (KFCausalClockFloorRelativeShift.scale ε z (v 0)) k δ v := by
    funext u
    exact KFCausalCorrelatedClusteredShiftedNarrowProfiles.actual_slice f α β k c ε y z δ (v 0) u v
  rw [he]
  apply integrable_finset_sum
  intro i _
  apply Integrable.const_mul
  exact KFCausalShiftedNarrowFourierSlices.physicalSlice_integrable α β _ _ _ _ _ k
    (KFCausalShiftedNarrowFourierGeometry.shifted_coefficient_positive α ε y (v 0) hα hε hy)
    (lt_of_lt_of_le zero_lt_one (KFCausalCorrelatedClusteredProfiles.widths_admissible f δ hδ.le i)) v

include hα hβ hw hε hy hz ha in
theorem frequency_memLp (δ : ℝ) (hδ : 0 < δ) :
    MemLp (frequencyProfile f α β ε y z a p k δ) 2 volume := by
  have hm := KFCausalCorrelatedClusteredJointFourierL2Limit.finiteInput_memLp
    f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ
  have hp : MemLp ((frequencyProfile f α β ε y z a p k δ) ∘ frequencyChart) 2 volume := by
    simpa only [Function.comp_def,frequency_pullback] using hm
  simpa only [Function.comp_def,MeasurableEquiv.apply_symm_apply] using
    hp.comp_measurePreserving frequencyChart_preserves_volume.symm

theorem paired_representation (δ : ℝ) (u : Hilbert) (hu : u =ᵐ[volume] F δ) :
    pairedCoordinates u =ᵐ[volume] pairedProfile f α β ε y z a p k δ := by
  have hp := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae hu
  filter_upwards [KFCausalNarrowFourierGeneralCoordinates.pairedCoordinates_coe u,hp] with x hx hpx
  rw [hx]
  simpa only [pairedChart_symm] using hpx

theorem paired_memLp (δ : ℝ) (u : Hilbert) (hu : u =ᵐ[volume] F δ) :
    MemLp (pairedProfile f α β ε y z a p k δ) 2 volume :=
  (Lp.memLp (pairedCoordinates u)).ae_eq (paired_representation f α β ε y z a p k δ u hu)

theorem finiteInput_frequency_coe (δ : ℝ) (hδ : 0 < δ) :
    frequencyCoordinates (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ) =ᵐ[volume]
      frequencyProfile f α β ε y z a p k δ := by
  have hp := frequencyChart_preserves_volume.symm.quasiMeasurePreserving.ae
    (KFCausalCorrelatedClusteredJointFourierL2Limit.finiteInput_coe
      f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ)
  filter_upwards [frequencyCoordinates_coe (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ),hp]
    with x hx hp
  rw [hx]
  change _ = fourierProfile f α β ε y z a p k δ _ _ _ at hp
  rw [← frequency_pullback,MeasurableEquiv.apply_symm_apply,frequencyChart_symm] at hp
  exact hp

theorem mixedCoordinates_finite (δ : ℝ) (hδ : 0 < δ) (u : Hilbert) (hu : u =ᵐ[volume] F δ) :
    mixedCoordinates u = frequencyCoordinates (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ) := by
  let hF := paired_memLp f α β ε y z a p k δ u hu
  let hG := frequency_memLp f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ
  have he : pairedCoordinates u = hF.toLp (pairedProfile f α β ε y z a p k δ) :=
    Lp.ext ((paired_representation f α β ε y z a p k δ u hu).trans hF.coeFn_toLp.symm)
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates u) = _
  rw [he]
  apply Lp.ext
  exact (KFCausalPartialFourierFiberFormula.leftFourier_toLp_coe 2 4 _ hF
    (Eventually.of_forall (slice_integrable f α β ε y z a p k hα hε hy δ hδ)) hG).trans
      (finiteInput_frequency_coe f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ).symm

theorem mixedCoordinates_limit (u : ℝ → Hilbert) (v : Hilbert)
    (hu : ∀ δ, 0 < δ → u δ =ᵐ[volume] F δ)
    (hv : Tendsto u (𝓝[>] 0) (𝓝 v)) :
    mixedCoordinates v = frequencyCoordinates (limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha) := by
  have h1 := (mixedCoordinates.continuous.tendsto v).comp hv
  have h2 := (frequencyCoordinates.continuous.tendsto _).comp
    (KFCausalCorrelatedClusteredJointFourierL2Limit.finiteInput_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha)
  apply tendsto_nhds_unique h1
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (mixedCoordinates_finite f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ (u δ) (hu δ hδ)).symm

#print axioms sliceFourier_eq
#print axioms frequency_pullback
#print axioms slice_integrable
#print axioms frequency_memLp
#print axioms paired_representation
#print axioms paired_memLp
#print axioms finiteInput_frequency_coe
#print axioms mixedCoordinates_finite
#print axioms mixedCoordinates_limit
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierOperatorBridge
