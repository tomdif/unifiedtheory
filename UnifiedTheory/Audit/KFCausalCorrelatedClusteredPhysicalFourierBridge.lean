/- The physical antisymmetric Fourier integral is the actual mixed-coordinate
representative of every original finite correlated mixed-shift packet.
The joint output L2 bound follows from slice Plancherel, without a separate
Gaussian domination assumption. The final endpoint identifies the original
finite vacuum-square output and its fully cancelled clock prefactor. -/
import UnifiedTheory.Audit.KFCausalPartialFourierFiberPlancherel
import UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowProfiles
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumSecondLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalFourierBridge
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart_preserves_volume pairedChart_symm
  pairedCoordinates_coe mixed_inverse_coe)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes amplitudes_continuous)
open KFCausalShiftedPhysicalFourierSlices
open KFCausalShiftedNarrowFourierGeometry (mixedField shifted_coefficient_positive)
open KFCausalShiftedNarrowFourierSlices (neutralPacket)
open KFCausalCorrelatedClusteredShiftedNarrowProfiles (fourier_finite_sum fourier_mul_left)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalPartialFourierFiberFormula (sliceFourier)
open KFCausalVacuumMixedClockNormalization (inverseHalf normalizedClock fourier_normalization)

variable {m : ℕ} (f : Family m) (c : Fin m → ℂ) (α β : ℝ) (r t : ℂ) (k : ℕ)

def slice (δ : ℝ) (v : Block 4) (u : Block 2) : ℂ :=
  ∑ j, coefficients f δ j*c (index f j).1*
    physicalSlice α β (widths f δ j) r t (sources f j) (polynomials f j) k v u

def transformed (δ : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  ∑ j, coefficients f δ j*c (index f j).1*
    (((Real.pi:ℂ)/((α:ℂ)*r^2))*mixedField t v^k*
      Complex.exp (-radius ((α:ℂ)*r^2) (widths f δ j) u v)*
        neutralPacket β r (sources f j) (polynomials f j) v)

theorem slice_fourier (hA : 0 < ((α:ℂ)*r^2).re) (δ : ℝ) (hδ : 0 < δ)
    (u : Block 2) (v : Block 4) :
    (𝓕 (slice f c α β r t k δ v)) u = transformed f c α β r t k δ u v := by
  have hw (j : Fin (count f)) : 0 < widths f δ j :=
    lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j)
  unfold slice
  rw [fourier_finite_sum _ (fun j =>
    (physicalSlice_integrable α β (widths f δ j) r t (sources f j) (polynomials f j) k hA (hw j) v).const_mul _)]
  simp only [fourier_mul_left,transformed]
  simp_rw [physicalSlice_fourier α β _ r t _ _ k hA (hw _) v u]

theorem actual_slice (c₀ : ℝ → Fin m → ℂ) (ε y z δ s : ℝ) (u : Block 2) (v : Block 4) :
    KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f c₀ α β ε y z k δ (s,reconstruct u v) =
      slice f (c₀ s) α β (scale ε y s) (scale ε z s) k δ v u := by
  unfold KFCausalCorrelatedClusteredNeutralPowers.fieldProfile
    KFCausalCorrelatedClusteredPhysicalTransfer.represented
    KFCausalReciprocalNeutralPhysicalSliceNorm.wave slice physicalSlice
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _*((f.amplitude (index f j).1*c₀ s (index f j).1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2*_)=_
  change _=(f.amplitude (index f j).1*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*
      c₀ s (index f j).1*(_*_)
  ring

variable (ε y z : ℝ) (a p : Fin m → ℝ)
local notation "c₀" => amplitudes ε y a p
local notation "F" => KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f c₀ α β ε y z k

def pairedProfile (δ : ℝ) (x : Product) : ℂ := F δ (x.2 0,reconstruct x.1 x.2)
def frequencyProfile (δ : ℝ) (x : Product) : ℂ :=
  transformed f (c₀ (x.2 0)) α β (scale ε y (x.2 0)) (scale ε z (x.2 0)) k δ x.1 x.2

variable (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)

include hα hε hy in
theorem sliceFourier_eq (δ : ℝ) (hδ : 0 < δ) :
    sliceFourier 2 4 (pairedProfile f α β k ε y z a p δ) =
      frequencyProfile f α β k ε y z a p δ := by
  funext x
  unfold sliceFourier pairedProfile frequencyProfile
  simp_rw [actual_slice]
  exact slice_fourier f _ α β _ _ k
    (shifted_coefficient_positive α ε y (x.2 0) hα hε hy) δ hδ x.1 x.2

include hα hε hy in
theorem slice_integrable (δ : ℝ) (hδ : 0 < δ) (v : Block 4) :
    Integrable (fun u => pairedProfile f α β k ε y z a p δ (u,v)) := by
  simp only [pairedProfile,actual_slice,slice]
  apply integrable_finset_sum
  intro j _
  apply Integrable.const_mul
  exact physicalSlice_integrable α β _ _ _ _ _ k
    (shifted_coefficient_positive α ε y (v 0) hα hε hy)
    (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j)) v

include hα hε hy hz in
theorem frequencyProfile_continuous (δ : ℝ) :
    Continuous (frequencyProfile f α β k ε y z a p δ) := by
  have hv : Continuous (fun x : Product => x.2 0) := by fun_prop
  have hc (i : Fin m) : Continuous (fun x : Product => c₀ (x.2 0) i) :=
    (amplitudes_continuous ε y a p hε hy i).comp hv
  have hr : Continuous (fun x : Product => scale ε y (x.2 0)) :=
    (scale_smooth ε y hε hy).continuous.comp hv
  have ht : Continuous (fun x : Product => scale ε z (x.2 0)) :=
    (scale_smooth ε z hε hz).continuous.comp hv
  have hn (x : Product) : (α:ℂ)*(scale ε y (x.2 0))^2 ≠ 0 := by
    have hp := shifted_coefficient_positive α ε y (x.2 0) hα hε hy
    intro he
    simp only [he,Complex.zero_re,lt_self_iff_false] at hp
  unfold frequencyProfile transformed
  apply continuous_finset_sum
  intro j _
  unfold radius neutralPacket KFCausalShiftedNarrowFourierGeometry.neutral mixedField
  fun_prop (disch := exact hn)

include hα hε hy hz in
theorem mixedCoordinates_finite (δ : ℝ) (hδ : 0 < δ) (u : Hilbert)
    (hu : u =ᵐ[volume] F δ) :
    mixedCoordinates u =ᵐ[volume] frequencyProfile f α β k ε y z a p δ := by
  have hp := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae hu
  have he : pairedCoordinates u =ᵐ[volume] pairedProfile f α β k ε y z a p δ := by
    filter_upwards [pairedCoordinates_coe u,hp] with x hx hpx
    rw [hx]
    simpa only [pairedChart_symm] using hpx
  let hF : MemLp (pairedProfile f α β k ε y z a p δ) 2 volume :=
    (Lp.memLp (pairedCoordinates u)).ae_eq he
  have hGm : AEStronglyMeasurable
      (sliceFourier 2 4 (pairedProfile f α β k ε y z a p δ)) volume := by
    rw [sliceFourier_eq f α β k ε y z a p hα hε hy δ hδ]
    exact (frequencyProfile_continuous f α β k ε y z a p hα hε hy hz δ).aestronglyMeasurable
  have hU : pairedCoordinates u = hF.toLp (pairedProfile f α β k ε y z a p δ) :=
    Lp.ext (he.trans hF.coeFn_toLp.symm)
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates u) =ᵐ[volume] _
  rw [hU]
  have hcoe := KFCausalPartialFourierFiberPlancherel.leftFourier_toLp_coe 2 4 _ hF
    (Eventually.of_forall (slice_integrable f α β k ε y z a p hα hε hy δ hδ)) hGm
  rw [sliceFourier_eq f α β k ε y z a p hα hε hy δ hδ] at hcoe
  exact hcoe

variable (h : ℝ)
local notation "α₀" => KFCausalChargeGaussianGeometry.groundWidth h
local notation "β₀" => KFCausalClockFloorInvariantTrial.neutralWidth h

def normalizedFinite (δ : ℝ) (x : Product) : ℂ :=
  ∑ j, coefficients f δ j*
    normalizedClock ε (a (index f j).1) (p (index f j).1) (-h) (x.2 0)*
    ((Real.pi:ℂ)/(α₀:ℂ))*
    Complex.exp (-radius ((α₀:ℂ)*(scale ε (-h) (x.2 0))^2) (widths f δ j) x.1 x.2)*
    neutralPacket β₀ (scale ε (-h) (x.2 0)) (sources f j) (polynomials f j) x.2

include hε in
theorem finite_normalization (δ : ℝ) (x : Product) :
    inverseHalf ε (x.2 0)*frequencyProfile f α₀ β₀ 0 ε (-h) (-h) a p δ x =
      normalizedFinite f ε a p h δ x := by
  unfold frequencyProfile transformed normalizedFinite
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero,mul_one,amplitudes]
  calc
    _ = (inverseHalf ε (x.2 0)*
      KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a (index f j).1)
        (p (index f j).1) (-h) (x.2 0)*
      ((Real.pi:ℂ)/((α₀:ℂ)*(scale ε (-h) (x.2 0))^2)))*coefficients f δ j*
      Complex.exp (-radius ((α₀:ℂ)*(scale ε (-h) (x.2 0))^2) (widths f δ j) x.1 x.2)*
      neutralPacket β₀ (scale ε (-h) (x.2 0)) (sources f j) (polynomials f j) x.2 := by ring
    _ = _ := by rw [fourier_normalization _ _ _ _ _ _ hε]; ring

variable (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)

include hε in
theorem original_finite_square_mixed (δ : ℝ) (hδ : 0 < δ) :
    mixedCoordinates (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds
      f ε h a p hε hh ha hb δ 7) =ᵐ[volume] normalizedFinite f ε a p h δ := by
  let U := KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb δ
  have hu : U =ᵐ[volume] KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f
      (amplitudes ε (-h) a p) α₀ β₀ ε (-h) (-h) 0 δ := by
    filter_upwards [KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_coe
      f ε h a p hε hh ha hb δ hδ] with x hx
    simpa only [KFCausalCorrelatedClusteredNeutralPowers.fieldProfile,pow_zero,one_mul,
      KFCausalCorrelatedClusteredDoubleVacuumProfiles.inputAmplitudes,amplitudes] using hx
  have hy : |-h| ≤ Real.pi*ε/3 := by simpa only [abs_neg] using hb
  have he := mixedCoordinates_finite f α₀ β₀ 0 ε (-h) (-h) a p
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh) hε hy hy δ hδ U hu
  rw [KFCausalCorrelatedClusteredVacuumSecondLimit.finiteSeconds_eq f ε h a p hε hh ha hb δ hδ]
  filter_upwards [mixed_inverse_coe ε hε U,he] with x hx he
  rw [hx,he]
  exact finite_normalization f ε a p hε h δ x

#print axioms slice_fourier
#print axioms actual_slice
#print axioms sliceFourier_eq
#print axioms slice_integrable
#print axioms frequencyProfile_continuous
#print axioms mixedCoordinates_finite
#print axioms finite_normalization
#print axioms original_finite_square_mixed
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalFourierBridge
