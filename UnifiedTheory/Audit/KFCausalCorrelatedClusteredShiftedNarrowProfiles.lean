/- The exact narrow Fourier integral of every correlated mixed-shift
profile. The original reciprocal width coefficients are summed before
taking limits, so charged cancellations are preserved. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierSlices
import UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowProfiles
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalCorrelatedClusteredProfiles
open KFCausalShiftedNarrowFourierGeometry
open KFCausalShiftedNarrowFourierSlices
open KFCausalClusteredWidthProfiles (quotient)

theorem fourier_finite_sum {n : ℕ} (g : Fin n → Block 2 → ℂ)
    (hg : ∀ i, Integrable (g i)) (u : Block 2) :
    (𝓕 (fun x => ∑ i, g i x)) u = ∑ i, (𝓕 (g i)) u := by
  simp only [Real.fourier_eq,Finset.smul_sum]
  exact integral_finset_sum _ (fun i _ => (Real.fourierIntegral_convergent_iff u).mpr (hg i))

theorem fourier_mul_left (g : Block 2 → ℂ) (c : ℂ) (u : Block 2) :
    (𝓕 (fun x => c*g x)) u = c*(𝓕 g) u := by
  simpa only [mul_comm] using fourier_mul_right g c u

variable {m : ℕ} (f : Family m) (c : Fin m → ℂ) (α β : ℝ) (r t : ℂ) (k : ℕ)

def slice (δ : ℝ) (v : Block 4) (u : Block 2) : ℂ :=
  ∑ j, coefficients f δ j*c (index f j).1*
    physicalSlice α β (widths f δ j) r t (sources f j) (polynomials f j) k v u

def coefficient (i : Fin m) (v : Block 4) : ℂ :=
  ((Real.pi:ℂ)/((α:ℂ)*r^2))*f.amplitude i*c i*mixedField t v^k*
    neutralPacket β r (f.source i) (f.polynomial i) v

def transformed (δ : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  ∑ i, coefficient f c α β r t k i v*
    KFCausalReciprocalWedgeLaplace.laplaceSum (f.degree i+1)
      (KFCausalClusteredWidthProfiles.widths (f.degree i) δ)
      (KFCausalClusteredWidthProfiles.coefficients (f.degree i) δ) (radius ((α:ℂ)*r^2) u v)

def limitTransformed (u : Block 2) (v : Block 4) : ℂ :=
  ∑ i, coefficient f c α β r t k i v*
    (Complex.exp (-radius ((α:ℂ)*r^2) u v)*radius ((α:ℂ)*r^2) u v^(f.degree i))

theorem slice_fourier (hA : 0 < ((α:ℂ)*r^2).re) (δ : ℝ) (hδ : 0 < δ)
    (u : Block 2) (v : Block 4) :
    (𝓕 (slice f c α β r t k δ v)) u = transformed f c α β r t k δ u v := by
  have hw (j : Fin (count f)) : 0 < widths f δ j :=
    lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j)
  unfold slice
  rw [fourier_finite_sum _ (fun j =>
    (physicalSlice_integrable α β (widths f δ j) r t (sources f j) (polynomials f j) k hA (hw j) v).const_mul _)]
  simp only [fourier_mul_left]
  simp_rw [physicalSlice_fourier α β _ r t _ _ k hA (hw _) v u]
  unfold transformed coefficient widths coefficients sources polynomials
  rw [sum_index f (fun j =>
    ((f.amplitude j.1*KFCausalClusteredWidthProfiles.coefficients (f.degree j.1) δ j.2)*c j.1)*
      (((Real.pi:ℂ)/((α:ℂ)*r^2))*(KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℂ)*
        mixedField t v^k*Complex.exp (-(KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℂ)*
          radius ((α:ℂ)*r^2) u v)*neutralPacket β r (f.source j.1) (f.polynomial j.1) v))]
  apply Finset.sum_congr rfl
  intro i _
  unfold KFCausalReciprocalWedgeLaplace.laplaceSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem transformed_exact (δ : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    transformed f c α β r t k δ u v = ∑ i, coefficient f c α β r t k i v*
      (Complex.exp (-radius ((α:ℂ)*r^2) u v)*quotient δ (radius ((α:ℂ)*r^2) u v)^(f.degree i)) := by
  simp only [transformed,KFCausalClusteredWidthProfiles.laplaceSum_exact _ δ hδ]

theorem transformed_tendsto (u : Block 2) (v : Block 4) :
    Tendsto (fun δ => transformed f c α β r t k δ u v) (𝓝[>] 0)
      (𝓝 (limitTransformed f c α β r t k u v)) :=
  tendsto_finset_sum _ (fun i _ =>
    (KFCausalClusteredWidthProfiles.laplaceSum_tendsto (f.degree i) (radius ((α:ℂ)*r^2) u v)).const_mul _)

theorem transformed_bound (hA : 0 ≤ ((α:ℂ)*r^2).re) (δ : ℝ) (hδ : 0 < δ)
    (u : Block 2) (v : Block 4) :
    ‖transformed f c α β r t k δ u v‖ ≤ ∑ i, ‖coefficient f c α β r t k i v‖*
      (Real.exp (-(radius ((α:ℂ)*r^2) u v).re)*‖radius ((α:ℂ)*r^2) u v‖^(f.degree i)) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (KFCausalClusteredWidthProfiles.laplaceSum_norm_le (f.degree i) δ hδ _
      (radius_re_nonnegative _ hA u v)) (norm_nonneg _)

theorem actual_slice (c₀ : ℝ → Fin m → ℂ) (ε y z δ s : ℝ) (u : Block 2) (v : Block 4) :
    KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f c₀ α β ε y z k δ (s,reconstruct u v) =
      slice f (c₀ s) α β (KFCausalClockFloorRelativeShift.scale ε y s)
        (KFCausalClockFloorRelativeShift.scale ε z s) k δ v u := by
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

#print axioms fourier_finite_sum
#print axioms fourier_mul_left
#print axioms slice_fourier
#print axioms transformed_exact
#print axioms transformed_tendsto
#print axioms transformed_bound
#print axioms actual_slice
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowProfiles
