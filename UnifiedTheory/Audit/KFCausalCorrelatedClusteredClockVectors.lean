/- Construct actual physical L2 vectors for arbitrary independent L2
clock coefficients at zero shift, then derive their clustered limit. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockVectors
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalReciprocalNeutralPhysicalSliceNorm (wave)
open KFCausalReciprocalNeutralSliceIntegrability (factor factor_memLp)
open KFCausalImaginaryShearInitialMultiplier (scale_zero)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β : ℝ)

def profile (δ : ℝ) (x : Configuration) : ℂ :=
  wave (count f) α β (widths f δ) 1
    (coefficients (reweight f (c x.1)) δ) (sources f) (polynomials f) x.2

theorem profile_sum (δ : ℝ) (x : Configuration) : profile f c α β δ x =
    ∑ j, c x.1 (index f j).1*(coefficients f δ j*
      factor α β (widths f δ j) 1 (sources f j) (polynomials f j) 0 x.2) := by
  unfold profile wave
  apply Finset.sum_congr rfl
  intro j _
  change ((f.amplitude (index f j).1*c x.1 (index f j).1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ = _
  unfold coefficients
  ring

theorem profile_transfer (ε : ℝ) (hε : 0 < ε) (δ : ℝ) :
    profile f c α β δ = KFCausalCorrelatedClusteredPhysicalTransfer.represented f c α β ε 0 δ := by
  funext x
  simp only [profile,KFCausalCorrelatedClusteredPhysicalTransfer.represented,scale_zero ε x.1 hε]

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hα hβ hw hc2 in
theorem profile_memLp (δ : ℝ) (hδ : 0 < δ) : MemLp (profile f c α β δ) 2 volume := by
  have hp (j : Fin (count f)) : MemLp (factor α β (widths f δ j) 1 (sources f j) (polynomials f j) 0) 2 volume := by
    have hm := factor_memLp α β 1 0 0 (widths f δ j) hα hβ hw zero_lt_one
      (by simp only [abs_zero]; positivity) (widths_admissible f δ hδ.le j) (sources f j) (polynomials f j) 0
    simpa only [scale_zero 1 0 zero_lt_one] using hm
  have hm := memLp_finset_sum Finset.univ (fun j _ =>
    KFCausalPhysicalGaussianDerivative.configuration_product_memLp _ _ (hc2 (index f j).1)
      ((hp j).const_mul (coefficients f δ j)))
  exact hm.ae_eq (Filter.Eventually.of_forall (fun x => (profile_sum f c α β δ x).symm))

def vector (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  (profile_memLp f c α β hα hβ hw hc2 δ hδ).toLp (profile f c α β δ) else 0

theorem vector_coe (δ : ℝ) (hδ : 0 < δ) :
    vector f c α β hα hβ hw hc2 δ =ᵐ[volume] profile f c α β δ := by
  rw [vector,dif_pos hδ]
  exact MemLp.coeFn_toLp _

variable (hc : ∀ i, Continuous (fun s => c s i))

include hc in
theorem vector_exists_limit : ∃ v : Hilbert,
    Tendsto (vector f c α β hα hβ hw hc2) (𝓝[>] 0) (𝓝 v) := by
  apply KFCausalCorrelatedClusteredPhysicalTransfer.exists_limit f c α β 1 0 hα hβ hw zero_lt_one
    (by simp only [abs_zero]; positivity) hc hc2 _
  intro δ hδ
  rw [← profile_transfer f c α β 1 zero_lt_one δ]
  exact vector_coe f c α β hα hβ hw hc2 δ hδ

def limitingVector : Hilbert := Classical.choose (vector_exists_limit f c α β hα hβ hw hc2 hc)

theorem vector_tendsto : Tendsto (vector f c α β hα hβ hw hc2) (𝓝[>] 0)
    (𝓝 (limitingVector f c α β hα hβ hw hc2 hc)) :=
  Classical.choose_spec (vector_exists_limit f c α β hα hβ hw hc2 hc)

#print axioms profile_sum
#print axioms profile_transfer
#print axioms profile_memLp
#print axioms vector_coe
#print axioms vector_exists_limit
#print axioms vector_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockVectors
