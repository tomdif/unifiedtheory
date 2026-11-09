/- The canonical physical score family indexed by every link and every
Haar rotation. Its collective quadratic estimate now matches the actual
Haar refresh lower bound, without a finite-sampling or channel-count loss. -/
import UnifiedTheory.Clay.YangMills.CompactHaarFrame
import UnifiedTheory.Clay.YangMills.WilsonPhysicalGram
import UnifiedTheory.Clay.YangMills.WilsonHaarLinkResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalHaarFrame
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonSymmetricLinkChange WilsonHaarLinkResponse
open WilsonDissipationIteration CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def family (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (e : SpatialVertex n × Fin 3) (z : Q × Slice n) : ℝ :=
  WilsonPhysicalScore.score n β hβ u (shift n e z.1 u) z.2

theorem family_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (e : SpatialVertex n × Fin 3) : Continuous (family n β hβ u e) := by
  have hs : Continuous (fun z : Q × Slice n => shift n e z.1 u) :=
    (shift_joint_continuous n e).comp (continuous_fst.prodMk continuous_const)
  exact (((WilsonHeatBathComparison.transitionMap n β hβ).continuous.comp
    (hs.prodMk continuous_snd)).div
    ((WilsonPhysicalScore.transition_continuous n β hβ u).comp continuous_snd)
      (fun z => (WilsonGroundLocalComparison.transition_pos n β hβ u z.2).ne')).sub continuous_const

def mixture (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : Slice n → ℝ :=
  CompactHaarFrame.mixture (RegulatedGauge.compactHaar Q) (family n β hβ u) a

theorem mixture_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : Continuous (mixture n β hβ u a) :=
  CompactHaarFrame.mixture_continuous _ _ (family_continuous n β hβ u) a

theorem mixture_gauge (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) (h : SliceGauge n Q) (v : Slice n) :
    mixture n β hβ u a (gaugeSlice h v) = mixture n β hβ u a v := by
  simp only [mixture, CompactHaarFrame.mixture, family, WilsonPhysicalScore.score_gauge]

def form (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : ℝ :=
  ∫ v, (mixture n β hβ u a v)^2 ∂rowLaw n β hβ u

theorem form_nonneg (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : 0 ≤ form n β hβ u a :=
  integral_nonneg (fun v => sq_nonneg (mixture n β hβ u a v))

/-- An exact full-Haar physical pairing, with no discretization of rotations. -/
theorem mixture_pairing (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ))
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, mixture n β hβ u a v*f v ∂rowLaw n β hβ u) =
      ∑ e, ∫ q, a e q*(step n β hβ f (shift n e q u)-step n β hβ f u)
        ∂RegulatedGauge.compactHaar Q := by
  letI := rowLaw_probability n β hβ u
  rw [mixture, CompactHaarFrame.mixture_pairing _ _ _ (family_continuous n β hβ u)
    a f f.continuous]
  simp only [CompactHaarFrame.pairing, family, WilsonPhysicalScore.score_pairing n β hβ u _ f hinv]

/-- The quadratic hypothesis is for continuous mixtures of all Haar rotations. -/
theorem conditional_collective (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hform : ∀ a : (SpatialVertex n × Fin 3) → C(Q, ℝ),
      form n β hβ u a ≤ κ * CompactHaarFrame.size (RegulatedGauge.compactHaar Q) a)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∑ e, ∫ q, (step n β hβ f (shift n e q u)-step n β hβ f u)^2
      ∂RegulatedGauge.compactHaar Q) ≤ κ * rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  have h := CompactHaarFrame.response_le (RegulatedGauge.compactHaar Q)
    (rowLaw n β hβ u) (family n β hβ u) (family_continuous n β hβ u)
    f f.continuous κ hκ hform
  simpa only [CompactHaarFrame.pairing, family,
    WilsonPhysicalScore.score_response n β hβ u _ f hinv] using h

theorem local_energy_continuous (e : SpatialVertex n × Fin 3) (f : C(Slice n, ℝ)) :
    Continuous (fun u : Slice n => ∫ q, (f (shift n e q u)-f u)^2
      ∂RegulatedGauge.compactHaar Q) :=
  GibbsMarginalTower.fiber_integral_continuous (RegulatedGauge.compactHaar Q) _
    ((((f.continuous.comp (shift_joint_continuous n e)).comp continuous_swap).sub
      (f.continuous.comp continuous_fst)).pow 2)

/-- This is exactly the total response energy in the Haar lower bound. -/
theorem energy_integral (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    totalEnergy n β hβ f =
      ∫ u, ∑ e, ∫ q, (f (shift n e q u)-f u)^2 ∂RegulatedGauge.compactHaar Q
        ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  rw [integral_finset_sum _ (fun e _ => continuous_integrable _ _
    (local_energy_continuous n e f))]
  apply Finset.sum_congr rfl
  intro e _
  have hc : Continuous (fun z : Q × Slice n => (f (shift n e z.1 z.2)-f z.2)^2) :=
    ((f.continuous.comp (shift_joint_continuous n e)).sub
      (f.continuous.comp continuous_snd)).pow 2
  exact integral_integral_swap (f := fun q u => (f (shift n e q u)-f u)^2)
    (continuous_integrable ((RegulatedGauge.compactHaar Q).prod
      (WilsonGroundHeatBath.groundLaw n β hβ)) _ hc)

theorem energy_le_loss (β : ℝ) (hβ : 0 ≤ β) (κ : ℝ) (hκ : 0 ≤ κ)
    (hform : ∀ u (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)),
      form n β hβ u a ≤ κ * CompactHaarFrame.size (RegulatedGauge.compactHaar Q) a)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    totalEnergy n β hβ (step n β hβ f) ≤ κ * loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  rw [energy_integral]
  have hl : Continuous (fun u : Slice n => ∑ e, ∫ q,
      (step n β hβ f (shift n e q u)-step n β hβ f u)^2 ∂RegulatedGauge.compactHaar Q) :=
    continuous_finset_sum _ (fun e _ => local_energy_continuous n e (step n β hβ f))
  have h := integral_mono (continuous_integrable _ _ hl)
    ((continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (rowVariance_continuous n β hβ f)).const_mul κ)
    (fun u => conditional_collective n β hβ u κ hκ (hform u) f hinv)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

theorem time_sum_le_loss (β : ℝ) (hβ : 0 ≤ β) (κ : ℝ) (hκ : 0 ≤ κ)
    (hform : ∀ u (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)),
      form n β hβ u a ≤ κ * CompactHaarFrame.size (RegulatedGauge.compactHaar Q) a)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) (k : ℕ) :
    (∑ j ∈ Finset.range k, totalEnergy n β hβ (flow n β hβ f (j+1))) ≤
      κ*(variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, κ * loss n β hβ (flow n β hβ f j) :=
      Finset.sum_le_sum (fun j _ => energy_le_loss n β hβ κ hκ hform _
        (flow_gauge n β hβ f hinv j))
    _ = _ := by rw [← Finset.mul_sum, loss_telescope]

/-- The collective Haar estimate and the existing Haar lower comparison now
use exactly the same family. Both remaining analytic hypotheses are explicit. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hfactor : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalConditionalVariance n β hβ F)
    (hform : ∀ u (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)),
      form n β hβ u a ≤ κ * CompactHaarFrame.size (RegulatedGauge.compactHaar Q) a)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (flow n β hβ f k) ≤
      (A*κ/((k : ℝ)+A*κ))*variance n β hβ f :=
  WilsonHaarLinkResponse.slab_contraction n β hβ A κ hA hκ hfactor
    (fun F hF => energy_le_loss n β hβ κ hκ hform F hF) f hinv k hk

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalHaarFrame
