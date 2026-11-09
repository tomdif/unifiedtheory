/- Unrestricted interior covariance bounds with the actual cap-complement
probability. No estimate on that probability or spatial decay is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchConditioning

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchCovarianceTransfer
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected
open WilsonSpatialCutEnergy WilsonChordPatchLaw WilsonPatchConditioning GibbsCrossCovariance
open scoped Quaternion

variable (n : ℕ)

def goodMass (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (A : Slice n → ℝ) : ℝ := (interiorLaw n S v₀ A).real (event n S v₀ ε)

def badMass (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (A : Slice n → ℝ) : ℝ := (interiorLaw n S v₀ A).real (event n S v₀ ε)ᶜ

theorem mass_partition (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (A : Slice n → ℝ) (hA : Continuous A) :
    goodMass n S v₀ ε A + badMass n S v₀ ε A = 1 := by
  letI := interior_probability n S v₀ A hA
  exact GibbsEventCovariance.mass_partition _ _ (event_measurable n S v₀ ε)

theorem covariance_transfer (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A F G : Slice n → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ v, |F v| ≤ 2) (hGb : ∀ v, |G v| ≤ 2) (B : ℝ)
    (hcap : |covariance (law n S v₀ ε A)
      (F ∘ assemble n S v₀ ε) (G ∘ assemble n S v₀ ε)| ≤ B) :
    |covariance (interiorLaw n S v₀ A) (F ∘ insert n S v₀) (G ∘ insert n S v₀)| ≤
      goodMass n S v₀ ε A * B + 4 * badMass n S v₀ ε A +
        16 * goodMass n S v₀ ε A * badMass n S v₀ ε A := by
  letI := interior_probability n S v₀ A hA
  have hh := GibbsEventCovariance.bounded_source_transfer (interiorLaw n S v₀ A)
    (event n S v₀ ε) (event_measurable n S v₀ ε) (F ∘ insert n S v₀) (G ∘ insert n S v₀)
    (hF.comp (insert_continuous n S v₀)) (hG.comp (insert_continuous n S v₀))
    (fun x => hFb _) (fun x => hGb _)
  rw [conditioned_covariance n S v₀ ε hε A hA F G] at hh
  have hb := mul_le_mul_of_nonneg_left hcap
    (measureReal_nonneg : 0 ≤ (interiorLaw n S v₀ A).real (event n S v₀ ε))
  change _ ≤ goodMass n S v₀ ε A * _ + 4 * badMass n S v₀ ε A +
    16 * goodMass n S v₀ ε A * badMass n S v₀ ε A at hh
  change goodMass n S v₀ ε A * _ ≤ goodMass n S v₀ ε A * B at hb
  linarith only [hh, hb]

theorem covariance_transfer_coarse (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A F G : Slice n → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ v, |F v| ≤ 2) (hGb : ∀ v, |G v| ≤ 2) (B : ℝ)
    (hcap : |covariance (law n S v₀ ε A)
      (F ∘ assemble n S v₀ ε) (G ∘ assemble n S v₀ ε)| ≤ B) :
    |covariance (interiorLaw n S v₀ A) (F ∘ insert n S v₀) (G ∘ insert n S v₀)| ≤
      B + 20 * badMass n S v₀ ε A := by
  have hh := covariance_transfer n S v₀ ε hε A F G hA hF hG hFb hGb B hcap
  have hpart := mass_partition n S v₀ ε A hA
  have hd : 0 ≤ badMass n S v₀ ε A := measureReal_nonneg
  have hB : 0 ≤ B := (abs_nonneg _).trans hcap
  have hp : goodMass n S v₀ ε A ≤ 1 := by linarith
  have hb := mul_le_mul_of_nonneg_right hp hB
  have hm := mul_le_mul_of_nonneg_right hp hd
  nlinarith only [hh, hb, hm]

variable [NeZero n]

theorem connected_bound (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    |covariance (interiorLaw n S v₀ (WilsonTiltedMiddleAction.action n β u w e d q r s t))
      (source n β e q u ∘ insert n S v₀) (source n β d r u ∘ insert n S v₀)| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 1) +
        20 * badMass n S v₀ (1 / 256) (WilsonTiltedMiddleAction.action n β u w e d q r s t) := by
  apply covariance_transfer_coarse n S v₀ (1 / 256) (by norm_num) _ _ _
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (source_continuous n β e q u) (source_continuous n β d r u)
  · intro v
    have hh := source_bound n β (by linarith) e q u v
    nlinarith only [hh, hq]
  · intro v
    have hh := source_bound n β (by linarith) d r u v
    nlinarith only [hh, hr]
  · exact WilsonPatchCovariance.connected_bound n β hβ u w e d hed q r hq hr
      s t hs ht S v₀ hflat hu hw

theorem transport_connected_bound (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ z c, c ∈ S → c ∈ support n z →
      ‖((spatialHolonomy v₀ z.1 z.2.1.1 z.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ c ∈ S, ‖(v₀ c : ℍ) - (u c : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ c ∈ S, ‖(v₀ c : ℍ) - (w c : ℍ)‖ ≤ 1 / 2) :
    |covariance (interiorLaw n S v₀ (CompactGibbsSource.action
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h))
      (source n β e q u ∘ insert n S v₀) (source n β b p w ∘ insert n S v₀)| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 2) +
        20 * badMass n S v₀ (1 / 256) (CompactGibbsSource.action
          (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h) := by
  apply covariance_transfer_coarse n S v₀ (1 / 256) (by norm_num) _ _ _
    (CompactGibbsSource.action_continuous _ _
      (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
      (source_continuous n β b p w) h)
    (source_continuous n β e q u) (source_continuous n β b p w)
  · intro v
    have hb := source_bound n β (by linarith) e q u v
    nlinarith only [hb, hq]
  · intro v
    have hb := source_bound n β (by linarith) b p w v
    nlinarith only [hb, hp]
  · exact WilsonPatchCovariance.transport_connected_bound n β hβ u w e d b hed
      q r p hq hr hp s t h hs ht hh S v₀ hflat hu hw

end
end UnifiedTheory.Clay.YangMills.WilsonPatchCovarianceTransfer
