/- A direct Haar coercivity constant is constrained by the actual local
plaquette variance. This does not assume heat-bath factorization, and the
Haar refresh is not treated as stationary for the ground law. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteVarianceFloor
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalBudget
import UnifiedTheory.Clay.YangMills.WilsonNormalizedResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDirectHaarBudget
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance
open WilsonSymmetricLinkChange WilsonHaarLinkResponse WilsonGroundLocalBudget
open WilsonPlaquetteTransport WilsonDissipationIteration CompactDensityEntropy

variable (n : ℕ) [NeZero n]

theorem response_zero (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hsupport : ∀ u v : Slice n, (∀ j ∈ T, u j = v j) → f u = f v)
    (e : SpatialVertex n × Fin 3) (he : e ∉ T) (q : Q) :
    responseEnergy n β hβ e q f = 0 := by
  have hf (u : Slice n) : f (shift n e q u) = f u := by
    apply hsupport
    intro j hj
    exact shift_away n e q u j (fun h => he (h ▸ hj))
  simp only [responseEnergy, hf, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]

theorem response_oscillation_bound (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ u v, |f u - f v| ≤ M)
    (e : SpatialVertex n × Fin 3) (q : Q) : responseEnergy n β hβ e q f ≤ M^2 := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  have hp (u : Slice n) : (f (shift n e q u)-f u)^2 ≤ M^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb (shift n e q u) u)
  have h := integral_mono
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (((f.continuous.comp (shift_continuous n e q)).sub f.continuous).pow 2))
    (integrable_const (M^2)) hp
  simpa only [responseEnergy, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem supported_total_le (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hsupport : ∀ u v : Slice n, (∀ j ∈ T, u j = v j) → f u = f v)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ u v, |f u - f v| ≤ M) :
    totalEnergy n β hβ f ≤ (T.card : ℝ)*M^2 := by
  classical
  have hz (e : SpatialVertex n × Fin 3) (he : e ∉ T) :
      (∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q) = 0 := by
    simp only [response_zero n β hβ T f hsupport e he, integral_zero]
  have hs : (∑ e ∈ T, ∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q) =
      totalEnergy n β hβ f :=
    Finset.sum_subset (Finset.subset_univ T) (fun e _ he => hz e he)
  have he (e : SpatialVertex n × Fin 3) :
      (∫ q, responseEnergy n β hβ e q f ∂RegulatedGauge.compactHaar Q) ≤ M^2 := by
    have h := integral_mono (continuous_integrable (RegulatedGauge.compactHaar Q) _
      (responseEnergy_continuous n β hβ e f)) (integrable_const (M^2))
      (response_oscillation_bound n β hβ f M hM hb e)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  rw [← hs]
  calc
    _ ≤ ∑ _e ∈ T, M^2 := Finset.sum_le_sum (fun e _ => he e)
    _ = _ := by simp

theorem plaquette_total_le (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (i j : Fin 3) :
    totalEnergy n β hβ (plaquette n x i j) ≤ 64 := by
  have hb (u : Slice n) : |plaquette n x i j u| ≤ 2 :=
    (Complex.abs_re_le_norm _).trans (WilsonGroundLocalComparison.character_bound _)
  have ho (u v : Slice n) : |plaquette n x i j u-plaquette n x i j v| ≤ 4 :=
    (abs_sub _ _).trans (by linarith [hb u, hb v])
  have h := supported_total_le n β hβ (plaquetteSupport n x i j) (plaquette n x i j)
    (plaquette_supported n x i j) 4 (by norm_num) ho
  have hc : ((plaquetteSupport n x i j).card : ℝ) ≤ 4 :=
    by exact_mod_cast plaquetteSupport_card n x i j
  nlinarith

/-- A direct Haar lower estimate yields the same time gain, without heat-bath factorization. -/
theorem slab_lower (β : ℝ) (hβ : 0 ≤ β) (A : ℝ)
    (hcoerce : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalEnergy n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U) (k : ℕ) :
    (k : ℝ)*variance n β hβ (flow n β hβ f k) ≤
      A*∑ j ∈ Finset.range k, totalEnergy n β hβ (flow n β hβ f (j+1)) := by
  have h := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range k) =>
    ((variance_flow_antitone n β hβ f)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans
        (hcoerce _ (flow_gauge n β hβ f hinv (j+1))))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] using h

theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hcoerce : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalEnergy n β hβ F)
    (hupper : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      totalEnergy n β hβ (step n β hβ F) ≤ κ * loss n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (flow n β hβ f k) ≤
      (A*κ/((k : ℝ)+A*κ))*variance n β hβ f := by
  have hu : (∑ j ∈ Finset.range k, totalEnergy n β hβ (flow n β hβ f (j+1))) ≤
      κ*(variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, κ*loss n β hβ (flow n β hβ f j) :=
        Finset.sum_le_sum (fun j _ => hupper _ (flow_gauge n β hβ f hinv j))
      _ = _ := by rw [← Finset.mul_sum, loss_telescope]
  have h := (slab_lower n β hβ A hcoerce f hinv k).trans (mul_le_mul_of_nonneg_left hu hA)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ)+A*κ)).mpr
  nlinarith

theorem explicit_slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hcoerce : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalEnergy n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (flow n β hβ f k) ≤
      (A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*WilsonNormalizedResponse.haarCap β) /
        ((k : ℝ)+A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*
          WilsonNormalizedResponse.haarCap β)))*variance n β hβ f :=
  slab_contraction n β hβ A _ hA
    (mul_nonneg (Nat.cast_nonneg _) (WilsonNormalizedResponse.haarCap_nonneg β))
    hcoerce (fun F _ => WilsonNormalizedResponse.total_upper n β hβ F) f hinv k hk

variable [Fact (1 < n)]

/-- A direct Haar constant cannot shrink faster than this polynomial ground-law budget. -/
theorem coercivity_budget (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hcoerce : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * totalEnergy n β hβ F) :
    1 ≤ 1536*(Real.exp 36+1)*(β+1)^4*A := by
  have h := (WilsonPlaquetteVarianceFloor.variance_lower n β hβ 0 0 1 (by decide)).trans
    ((hcoerce _ (plaquette_gauge n 0 0 1)).trans
      (mul_le_mul_of_nonneg_left (plaquette_total_le n β hβ 0 0 1) hA))
  have hc := (div_le_iff₀ (by positivity : 0 < 24*(Real.exp 36+1)*(β+1)^4)).mp h
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonDirectHaarBudget
