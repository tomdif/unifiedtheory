/- Actual block-supported L2 decay with exterior normalization canceled.
The remaining factors are the internal block mass and the crossing boundary. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutDecay
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonGroundHeatBath WilsonPhysicalVariance WilsonHighFieldDecay WilsonTemporalGauge
open WilsonSpatialCutEnergy WilsonSpatialCutKernel WilsonSpatialCutCap
open CompactKernelOperator CompactKernelProductComparison WilsonPositiveGroundState
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def source (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) : C(Coordinates n S, ℝ) :=
  ⟨fun z => ground n β hβ (WilsonBlockMarginal.assemble S z)*f (WilsonBlockMarginal.assemble S z),
    ((ground n β hβ).continuous.mul f.continuous).comp (WilsonBlockMarginal.assemble_continuous S)⟩

theorem source_norm (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) :
    ‖ContinuousMap.toLp 2 ((outsideHaar n S).prod (insideHaar n S)) ℂ
      (complexify (source n β hβ S f))‖^2 = mass n β hβ f := by
  rw [real_embedding_norm_sq, mass_ground]
  exact (WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)).integral_comp
    (WilsonBlockMarginal.assemble S).measurableEmbedding (fun u => (ground n β hβ u*f u)^2)

theorem source_output (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) (z : Coordinates n S) :
    realSmoothing ((outsideHaar n S).prod (insideHaar n S)) (full n β S)
      (source n β hβ S f) z = ‖transfer n β‖*source n β hβ S (step n β hβ f) z := by
  rw [realSmoothing_integral]
  have hp :=
    (WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)).integral_comp
    (WilsonBlockMarginal.assemble S).measurableEmbedding
    (fun v => rawKernel character β 2 (WilsonBlockMarginal.assemble S z) v*ground n β hβ v*f v)
  have he : (∫ w, full n β S (z,w)*source n β hβ S f w
      ∂(outsideHaar n S).prod (insideHaar n S)) =
      ∫ v, rawKernel character β 2 (WilsonBlockMarginal.assemble S z) v*ground n β hβ v*f v
        ∂WilsonSlabOperator.measure n := by
    apply Eq.trans _ hp
    apply integral_congr_ae
    filter_upwards with w
    simp only [full, source, ContinuousMap.coe_mk]
    ring
  rw [he]
  have h := (eq_div_iff (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne').mp
    (ground_step n β hβ f (WilsonBlockMarginal.assemble S z))
  change _ = ‖transfer n β‖*(ground n β hβ _*step n β hβ f _)
  linarith

theorem output_norm (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) :
    ‖operator ((outsideHaar n S).prod (insideHaar n S)) (full n β S)
      (ContinuousMap.toLp 2 ((outsideHaar n S).prod (insideHaar n S)) ℂ
        (complexify (source n β hβ S f)))‖^2 =
      ‖transfer n β‖^2*mass n β hβ (step n β hβ f) := by
  change ‖ContinuousMap.toLp 2 ((outsideHaar n S).prod (insideHaar n S)) ℂ
    (smoothing _ (full n β S) (ContinuousMap.toLp 2 _ ℂ (complexify (source n β hβ S f))))‖^2 = _
  rw [← complexify_realSmoothing, real_embedding_norm_sq]
  simp_rw [source_output, mul_pow]
  rw [integral_const_mul, ← real_embedding_norm_sq, source_norm]

theorem full_high (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (z w : Coordinates n S)
    (hw : R ≤ bulkPotential n S (WilsonBlockMarginal.assemble S w)) :
    full n β S (z,w) ≤ Real.exp (-β*R/2)*exterior n β S (z.1,w.1) := by
  have h := piece_high n β hβ S R (WilsonBlockMarginal.assemble S z)
    (WilsonBlockMarginal.assemble S w) hw
  rw [interior_piece] at h
  have hm := mul_le_mul_of_nonneg_left h (piece_pos n β Sᶜ (outsideField n S z.1)
    (outsideField n S w.1)).le
  change exterior n β S (z.1,w.1)*interior n β S (z.2,w.2) ≤
    exterior n β S (z.1,w.1)*Real.exp (-β*R/2) at hm
  exact (cut_upper n β hβ S z w).trans (hm.trans_eq (mul_comm _ _))

/-- Every outside variable remains in the source. No product source law is assumed. -/
theorem input_bound (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (f : C(Slice n, ℝ)) (hs : ∀ u, bulkPotential n S u < R → f u = 0) :
    ‖operator ((outsideHaar n S).prod (insideHaar n S)) (full n β S)
      (ContinuousMap.toLp 2 ((outsideHaar n S).prod (insideHaar n S)) ℂ
        (complexify (source n β hβ S f)))‖ ≤
      Real.exp (-β*R/2)*‖operator (outsideHaar n S) (exterior n β S)‖*
      ‖ContinuousMap.toLp 2 ((outsideHaar n S).prod (insideHaar n S)) ℂ
        (complexify (source n β hβ S f))‖ := by
  have hd := CompactKernelDomination.input_domination
    ((outsideHaar n S).prod (insideHaar n S)) (full n β S)
    (productKernel (Y := Inside n S) (exterior n β S) 1)
    (Real.exp (-β*R/2)) (Real.exp_pos _).le (complexify (source n β hβ S f)) (fun z w => by
      by_cases hw : R ≤ bulkPotential n S (WilsonBlockMarginal.assemble S w)
      · have h := mul_le_mul_of_nonneg_right (full_high n β hβ S R z w hw)
          (norm_nonneg (complexify (source n β hβ S f) w))
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show 0 < full n β S (z,w) from rawKernel_pos _ _ _ _ _),
          productKernel, ContinuousMap.coe_mk, ContinuousMap.one_apply, mul_one] using h
      · have hf := hs _ (lt_of_not_ge hw)
        simp only [source, complexify, ContinuousMap.coe_mk, hf, mul_zero,
          Complex.ofReal_zero, norm_zero, le_refl])
  have hn := lifted_norm_le (outsideHaar n S) (insideHaar n S) (exterior n β S)
    (fun _ _ => (piece_pos n β Sᶜ _ _).le)
  exact hd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le) (norm_nonneg _))

/-- The actual block high-field estimate after canceling the entire exterior
normalization. The remaining q is the explicit internal block kernel mass. -/
theorem mass_decay (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (f : C(Slice n, ℝ)) (hs : ∀ u, bulkPotential n S u < R → f u = 0) :
    (insideMass n β S)^2*mass n β hβ (step n β hβ f) ≤
      Real.exp (-β*R+8*β*(boundary n S).card)*mass n β hβ f := by
  let μ := (outsideHaar n S).prod (insideHaar n S)
  let F := ContinuousMap.toLp 2 μ ℂ (complexify (source n β hβ S f))
  let q := insideMass n β S
  let a := Real.exp (-β*R/2)
  let b := Real.exp (4*β*(boundary n S).card)
  have h1 := mul_le_mul_of_nonneg_left (input_bound n β hβ S R f hs) (insideMass_pos n β S).le
  have h2 := mul_le_mul_of_nonneg_right (exterior_normalization n β hβ S)
    (mul_nonneg (Real.exp_pos (-β*R/2)).le (norm_nonneg F))
  have h : q*‖operator μ (full n β S) F‖ ≤ (a*b)*‖transfer n β‖*‖F‖ := by
    change q*‖operator μ (full n β S) F‖ ≤
      q*(a*‖operator (outsideHaar n S) (exterior n β S)‖*‖F‖) at h1
    change (q*‖operator (outsideHaar n S) (exterior n β S)‖)*(a*‖F‖) ≤
      (b*‖transfer n β‖)*(a*‖F‖) at h2
    nlinarith
  have hh := pow_le_pow_left₀ (mul_nonneg (insideMass_pos n β S).le (norm_nonneg _)) h 2
  simp only [mul_pow] at hh
  have ho : ‖operator μ (full n β S) F‖^2 = ‖transfer n β‖^2*mass n β hβ (step n β hβ f) :=
    output_norm n β hβ S f
  have hi : ‖F‖^2 = mass n β hβ f := source_norm n β hβ S f
  rw [ho, hi] at hh
  have he : a^2*b^2 = Real.exp (-β*R+8*β*(boundary n S).card) := by
    dsimp [a,b]
    rw [← mul_pow, ← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1)).mp
  convert hh using 1 <;> ring

/-- Fully numerical block decay. Every constant counts only internal or
crossing plaquettes and block links, never the exterior volume. -/
theorem price_decay (β : ℝ) (hβ : 0 < β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (f : C(Slice n, ℝ)) (hs : ∀ u, bulkPotential n S u < R → f u = 0) :
    mass n β hβ.le (step n β hβ.le f) ≤
      Real.exp (-β*(R-8*(boundary n S).card-
        4 * (((bulk n S).card : ℝ) + S.card) * WilsonGroundSlabEnergy.envelope β))*
          mass n β hβ.le f := by
  let M : ℝ := (bulk n S).card+S.card
  have hq := pow_le_pow_left₀ (Real.exp_pos _).le (insideMass_exp_lower n β hβ S) 2
  have he : (Real.exp (-2*β*M*WilsonGroundSlabEnergy.envelope β))^2 =
      Real.exp (-4*β*M*WilsonGroundSlabEnergy.envelope β) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change (Real.exp (-2*β*M*WilsonGroundSlabEnergy.envelope β))^2 ≤ _ at hq
  rw [he] at hq
  have h := (mul_le_mul_of_nonneg_right hq (mass_nonneg n β hβ.le (step n β hβ.le f))).trans
    (mass_decay n β hβ.le S R f hs)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (-4*β*M*WilsonGroundSlabEnergy.envelope β))).mp
  apply h.trans_eq
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  dsimp [M]
  ring

/-- A positive energy margin above the explicit boundary cost is enough for
weak-coupling decay once the local free-energy price is below half that margin. -/
theorem local_decay (β : ℝ) (hβ : 0 < β) (S : Finset (SpatialVertex n × Fin 3))
    (R ρ : ℝ) (hR : 8 * ((boundary n S).card : ℝ) + ρ ≤ R)
    (he : 4 * (((bulk n S).card : ℝ) + S.card) * WilsonGroundSlabEnergy.envelope β ≤ ρ / 2)
    (f : C(Slice n, ℝ)) (hs : ∀ u, bulkPotential n S u < R → f u = 0) :
    mass n β hβ.le (step n β hβ.le f) ≤ Real.exp (-β*ρ / 2)*mass n β hβ.le f := by
  apply (price_decay n β hβ S R f hs).trans
  apply mul_le_mul_of_nonneg_right _ (mass_nonneg n β hβ.le f)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (show ρ / 2 ≤ R-8*(boundary n S).card-
    4 * (((bulk n S).card : ℝ) + S.card) * WilsonGroundSlabEnergy.envelope β by linarith) hβ.le
  nlinarith

theorem local_loss (β : ℝ) (hβ : 0 < β) (S : Finset (SpatialVertex n × Fin 3))
    (R ρ : ℝ) (hR : 8 * ((boundary n S).card : ℝ) + ρ ≤ R)
    (he : 4 * (((bulk n S).card : ℝ) + S.card) * WilsonGroundSlabEnergy.envelope β ≤ ρ / 2)
    (f : C(Slice n, ℝ)) (hs : ∀ u, bulkPotential n S u < R → f u = 0) :
    (1-Real.exp (-β*ρ / 2))*mass n β hβ.le f ≤ loss n β hβ.le f := by
  rw [loss_mass]
  have h := local_decay n β hβ S R ρ hR he f hs
  linarith

/-- The numerical condition is eventually satisfied for each positive margin;
its parameters depend only on the internal block counts. -/
theorem eventual_price (S : Finset (SpatialVertex n × Fin 3)) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ β : ℝ in Filter.atTop, 0 < β ∧
      4 * (((bulk n S).card : ℝ) + S.card) * WilsonGroundSlabEnergy.envelope β ≤ ρ / 2 := by
  have h := (WilsonGroundSlabEnergy.envelope_tendsto.const_mul
    (4 * (((bulk n S).card : ℝ) + S.card))).eventually
      (eventually_lt_nhds (show (4 * (((bulk n S).card : ℝ) + S.card))*0 < ρ / 2 by linarith))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), h] with β hb he
  exact ⟨hb,he.le⟩

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutDecay
