/- Positive-form estimates comparing two regularized trajectories.
The error is controlled by their actual velocity energies. -/
import UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth
import UnifiedTheory.Audit.KFCausalQuasiResolventVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeightedCauchyPairing
noncomputable section
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
open UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth (energy_sub_bound)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem negative_young (W : V →L[ℂ] V) (hW : W.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy W x) (e v : V) (δ : ℝ) :
    -2*δ*(inner ℂ e (W v)).re ≤ energy W e+δ^2*energy W v := by
  have he := KFCausalQuasiDissipativeResolvent.energy_sub_real W hW e v (-δ)
  have hpos := hp (e-(-δ) • v)
  have hs : (inner ℂ v (W e)).re = (inner ℂ e (W v)).re :=
    (inner_re_symm (𝕜 := ℂ) v (W e)).trans (congrArg Complex.re (hW e v))
  rw [hs] at he
  nlinarith only [he,hpos]

theorem error_energy (W : V →L[ℂ] V) (hW : W.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy W x) (v z : V) (p q M : ℝ)
    (hp₀ : 0 ≤ p) (hq₀ : 0 ≤ q) (hM : 0 ≤ M)
    (hv : energy W v ≤ M) (hz : energy W z ≤ M) :
    energy W (p • v-q • z) ≤ 2*M*(p+q)^2 := by
  have he := energy_sub_bound W hW hp (p • v) (q • z)
  rw [energy_real_smul,energy_real_smul] at he
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg p)
  have hz' := mul_le_mul_of_nonneg_left hz (sq_nonneg q)
  have hm := mul_nonneg hM (mul_nonneg hp₀ hq₀)
  nlinarith only [he,hv',hz',hm]

theorem velocity_difference_energy (W : V →L[ℂ] V) (hW : W.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy W x) (v z : V) (M : ℝ)
    (hv : energy W v ≤ M) (hz : energy W z ≤ M) : energy W (v-z) ≤ 4*M := by
  have he := energy_sub_bound W hW hp v z
  linarith

theorem difference_pairing (W : V →L[ℂ] V) (hW : W.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy W x) (d u e v : V) (ω M δ : ℝ)
    (hω : 0 ≤ ω) (hM : 0 ≤ M) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hd : d = u-e) (he : energy W e ≤ 2*M*δ^2) (hv : energy W v ≤ 4*M)
    (hq : (inner ℂ u (W v)).re ≤ ω*energy W u) :
    2*(inner ℂ d (W v)).re ≤ 4*ω*energy W d+(6+8*ω)*M*δ := by
  have hy := negative_young W hW hp e v δ
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg δ)
  have hcross : -2*(inner ℂ e (W v)).re ≤ 6*M*δ := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    nlinarith only [hy,hv',he]
  have hu := energy_sub_bound W hW hp d (-e)
  have hde : d-(-e)=u := by rw [hd]; abel
  have hneg : energy W (-e) = energy W e := by
    simp only [energy,map_neg,inner_neg_left,inner_neg_right,neg_neg]
  rw [hde,hneg] at hu
  have hu' := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2*ω by positivity)
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*ω by positivity)
  have hsmall : δ^2 ≤ δ := by nlinarith only [hδ,hδ₁]
  have hs := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 8*ω*M by positivity)
  have hpair : (inner ℂ d (W v)).re = (inner ℂ u (W v)).re-(inner ℂ e (W v)).re := by
    rw [hd,inner_sub_left,Complex.sub_re]
  nlinarith only [hpair,hq,hcross,hu',he',hs]

theorem regularized_pairing_of_bound (W : V →L[ℂ] V)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (ω M p q : ℝ) (hω : 0 ≤ ω) (hM : 0 ≤ M) (hp₀ : 0 ≤ p) (hq₀ : 0 ≤ q)
    (hsum : 0 < p+q) (hsum₁ : p+q ≤ 1)
    (x y u z v w : V) (hex : u-x = p • v) (hey : z-y = q • w)
    (hv : energy W v ≤ M) (hw : energy W w ≤ M)
    (hquasi : (inner ℂ (u-z) (W (v-w))).re ≤ ω*energy W (u-z)) :
    2*(inner ℂ (x-y) (W (v-w))).re ≤ 4*ω*energy W (x-y)+(6+8*ω)*M*(p+q) := by
  apply difference_pairing W hW hp (x-y) (u-z) (p • v-q • w) (v-w) ω M (p+q)
    hω hM hsum hsum₁
  · rw [← hex,← hey]
    abel
  · exact error_energy W hW hp v w p q M hp₀ hq₀ hM hv hw
  · exact velocity_difference_energy W hW hp v w M hv hw
  · exact hquasi

theorem complex_regularized_pairing (W : V →L[ℂ] V)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (ω M p q : ℝ) (hω : 0 ≤ ω) (hM : 0 ≤ M) (hp₀ : 0 ≤ p) (hq₀ : 0 ≤ q)
    (hsum : 0 < p+q) (hsum₁ : p+q ≤ 1)
    (x y u z v w : V) (hex : u-x = (p:ℂ) • v) (hey : z-y = (q:ℂ) • w)
    (hv : energy W v ≤ M) (hw : energy W w ≤ M)
    (hquasi : (inner ℂ (u-z) (W (v-w))).re ≤ ω*energy W (u-z)) :
    2*(inner ℂ (x-y) (W (v-w))).re ≤ 4*ω*energy W (x-y)+(6+8*ω)*M*(p+q) := by
  simp only [Complex.coe_smul] at hex hey
  exact regularized_pairing_of_bound W hW hp ω M p q hω hM hp₀ hq₀ hsum hsum₁
    x y u z v w hex hey hv hw hquasi

theorem pairing_at_output (W : V →L[ℂ] V)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (ω M p q : ℝ) (hω : 0 ≤ ω) (hM : 0 ≤ M) (hp₀ : 0 ≤ p) (hq₀ : 0 ≤ q)
    (hsum : 0 < p+q) (hsum₁ : p+q ≤ 1)
    (x y u z v w d j k : V) (hd : d = x-y) (hj : j = v-w) (hk : k = u-z)
    (hex : u-x = (p:ℂ) • v) (hey : z-y = (q:ℂ) • w)
    (hv : energy W v ≤ M) (hw : energy W w ≤ M)
    (hquasi : (inner ℂ k (W j)).re ≤ ω*energy W k) :
    2*(inner ℂ d (W j)).re ≤ 4*ω*energy W d+(6+8*ω)*M*(p+q) := by
  simpa only [hd,hj] using complex_regularized_pairing W hW hp ω M p q hω hM hp₀ hq₀ hsum hsum₁
    x y u z v w hex hey hv hw (by simpa only [hk,hj] using hquasi)

theorem regularized_pairing (T : V →ₗ.[ℂ] V) (W : V →L[ℂ] V)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (ω M p q : ℝ) (hω : 0 ≤ ω) (hM : 0 ≤ M) (hp₀ : 0 ≤ p) (hq₀ : 0 ≤ q)
    (hsum : 0 < p+q) (hsum₁ : p+q ≤ 1)
    (hquasi : ∀ x y, (x,y) ∈ T.graph → (inner ℂ x (W y)).re ≤ ω*energy W x)
    (x y u z v w : V) (hu : (u,v) ∈ T.graph) (hz : (z,w) ∈ T.graph)
    (hex : u-x = p • v) (hey : z-y = q • w)
    (hv : energy W v ≤ M) (hw : energy W w ≤ M) :
    2*(inner ℂ (x-y) (W (v-w))).re ≤ 4*ω*energy W (x-y)+(6+8*ω)*M*(p+q) := by
  apply difference_pairing W hW hp (x-y) (u-z) (p • v-q • w) (v-w) ω M (p+q)
    hω hM hsum hsum₁
  · rw [← hex,← hey]
    abel
  · exact error_energy W hW hp v w p q M hp₀ hq₀ hM hv hw
  · exact velocity_difference_energy W hW hp v w M hv hw
  · exact hquasi _ _ (T.graph.sub_mem hu hz)

theorem reciprocal_parameters (b c : ℝ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    0 < 1/b+1/c ∧ 1/b+1/c ≤ 1 := by
  have hb₀ : 0 < b := by linarith
  have hc₀ : 0 < c := by linarith
  have h₁ := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hb
  have h₂ := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hc
  exact ⟨by positivity,by linarith⟩

theorem pairing_transfer (W F S : V →L[ℂ] V) (x v : V) (ω M δ : ℝ)
    (hp : inner ℂ x (W v) = inner ℂ (S x) (F (S v)))
    (he : energy W x = energy F (S x))
    (hb : 2*(inner ℂ x (W v)).re ≤ 4*ω*energy W x+(6+8*ω)*M*δ) :
    2*(inner ℂ (S x) (F (S v))).re ≤ 4*ω*energy F (S x)+(6+8*ω)*M*δ := by
  simpa only [hp,he] using hb

theorem resolvent_pairing (T : V →ₗ.[ℂ] V) (W R Q A B : V →L[ℂ] V)
    (b c ω M : ℝ) (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hω : 0 ≤ ω) (hM : 0 ≤ M)
    (hA : A = b • (b • R-1)) (hB : B = c • (c • Q-1))
    (hR : ∀ f, (R f,b • R f-f) ∈ T.graph) (hQ : ∀ f, (Q f,c • Q f-f) ∈ T.graph)
    (hquasi : ∀ x y, (x,y) ∈ T.graph → (inner ℂ x (W y)).re ≤ ω*energy W x)
    (x y : V) (hx : energy W (A x) ≤ M) (hy : energy W (B y) ≤ M) :
    2*(inner ℂ (x-y) (W (A x-B y))).re ≤ 4*ω*energy W (x-y)+(6+8*ω)*M*(1/b+1/c) := by
  have hb₀ : 0 < b := by linarith
  have hc₀ : 0 < c := by linarith
  have hsum := reciprocal_parameters b c hb hc
  exact regularized_pairing T W hW hp ω M (1/b) (1/c) hω hM (by positivity) (by positivity)
    hsum.1 hsum.2 hquasi x y (b • R x) (c • Q y) (A x) (B y)
    (KFCausalQuasiResolventVelocity.smoothed_graph T R A b hA hR x)
    (KFCausalQuasiResolventVelocity.smoothed_graph T Q B c hB hQ y)
    (KFCausalQuasiResolventVelocity.smoothed_error R A b (ne_of_gt hb₀) hA x)
    (KFCausalQuasiResolventVelocity.smoothed_error Q B c (ne_of_gt hc₀) hB y) hx hy

#print axioms negative_young
#print axioms error_energy
#print axioms velocity_difference_energy
#print axioms difference_pairing
#print axioms pairing_at_output
#print axioms complex_regularized_pairing
#print axioms regularized_pairing_of_bound
#print axioms regularized_pairing
#print axioms reciprocal_parameters
#print axioms pairing_transfer
#print axioms resolvent_pairing
end
end UnifiedTheory.Audit.KFCausalWeightedCauchyPairing
