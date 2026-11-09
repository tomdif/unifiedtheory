/- A bounded correction to the full approximations gives a derived
energy estimate for the resolvent coordinates and their graph outputs. -/
import UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth
import UnifiedTheory.Audit.KFCausalQuasiDissipativeResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
open UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem perturbed_pairing (F S A B : V →L[ℂ] V) (ω η : ℝ) (x : V)
    (hA : (inner ℂ (S x) (F (S (A x)))).re ≤ (4*ω)*energy F (S x))
    (hB : (inner ℂ (S x) (F (S ((-B) x)))).re ≤ η*energy F (S x)) :
    (inner ℂ (S x) (F (S ((A-B) x)))).re ≤ (4*ω+η)*energy F (S x) := by
  simp only [ContinuousLinearMap.neg_apply,map_neg,inner_neg_right,Complex.neg_re] at hB
  simp only [ContinuousLinearMap.sub_apply,map_sub,inner_sub_right,Complex.sub_re]
  nlinarith only [hA,hB]

theorem perturbed_growth (F D S P A B : ℝ → V →L[ℂ] V) (θ ω η : ℝ → ℝ) (κ l r : ℝ)
    (hlr : l ≤ r) (hFc : Continuous F) (hSc : Continuous S)
    (hF : ∀ t, (F t).toLinearMap.IsSymmetric)
    (hD : ∀ t, HasDerivAt F (D t) t) (hP : ∀ t, HasDerivAt S (P t) t)
    (hd : ∀ t ∈ Icc l r, ∀ x, energy (D t) (S t x) ≤ 2*energy (F t) (S t x))
    (hp : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (P t x))).re ≤ θ t*energy (F t) (S t x))
    (ha : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (S t (A t x)))).re ≤ (4*ω t)*energy (F t) (S t x))
    (hb : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (S t ((-B t) x)))).re ≤ η t*energy (F t) (S t x))
    (hpos : ∀ t ∈ Icc l r, ∀ x, 0 ≤ energy (F t) (S t x))
    (hκ : ∀ t ∈ Icc l r, 2+2*θ t+8*ω t+2*η t ≤ κ)
    (w : ℝ → V) (hwc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Ioo l r, HasDerivAt w ((A t-B t) (w t)) t) :
    trajectoryEnergy F S w r ≤ Real.exp (κ*(r-l))*trajectoryEnergy F S w l := by
  apply interval_growth (trajectoryEnergy F S w)
    (trajectoryDerivative F D S P (fun t => A t-B t) w) κ l r hlr
    (trajectory_continuousOn F S w _ hFc hSc hwc)
    (fun t ht => trajectory_derivative F D S P (fun t => A t-B t) w t (hF t) (hD t) (hP t) (hw t ht))
  intro t ht
  have hi := Ioo_subset_Icc_self ht
  have he := perturbed_pairing (F t) (S t) (A t) (B t) (ω t) (η t) (w t)
    (ha t hi (w t)) (hb t hi (w t))
  have hd' := hd t hi (w t)
  have hp' := hp t hi (w t)
  have hm := mul_le_mul_of_nonneg_right (hκ t hi) (hpos t hi (w t))
  simp only [trajectoryDerivative,trajectoryEnergy,map_add,inner_add_right,Complex.add_re]
  nlinarith only [he,hd',hp',hm]

theorem compact_rates (q ω ρ : ℝ → ℝ) (l r : ℝ)
    (hq : ContinuousOn q (Icc l r)) (hω : ContinuousOn ω (Icc l r)) (hρ : ContinuousOn ρ (Icc l r)) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ := by
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image
    (fun t ht => (hq t ht).max ((continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ℝ => (2:ℝ)) (Icc l r) t).mul (hω t ht)))
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image hρ
  refine ⟨|N|+1,|M|+1,by positivity,by positivity,?_⟩
  intro b hb t ht
  have hn : max (q t) (2*ω t) ≤ N := hN (mem_image_of_mem _ ht)
  have hm : ρ t ≤ M := hM (mem_image_of_mem _ ht)
  have hq' := (le_max_left _ _).trans hn
  have hw' := (le_max_right _ _).trans hn
  exact ⟨by linarith [le_abs_self N],by linarith [le_abs_self N],by linarith [le_abs_self M]⟩

theorem energy_sub_bound (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy F x) (x y : V) : energy F (x-y) ≤ 2*energy F x+2*energy F y := by
  have h₁ := KFCausalQuasiDissipativeResolvent.energy_sub_real F hF x y 1
  have h₂ := KFCausalQuasiDissipativeResolvent.energy_sub_real F hF x y (-1)
  have hpos := hp (x-(-1:ℝ) • y)
  simp only [one_smul,one_pow,one_mul] at h₁
  nlinarith only [h₁,h₂,hpos]

theorem graph_output_energy_bound (F S : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ energy F x) (w z : V) (lam C E₀ Z₀ : ℝ)
    (hw : energy F (S w) ≤ C*E₀) (hz : energy F (S z) ≤ C*Z₀) :
    energy F (S (lam • w-z)) ≤ C*(2*lam^2*E₀+2*Z₀) := by
  have he := energy_sub_bound F hF hp (lam • S w) (S z)
  rw [energy_real_smul] at he
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*lam^2 by positivity)
  simp only [map_sub,ContinuousLinearMap.map_smul_of_tower]
  nlinarith only [he,hm,hz]

#print axioms perturbed_pairing
#print axioms perturbed_growth
#print axioms compact_rates
#print axioms energy_sub_bound
#print axioms graph_output_energy_bound
end
end UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth
