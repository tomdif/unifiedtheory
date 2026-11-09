/- Assemble actual domain-preserving solutions with uniform bounds on
both the state and the generator output, from the derived energy estimates. -/
import UnifiedTheory.Audit.KFCausalResolventDomainTrajectories
import UnifiedTheory.Audit.KFCausalTransportedPerturbedGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformGraphTrajectories
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_reference_parameter (q : ℝ → ℝ) (l r : ℝ) (hc : ContinuousOn q (Icc l r)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ Icc l r, q t < lam := by
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image hc
  refine ⟨|N|+1,by positivity,?_⟩
  intro t ht
  have hn : q t ≤ N := hN (mem_image_of_mem _ ht)
  linarith [le_abs_self N]

theorem subinterval_derivative (w dw : ℝ → V) (l r t : ℝ) (htr : t ≤ r)
    (hd : ∀ u ∈ Icc l r, HasDerivWithinAt w (dw u) (Icc l r) u) :
    ∀ u ∈ Ioo l t, HasDerivAt w (dw u) u := by
  intro u hu
  have hur := hu.2.trans_le htr
  exact (hd u ⟨hu.1.le,hur.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hur)

theorem exists_uniform_graph_bounds (G : ℝ → V →ₗ.[ℂ] V) (A : ℝ → ℝ → V →L[ℂ] V)
    (R D F S : ℝ → V →L[ℂ] V) (q ω ρ σ : ℝ → ℝ) (lam l r : ℝ)
    (hparams : ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q t < b ∧ 2*ω t ≤ b ∧ σ t ≤ κ)
    (hrate : ∀ t, ρ t ≤ σ t)
    (hF : ∀ t, (F t).toLinearMap.IsSymmetric) (hpos : ∀ t x, 0 ≤ energy (F t) x)
    (hex : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ∀ x y, (x,y) ∈ (G l).graph →
      ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
        ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
        (∀ t ∈ Icc l r, w t = R t (z t)) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧
          HasDerivWithinAt z ((A b t-D t) (z t)) (Icc l r) t ∧
          (w t,lam • w t-z t) ∈ (G t).graph)
    (hEw : ∀ b κ t, 0 < b → l ≤ t →
      (∀ u ∈ Icc l t, q u < b ∧ 2*ω u ≤ b ∧ ρ u ≤ κ) →
      ∀ w : ℝ → V, ContinuousOn w (Icc l t) →
      (∀ u ∈ Ioo l t, HasDerivAt w (A b u (w u)) u) →
      energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l)))
    (hEz : ∀ b κ t, 0 < b → l ≤ t →
      (∀ u ∈ Icc l t, q u < b ∧ 2*ω u ≤ b ∧ σ u ≤ κ) →
      ∀ z : ℝ → V, ContinuousOn z (Icc l t) →
      (∀ u ∈ Ioo l t, HasDerivAt z ((A b u-D u) (z u)) u) →
      energy (F t) (S t (z t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (z l))) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ x y, (x,y) ∈ (G l).graph →
      ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
        ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
        (∀ t ∈ Icc l r, w t = R t (z t)) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧
          HasDerivWithinAt z ((A b t-D t) (z t)) (Icc l r) t ∧
          (w t,lam • w t-z t) ∈ (G t).graph ∧
          energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l x) ∧
          energy (F t) (S t (z t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (lam • x-y)) ∧
          energy (F t) (S t (lam • w t-z t)) ≤ Real.exp (κ*(t-l))*
            (2*lam^2*energy (F l) (S l x)+2*energy (F l) (S l (lam • x-y))) := by
  obtain ⟨b₀,κ,hb₀,hκ,hp⟩ := hparams
  refine ⟨b₀,κ,hb₀,hκ,?_⟩
  intro b hb x y hxy
  have hbpos := hb₀.trans_le hb
  obtain ⟨w,z,hi,hzi,hc,hzc,hr,hw⟩ := hex b hbpos (fun t ht => (hp b hb t ht).1) x y hxy
  refine ⟨w,z,hi,hzi,hc,hzc,hr,?_⟩
  intro t ht
  have hsub : Icc l t ⊆ Icc l r := Icc_subset_Icc le_rfl ht.2
  have hwE : energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l x) := by
    have he := hEw b κ t hbpos ht.1
      (fun u hu => ⟨(hp b hb u (hsub hu)).1,(hp b hb u (hsub hu)).2.1,
        (hrate u).trans (hp b hb u (hsub hu)).2.2⟩) w (hc.mono hsub)
      (subinterval_derivative w (fun u => A b u (w u)) l r t ht.2 (fun u hu => (hw u hu).1))
    simpa only [hi] using he
  have hzE : energy (F t) (S t (z t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (lam • x-y)) := by
    have he := hEz b κ t hbpos ht.1 (fun u hu => hp b hb u (hsub hu)) z (hzc.mono hsub)
      (subinterval_derivative z (fun u => (A b u-D u) (z u)) l r t ht.2 (fun u hu => (hw u hu).2.1))
    simpa only [hzi] using he
  exact ⟨(hw t ht).1,(hw t ht).2.1,(hw t ht).2.2,hwE,hzE,
    KFCausalTransportedPerturbedGrowth.graph_output_energy_bound (F t) (S t) (hF t) (hpos t)
      (w t) (z t) lam (Real.exp (κ*(t-l))) (energy (F l) (S l x))
      (energy (F l) (S l (lam • x-y))) hwE hzE⟩

#print axioms subinterval_derivative
#print axioms exists_reference_parameter
#print axioms exists_uniform_graph_bounds
end
end UnifiedTheory.Audit.KFCausalUniformGraphTrajectories
