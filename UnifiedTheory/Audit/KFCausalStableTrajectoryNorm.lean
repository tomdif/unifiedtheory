/- Initial-state stability in the ambient form norm, derived from the
transported energy estimate and uniform coercivity. -/
import UnifiedTheory.Audit.KFCausalUniformGraphTrajectories

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStableTrajectoryNorm
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem transported_energy_upper (F S : V →L[ℂ] V) (x : V) :
    energy F (S x) ≤ (‖F‖*‖S‖^2)*‖x‖^2 := by
  have hn := (sq_le_sq₀ (norm_nonneg (S x)) (mul_nonneg (norm_nonneg S) (norm_nonneg x))).2
    (S.le_opNorm x)
  have he := (KFCausalWeightedMassEnergy.energy_norm_upper F (S x)).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg F))
  exact he.trans_eq (by ring)

theorem square_to_bound (L u v : ℝ) (hL : 0 ≤ L) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (he : u^2 ≤ L*v^2) : u ≤ (L+1)*v := by
  have hLs : L ≤ (L+1)^2 := by nlinarith only [hL,sq_nonneg L]
  apply (sq_le_sq₀ hu (mul_nonneg (by linarith) hv)).mp
  have hm := mul_le_mul_of_nonneg_right hLs (sq_nonneg v)
  nlinarith only [he,hm]

theorem energy_growth_to_norm (F S : ℝ → V →L[ℂ] V) (K κ l r t : ℝ)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ) (ht : t ∈ Icc l r)
    (hnorm : ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z)) (x z : V)
    (he : energy (F t) (S t z) ≤ Real.exp (κ*(t-l))*energy (F l) (S l x)) :
    ‖z‖ ≤ (K*Real.exp (κ*(r-l))*(‖F l‖*‖S l‖^2)+1)*‖x‖ := by
  have hup := transported_energy_upper (F l) (S l) x
  have hE := he.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)
  have hexp : Real.exp (κ*(t-l)) ≤ Real.exp (κ*(r-l)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) hκ)
  have hE' := hE.trans (mul_le_mul_of_nonneg_right hexp (by positivity))
  apply square_to_bound _ _ _ (by positivity) (norm_nonneg z) (norm_nonneg x)
  exact (hnorm z).trans ((mul_le_mul_of_nonneg_left hE' hK).trans_eq (by ring))

theorem interval_energy_growth (A F S : ℝ → V →L[ℂ] V) (κ l r : ℝ)
    (hpoint : ∀ t ∈ Icc l r, ∀ w : ℝ → V, ContinuousOn w (Icc l t) →
      (∀ z ∈ Ioo l t, HasDerivAt w (A z (w z)) z) →
      energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l)))
    (w : ℝ → V) (hc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Icc l r, HasDerivWithinAt w (A t (w t)) (Icc l r) t) :
    ∀ t ∈ Icc l r, energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l)) := by
  intro t ht
  exact hpoint t ht w (hc.mono (Icc_subset_Icc le_rfl ht.2))
    (KFCausalUniformGraphTrajectories.subinterval_derivative w (fun z => A z (w z)) l r t ht.2 hw)

theorem difference_stability (A F S : ℝ → V →L[ℂ] V) (K κ l r : ℝ)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hnorm : ∀ t ∈ Icc l r, ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z))
    (henergy : ∀ w : ℝ → V, ContinuousOn w (Icc l r) →
      (∀ t ∈ Icc l r, HasDerivWithinAt w (A t (w t)) (Icc l r) t) →
      ∀ t ∈ Icc l r, energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l)))
    (u v : ℝ → V) (huC : ContinuousOn u (Icc l r)) (hvC : ContinuousOn v (Icc l r))
    (hu : ∀ t ∈ Icc l r, HasDerivWithinAt u (A t (u t)) (Icc l r) t)
    (hv : ∀ t ∈ Icc l r, HasDerivWithinAt v (A t (v t)) (Icc l r) t) :
    ∀ t ∈ Icc l r, ‖u t-v t‖ ≤ (K*Real.exp (κ*(r-l))*(‖F l‖*‖S l‖^2)+1)*‖u l-v l‖ := by
  have hd : ∀ t ∈ Icc l r,
      HasDerivWithinAt (fun z => u z-v z) (A t (u t-v t)) (Icc l r) t := by
    intro t ht
    simpa only [map_sub] using (hu t ht).sub (hv t ht)
  intro t ht
  exact energy_growth_to_norm F S K κ l r t hK hκ ht (hnorm t ht) (u l-v l) (u t-v t)
    (henergy (fun z => u z-v z) (huC.sub hvC) hd t ht)

#print axioms transported_energy_upper
#print axioms square_to_bound
#print axioms energy_growth_to_norm
#print axioms interval_energy_growth
#print axioms difference_stability
end
end UnifiedTheory.Audit.KFCausalStableTrajectoryNorm
