/- An inhomogeneous interval estimate and its application to an arbitrary
velocity curve in transported energy. No limiting derivative is assumed. -/
import UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalForcedEnergyGrowth
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
open UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth

theorem forced_interval_growth (E D : ℝ → ℝ) (κ J l r : ℝ)
    (hκ : 0 ≤ κ) (hJ : 0 ≤ J) (hlr : l ≤ r) (hc : ContinuousOn E (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt E (D t) t)
    (hb : ∀ t ∈ Ioo l r, D t ≤ κ*E t+J) :
    E r ≤ Real.exp (κ*(r-l))*(E l+J*(r-l)) := by
  have he := interval_growth (fun t => E t+J*(r-t)) (fun t => D t-J) κ l r hlr
    (hc.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
    (fun t ht => by
      have hh := (hd t ht).add (((hasDerivAt_const t r).sub (hasDerivAt_id t)).const_mul J)
      simpa only [zero_sub,mul_neg,mul_one,← sub_eq_add_neg] using hh)
    (fun t ht => by
      have hpos := mul_nonneg hκ (mul_nonneg hJ (sub_nonneg.mpr ht.2.le))
      have hbt := hb t ht
      nlinarith only [hpos,hbt])
  simpa only [sub_self,mul_zero,add_zero] using he

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def velocityDerivative (F D S P : ℝ → V →L[ℂ] V) (w v : ℝ → V) (t : ℝ) : ℝ :=
  energy (D t) (S t (w t))+2*(inner ℂ (S t (w t)) (F t (P t (w t)+S t (v t)))).re

theorem energy_velocity_derivative (F D S P : ℝ → V →L[ℂ] V) (w v : ℝ → V) (t : ℝ)
    (hF : (F t).toLinearMap.IsSymmetric) (hd : HasDerivAt F (D t) t)
    (hs : HasDerivAt S (P t) t) (hw : HasDerivAt w (v t) t) :
    HasDerivAt (trajectoryEnergy F S w) (velocityDerivative F D S P w v t) t :=
  energy_derivative F (D t) (fun r => S r (w r)) (P t (w t)+S t (v t)) t hF hd
    (KFCausalHilbertStateEvolution.operator_apply_derivative S w (P t) (v t) t hs hw)

theorem velocity_derivative_bound (F D S P : ℝ → V →L[ℂ] V) (w v : ℝ → V)
    (t θ ω κ M δ : ℝ) (hθ : 0 ≤ θ) (hω : 0 ≤ ω) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hκ : 2+2*θ+8*ω ≤ κ) (hpos : 0 ≤ energy (F t) (S t (w t)))
    (hd : energy (D t) (S t (w t)) ≤ 2*energy (F t) (S t (w t)))
    (hp : (inner ℂ (S t (w t)) (F t (P t (w t)))).re ≤ θ*energy (F t) (S t (w t)))
    (hv : 2*(inner ℂ (S t (w t)) (F t (S t (v t)))).re ≤
      4*ω*energy (F t) (S t (w t))+(6+8*ω)*M*δ) :
    velocityDerivative F D S P w v t ≤ κ*trajectoryEnergy F S w t+(6+κ)*M*δ := by
  have hr : 2+2*θ+4*ω ≤ κ := by linarith
  have hr' : 8*ω ≤ κ := by linarith
  have hm := mul_le_mul_of_nonneg_right hr hpos
  have hm' := mul_le_mul_of_nonneg_right hr' (mul_nonneg hM hδ)
  simp only [velocityDerivative,trajectoryEnergy,map_add,inner_add_right,Complex.add_re]
  nlinarith only [hd,hp,hv,hm,hm']

theorem velocity_growth (F D S P : ℝ → V →L[ℂ] V) (θ ω : ℝ → ℝ)
    (κ M δ l r : ℝ) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hlr : l ≤ r)
    (hFc : Continuous F) (hSc : Continuous S) (hF : ∀ t, (F t).toLinearMap.IsSymmetric)
    (hD : ∀ t, HasDerivAt F (D t) t) (hP : ∀ t, HasDerivAt S (P t) t)
    (hθ : ∀ t ∈ Icc l r, 0 ≤ θ t) (hω : ∀ t ∈ Icc l r, 0 ≤ ω t)
    (hrate : ∀ t ∈ Icc l r, 2+2*θ t+8*ω t ≤ κ)
    (hd : ∀ t ∈ Icc l r, ∀ x, energy (D t) (S t x) ≤ 2*energy (F t) (S t x))
    (hp : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (P t x))).re ≤ θ t*energy (F t) (S t x))
    (hpos : ∀ t ∈ Icc l r, ∀ x, 0 ≤ energy (F t) (S t x))
    (w v : ℝ → V) (hwc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Ioo l r, HasDerivAt w (v t) t)
    (hv : ∀ t ∈ Icc l r, 2*(inner ℂ (S t (w t)) (F t (S t (v t)))).re ≤
      4*ω t*energy (F t) (S t (w t))+(6+8*ω t)*M*δ) :
    trajectoryEnergy F S w r ≤ Real.exp (κ*(r-l))*(trajectoryEnergy F S w l+(6+κ)*M*δ*(r-l)) := by
  apply forced_interval_growth (trajectoryEnergy F S w) (velocityDerivative F D S P w v)
    κ ((6+κ)*M*δ) l r hκ (by positivity) hlr (trajectory_continuousOn F S w _ hFc hSc hwc)
    (fun t ht => energy_velocity_derivative F D S P w v t (hF t) (hD t) (hP t) (hw t ht))
  intro t ht
  have hi := Ioo_subset_Icc_self ht
  exact velocity_derivative_bound F D S P w v t (θ t) (ω t) κ M δ
    (hθ t hi) (hω t hi) hM hδ (hrate t hi) (hpos t hi (w t))
    (hd t hi (w t)) (hp t hi (w t)) (hv t hi)

theorem drop_initial_zero (F S : ℝ → V →L[ℂ] V) (w : ℝ → V) (κ J l r : ℝ)
    (hi : w l = 0)
    (he : trajectoryEnergy F S w r ≤ Real.exp (κ*(r-l))*(trajectoryEnergy F S w l+J*(r-l))) :
    energy (F r) (S r (w r)) ≤ Real.exp (κ*(r-l))*(J*(r-l)) := by
  simpa only [trajectoryEnergy,hi,map_zero,energy,inner_zero_left,Complex.zero_re,zero_add] using he

#print axioms forced_interval_growth
#print axioms energy_velocity_derivative
#print axioms velocity_derivative_bound
#print axioms velocity_growth
#print axioms drop_initial_zero
end
end UnifiedTheory.Audit.KFCausalForcedEnergyGrowth
