/- An interval energy estimate for bounded approximations in a moving
coordinate system. Only continuity at interval endpoints is needed. -/
import UnifiedTheory.Audit.KFCausalTransportedEnergyForm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy

theorem interval_growth (E D : ℝ → ℝ) (κ l r : ℝ) (hlr : l ≤ r)
    (hc : ContinuousOn E (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt E (D t) t)
    (hb : ∀ t ∈ Ioo l r, D t ≤ κ*E t) :
    E r ≤ Real.exp (κ*(r-l))*E l := by
  have hw (x : ℝ) (hx : x ∈ Ioo l r) :
      HasDerivAt (fun t => Real.exp (-κ*t)*E t) (Real.exp (-κ*x)*(D x-κ*E x)) x := by
    have he := (Real.hasDerivAt_exp (-κ*x)).comp x ((hasDerivAt_id x).const_mul (-κ))
    convert he.mul (hd x hx) using 1
    simp only [Function.comp_apply]
    ring
  have hm : AntitoneOn (fun t => Real.exp (-κ*t)*E t) (Icc l r) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l r)
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hc)
      (fun x hx => (hw x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt)
    intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hb x (by simpa only [interior_Icc] using hx)))
  have hh := mul_le_mul_of_nonneg_left (hm ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩ hlr) (Real.exp_pos (κ*r)).le
  have hself : Real.exp (κ*r)*Real.exp (-κ*r) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hshift : Real.exp (κ*r)*Real.exp (-κ*l) = Real.exp (κ*(r-l)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,hself,one_mul,hshift] using hh

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def trajectoryEnergy (F S : ℝ → V →L[ℂ] V) (w : ℝ → V) (t : ℝ) : ℝ := energy (F t) (S t (w t))

def trajectoryDerivative (F D S P A : ℝ → V →L[ℂ] V) (w : ℝ → V) (t : ℝ) : ℝ :=
  energy (D t) (S t (w t))+2*(inner ℂ (S t (w t)) (F t (P t (w t)+S t (A t (w t))))).re

theorem trajectory_continuousOn (F S : ℝ → V →L[ℂ] V) (w : ℝ → V) (I : Set ℝ)
    (hF : Continuous F) (hS : Continuous S) (hw : ContinuousOn w I) :
    ContinuousOn (trajectoryEnergy F S w) I := by
  have hv := hS.continuousOn.clm_apply hw
  have hf := hF.continuousOn.clm_apply hv
  exact Complex.continuous_re.comp_continuousOn (hv.inner hf)

theorem trajectory_derivative (F D S P A : ℝ → V →L[ℂ] V) (w : ℝ → V) (t : ℝ)
    (hF : (F t).toLinearMap.IsSymmetric) (hd : HasDerivAt F (D t) t)
    (hs : HasDerivAt S (P t) t) (hw : HasDerivAt w (A t (w t)) t) :
    HasDerivAt (trajectoryEnergy F S w) (trajectoryDerivative F D S P A w t) t :=
  energy_derivative F (D t) (fun r => S r (w r)) (P t (w t)+S t (A t (w t))) t hF hd
    (KFCausalHilbertStateEvolution.operator_apply_derivative S w (P t) (A t (w t)) t hs hw)

theorem trajectory_derivative_bound (F D S P A : ℝ → V →L[ℂ] V) (w : ℝ → V) (t θ ω : ℝ)
    (hd : energy (D t) (S t (w t)) ≤ 2*energy (F t) (S t (w t)))
    (hp : (inner ℂ (S t (w t)) (F t (P t (w t)))).re ≤ θ*energy (F t) (S t (w t)))
    (ha : (inner ℂ (S t (w t)) (F t (S t (A t (w t))))).re ≤ (4*ω)*energy (F t) (S t (w t))) :
    trajectoryDerivative F D S P A w t ≤ (2+2*θ+8*ω)*trajectoryEnergy F S w t := by
  simp only [trajectoryDerivative,trajectoryEnergy,map_add,inner_add_right,Complex.add_re]
  nlinarith only [hd,hp,ha]

theorem compact_rate_bounds (q ω ρ : ℝ → ℝ) (hq : Continuous q) (hω : Continuous ω)
    (hρ : Continuous ρ) (l r : ℝ) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ := by
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image
    (hq.max ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).mul hω)).continuousOn
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image hρ.continuousOn
  refine ⟨|N|+1,|M|+1,by positivity,by positivity,?_⟩
  intro b hb t ht
  have hn : max (q t) (2*ω t) ≤ N := hN (mem_image_of_mem _ ht)
  have hm : ρ t ≤ M := hM (mem_image_of_mem _ ht)
  have hq' := (le_max_left _ _).trans hn
  have hw' := (le_max_right _ _).trans hn
  exact ⟨by linarith [le_abs_self N],by linarith [le_abs_self N],by linarith [le_abs_self M]⟩

theorem trajectory_growth (F D S P A : ℝ → V →L[ℂ] V) (θ ω : ℝ → ℝ) (κ l r : ℝ)
    (hlr : l ≤ r) (hFc : Continuous F) (hSc : Continuous S)
    (hF : ∀ t, (F t).toLinearMap.IsSymmetric)
    (hD : ∀ t, HasDerivAt F (D t) t) (hP : ∀ t, HasDerivAt S (P t) t)
    (hd : ∀ t ∈ Icc l r, ∀ x, energy (D t) (S t x) ≤ 2*energy (F t) (S t x))
    (hp : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (P t x))).re ≤ θ t*energy (F t) (S t x))
    (ha : ∀ t ∈ Icc l r, ∀ x, (inner ℂ (S t x) (F t (S t (A t x)))).re ≤ (4*ω t)*energy (F t) (S t x))
    (hpos : ∀ t ∈ Icc l r, ∀ x, 0 ≤ energy (F t) (S t x))
    (hκ : ∀ t ∈ Icc l r, 2+2*θ t+8*ω t ≤ κ)
    (w : ℝ → V) (hwc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Ioo l r, HasDerivAt w (A t (w t)) t) :
    trajectoryEnergy F S w r ≤ Real.exp (κ*(r-l))*trajectoryEnergy F S w l := by
  apply interval_growth (trajectoryEnergy F S w) (trajectoryDerivative F D S P A w) κ l r hlr
    (trajectory_continuousOn F S w _ hFc hSc hwc)
    (fun t ht => trajectory_derivative F D S P A w t (hF t) (hD t) (hP t) (hw t ht))
  intro t ht
  have hi := Ioo_subset_Icc_self ht
  exact (trajectory_derivative_bound F D S P A w t (θ t) (ω t)
    (hd t hi (w t)) (hp t hi (w t)) (ha t hi (w t))).trans
    (mul_le_mul_of_nonneg_right (hκ t hi) (hpos t hi (w t)))

#print axioms interval_growth
#print axioms trajectory_continuousOn
#print axioms trajectory_derivative
#print axioms trajectory_derivative_bound
#print axioms compact_rate_bounds
#print axioms trajectory_growth
end
end UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth
