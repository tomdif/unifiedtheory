/-
  A local canonical map cannot turn a fixed-speed massless wave into the
  rescaled areal wave. All time-dependent real 2x2 symplectic point maps
  and orientation-preserving time changes are included. Spatial derivative
  or nonlocal transformations, different microscopic interactions and
  nontrivial background phases are outside the theorem.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLocalClockObstruction
noncomputable section
open Filter Topology

private theorem derivative_zero_on_positive
    (f df : ℝ → ℝ) (hf : ∀ t, 0 < t → f t = 0)
    (hd : ∀ t, 0 < t → HasDerivAt f (df t) t)
    (t : ℝ) (ht : 0 < t) : df t = 0 := by
  have he : f =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact hf s hs
  exact (hd t ht).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)

/-- Coefficient identity S'+rho S A(k)=B(k,t) S, where
S=[[a,b],[c,d]], A=[[0,1],[-k,0]], B=[[0,1],[-k-mass,0]].
Here k is frequency squared; only k=0 and k=1 are needed below. -/
def generatorMatch (a b c d da db dc dd ρ mass k : ℝ) : Prop :=
  da-ρ*b*k = c ∧ db+ρ*a = d ∧
    dc-ρ*d*k = -(k+mass)*a ∧ dd+ρ*c = -(k+mass)*b

/-- A necessary condition for any such local, canonical intertwiner of the
whole wave field: the target mass is zero at every positive time. -/
theorem local_canonical_map_forces_zero_mass
    (a b c d da db dc dd ρ mass : ℝ → ℝ)
    (ha : ∀ t, 0 < t → HasDerivAt a (da t) t)
    (hb : ∀ t, 0 < t → HasDerivAt b (db t) t)
    (hc : ∀ t, 0 < t → HasDerivAt c (dc t) t)
    (hρ : ∀ t, 0 < t → 0 < ρ t)
    (hsym : ∀ t, 0 < t → a t*d t-b t*c t = 1)
    (hmatch : ∀ t, 0 < t → ∀ k : ℝ,
      generatorMatch (a t) (b t) (c t) (d t)
        (da t) (db t) (dc t) (dd t) (ρ t) (mass t) k) :
    ∀ t, 0 < t → mass t = 0 := by
  have hb0 : ∀ t, 0 < t → b t = 0 := by
    intro t ht
    have h0 := (hmatch t ht 0).2.2.2
    have h1 := (hmatch t ht 1).2.2.2
    nlinarith
  have hdb0 : ∀ t, 0 < t → db t = 0 :=
    derivative_zero_on_positive b db hb0 hb
  have had : ∀ t, 0 < t → a t*d t = 1 := by
    intro t ht
    simpa [hb0 t ht] using hsym t ht
  have ha0 : ∀ t, 0 < t → a t ≠ 0 := by
    intro t ht hz
    have h := had t ht
    simp [hz] at h
  have hdrel : ∀ t, 0 < t → d t = ρ t*a t := by
    intro t ht
    have h := (hmatch t ht 0).2.1
    simpa [hdb0 t ht] using h.symm
  have hρd : ∀ t, 0 < t → ρ t*d t = a t := by
    intro t ht
    have h0 := (hmatch t ht 0).2.2.1
    have h1 := (hmatch t ht 1).2.2.1
    nlinarith
  have hρ1 : ∀ t, 0 < t → ρ t = 1 := by
    intro t ht
    have he : ((ρ t)^2-1)*a t = 0 := by
      have h := hρd t ht
      rw [hdrel t ht] at h
      nlinarith
    have hs := (mul_eq_zero.mp he).resolve_right (ha0 t ht)
    have hp := hρ t ht
    nlinarith
  have ha2 : ∀ t, 0 < t → (a t)^2 = 1 := by
    intro t ht
    have h := had t ht
    rw [hdrel t ht, hρ1 t ht] at h
    nlinarith
  have hda0 : ∀ t, 0 < t → da t = 0 := by
    intro t ht
    have hzero : ∀ s, 0 < s → (a s)^2-1 = 0 := by
      intro s hs
      rw [ha2 s hs]
      ring
    have hder : ∀ s, 0 < s → HasDerivAt (fun u => (a u)^2-1) (2*a s*da s) s := by
      intro s hs
      simpa using ((ha s hs).pow 2).sub_const 1
    have hz := derivative_zero_on_positive _ _ hzero hder t ht
    have hp : 2*a t ≠ 0 := mul_ne_zero (by norm_num) (ha0 t ht)
    exact (mul_eq_zero.mp hz).resolve_left hp
  have hc0 : ∀ t, 0 < t → c t = 0 := by
    intro t ht
    have h := (hmatch t ht 0).1
    simpa [hda0 t ht] using h.symm
  have hdc0 : ∀ t, 0 < t → dc t = 0 :=
    derivative_zero_on_positive c dc hc0 hc
  intro t ht
  have h := (hmatch t ht 0).2.2.1
  simp only [hdc0 t ht, mul_zero, sub_zero, zero_add, neg_mul, zero_eq_neg] at h
  exact (mul_eq_zero.mp h).resolve_right (ha0 t ht)

/-- The inverse-square term required by the areal target cannot be made
from the free parent by any map in the stated class. -/
theorem areal_local_map_impossible
    (a b c d da db dc dd ρ : ℝ → ℝ)
    (ha : ∀ t, 0 < t → HasDerivAt a (da t) t)
    (hb : ∀ t, 0 < t → HasDerivAt b (db t) t)
    (hc : ∀ t, 0 < t → HasDerivAt c (dc t) t)
    (hρ : ∀ t, 0 < t → 0 < ρ t)
    (hsym : ∀ t, 0 < t → a t*d t-b t*c t = 1) :
    ¬ (∀ t, 0 < t → ∀ k : ℝ,
      generatorMatch (a t) (b t) (c t) (d t)
        (da t) (db t) (dc t) (dd t) (ρ t) (1/(4*t^2)) k) := by
  intro h
  have hz := local_canonical_map_forces_zero_mass a b c d da db dc dd ρ
    (fun t => 1/(4*t^2)) ha hb hc hρ hsym h 1 (by norm_num)
  norm_num at hz

#print axioms local_canonical_map_forces_zero_mass
#print axioms areal_local_map_impossible

end
end UnifiedTheory.Audit.KFCausalLocalClockObstruction
