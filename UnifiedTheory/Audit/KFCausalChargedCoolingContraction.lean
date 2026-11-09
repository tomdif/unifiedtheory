/- Finite real charged-cooling shifts contract every correlated fixed-v Gram form. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedCoolingContraction
noncomputable section
open Matrix Set
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingDerivative KFCausalChargedCoolingFixedV

variable {n : Type*} [Fintype n]

theorem translated_sector (r : ℂ) (hr : |r.im| < r.re) (x : ℝ) (hx : 0 ≤ x) :
    |(r+(x:ℂ)).im| < (r+(x:ℂ)).re := by
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,add_zero]
  linarith

theorem translated_form_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => form ((α:ℂ)*(r+(t:ℂ))^2/2) w v c)
      (-(star c ⬝ᵥ ((fun i j => dissipation ((α:ℂ)*(r+(x:ℂ))^2/2)
        ((α:ℂ)*(r+(x:ℂ))) (w i) (w j) v) *ᵥ c))) x := by
  have h := (actual_form_derivative α (r+(x:ℂ)) hα (translated_sector r hr x hx) w hw v c).scomp_of_eq x
    ((hasDerivAt_id x).sub_const x) (by simp)
  simp only [one_smul] at h
  convert h using 1
  funext t
  congr 3
  simp only [id_eq,Complex.ofReal_sub]
  ring

theorem form_antitone (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    AntitoneOn (fun t : ℝ => (form ((α:ℂ)*(r+(t:ℂ))^2/2) w v c).re) (Ici 0) := by
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun t : ℝ => (form ((α:ℂ)*(r+(t:ℂ))^2/2) w v c).re)
        (-(star c ⬝ᵥ ((fun i j => dissipation ((α:ℂ)*(r+(x:ℂ))^2/2)
          ((α:ℂ)*(r+(x:ℂ))) (w i) (w j) v) *ᵥ c))).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      (translated_form_derivative α r hα hr w hw v c x hx)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    change -(star c ⬝ᵥ ((fun i j => dissipation ((α:ℂ)*(r+(x:ℂ))^2/2)
      ((α:ℂ)*(r+(x:ℂ))) (w i) (w j) v) *ᵥ c)).re ≤ 0
    exact neg_nonpos.mpr (actual_dissipation_form_nonnegative α (r+(x:ℂ)) hα
      (translated_sector r hr x (interior_subset hx)) w hw v c)

theorem positive_shift_contraction (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v h : ℝ) (hh : 0 ≤ h) (c : n → ℂ) :
    (form ((α:ℂ)*(r+(h:ℂ))^2/2) w v c).re ≤ (form ((α:ℂ)*r^2/2) w v c).re := by
  simpa only [Complex.ofReal_zero,add_zero] using
    form_antitone α r hα hr w hw v c (show (0:ℝ) ∈ Ici 0 by simp) hh hh

#print axioms translated_sector
#print axioms translated_form_derivative
#print axioms form_antitone
#print axioms positive_shift_contraction
end
end UnifiedTheory.Audit.KFCausalChargedCoolingContraction
