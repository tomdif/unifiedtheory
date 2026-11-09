/-
  Tests required to identify a fixed microscopic wave parent with the
  areal-clock target. A time change alone fails in the same canonical
  variables. A time-dependent canonical field rescaling instead yields
  a positive wave Hamiltonian with mass squared 1/(4 t^2).
  The clock, rescaling and reconstructed metric are continuum suppliers;
  this file does not claim they emerge from the spin model.
-/
import UnifiedTheory.Audit.KFCausalTensorModeDynamics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalArealMicroscopicBridge
noncomputable section

/-- Matching both canonical equations at two areal-log times with only
a time reparametrization forces those times to be identical. -/
theorem fixed_parent_clock_rigidity
    (U g c r s₁ s₂ τ₁ τ₂ : ℝ) (hc : c ≠ 0) (hr : r ≠ 0)
    (hp₁ : s₁*U = 1/c) (hp₂ : s₂*U = 1/c)
    (hq₁ : s₁*g = r*Real.exp (2*τ₁)/c)
    (hq₂ : s₂*g = r*Real.exp (2*τ₂)/c) : τ₁ = τ₂ := by
  have hU : U ≠ 0 := by
    intro h
    simp [h] at hp₁
    exact hc hp₁.symm
  have hs : s₁ = s₂ := mul_right_cancel₀ hU (hp₁.trans hp₂.symm)
  have he : Real.exp (2*τ₁) = Real.exp (2*τ₂) := by
    apply mul_left_cancel₀ hr
    apply (div_left_inj' hc).mp
    rw [← hq₁, ← hq₂, hs]
  have h := Real.exp_injective he
  linarith

def rescaledQ (c t q : ℝ) : ℝ := Real.sqrt (c*t)*q
def rescaledP (c t q p : ℝ) : ℝ := p/Real.sqrt (c*t)+rescaledQ c t q/(2*t)

theorem rescaling_canonical (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    Real.sqrt (c*t)*(1/Real.sqrt (c*t)) - 0*(Real.sqrt (c*t)/(2*t)) = 1 := by
  have hw := (Real.sqrt_pos.2 (mul_pos hc ht)).ne'
  field_simp
  ring

theorem sqrt_scale_derivative (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (c*s)) (Real.sqrt (c*t)/(2*t)) t := by
  have hw : Real.sqrt (c*t) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hc ht)).ne'
  have hd := ((hasDerivAt_id t).const_mul c).sqrt (mul_pos hc ht).ne'
  convert hd using 1
  dsimp
  field_simp
  nlinarith [Real.sq_sqrt (mul_pos hc ht).le]

/-- The actual derivative of the rescaled coordinate, using the areal-time
Hamilton equation Q_t=P/(c t). -/
theorem rescaled_coordinate_equation (q p : ℝ → ℝ) (c t : ℝ)
    (hc : 0 < c) (ht : 0 < t)
    (hq : HasDerivAt q (p t/(c*t)) t) :
    HasDerivAt (fun s => rescaledQ c s (q s)) (rescaledP c t (q t) (p t)) t := by
  have hw : Real.sqrt (c*t) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hc ht)).ne'
  have hw2 := Real.sq_sqrt (mul_pos hc ht).le
  convert (sqrt_scale_derivative c t hc ht).mul hq using 1
  dsimp [rescaledQ, rescaledP]
  field_simp
  rw [hw2]
  ring

/-- Both transformed Hamilton equations, including the time-dependent
momentum shift. Merely rescaling Q would omit the mass term. -/
theorem rescaled_momentum_equation (q p : ℝ → ℝ) (c r t qxx : ℝ)
    (hc : 0 < c) (ht : 0 < t)
    (hq : HasDerivAt q (p t/(c*t)) t)
    (hp : HasDerivAt p (r*t*qxx/c) t) :
    HasDerivAt (fun s => rescaledP c s (q s) (p s))
      (r/c^2*(Real.sqrt (c*t)*qxx)-rescaledQ c t (q t)/(4*t^2)) t := by
  have hw : Real.sqrt (c*t) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hc ht)).ne'
  have hw2 := Real.sq_sqrt (mul_pos hc ht).le
  have hdw := sqrt_scale_derivative c t hc ht
  have hdu := rescaled_coordinate_equation q p c t hc ht hq
  have hd := (hp.div hdw hw).add (hdu.div ((hasDerivAt_id t).const_mul 2) (by positivity))
  convert hd using 1
  dsimp [rescaledP, rescaledQ]
  field_simp
  rw [hw2]
  ring

def rescaledEnergy (ω2 t q p : ℝ) : ℝ := (p^2+ω2*q^2+q^2/(4*t^2))/2

theorem rescaledEnergy_nonneg (ω2 t q p : ℝ) (hω : 0 ≤ ω2) :
    0 ≤ rescaledEnergy ω2 t q p := by
  unfold rescaledEnergy
  positivity

/-- The rescaled energy decreases, including the homogeneous mode ω2=0. -/
theorem rescaled_energy_derivative (q p : ℝ → ℝ) (ω2 t : ℝ) (ht : 0 < t)
    (hq : HasDerivAt q (p t) t)
    (hp : HasDerivAt p (-ω2*q t-q t/(4*t^2)) t) :
    HasDerivAt (fun s => rescaledEnergy ω2 s (q s) (p s))
      (-(q t)^2/(4*t^3)) t := by
  have hd := ((hp.pow 2).add ((hq.pow 2).const_mul ω2)).add
    ((hq.pow 2).div (((hasDerivAt_id t).pow 2).const_mul 4) (by dsimp; positivity))
  convert hd.div_const 2 using 1
  dsimp
  field_simp
  ring

theorem rescaled_energy_antitone (q p : ℝ → ℝ) (ω2 : ℝ)
    (hq : ∀ t, 0 < t → HasDerivAt q (p t) t)
    (hp : ∀ t, 0 < t → HasDerivAt p (-ω2*q t-q t/(4*t^2)) t) :
    AntitoneOn (fun t => rescaledEnergy ω2 t (q t) (p t)) (Set.Ioi 0) := by
  have hd : ∀ t, 0 < t → HasDerivAt (fun s => rescaledEnergy ω2 s (q s) (p s))
      (-(q t)^2/(4*t^3)) t := fun t ht =>
    rescaled_energy_derivative q p ω2 t ht (hq t ht) (hp t ht)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa using ht
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

/-- No frequency-dependent constant or mode count is lost in this bound. -/
theorem finite_rescaled_energy_bound {ι : Type*} [Fintype ι]
    (q p : ι → ℝ → ℝ) (ω2 : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hq : ∀ i t, 0 < t → HasDerivAt (q i) (p i t) t)
    (hp : ∀ i t, 0 < t → HasDerivAt (p i) (-ω2 i*q i t-q i t/(4*t^2)) t) :
    ∑ i, rescaledEnergy (ω2 i) b (q i b) (p i b) ≤
      ∑ i, rescaledEnergy (ω2 i) a (q i a) (p i a) := by
  apply Finset.sum_le_sum
  intro i _
  exact rescaled_energy_antitone (q i) (p i) (ω2 i) (hq i) (hp i) ha (ha.trans_le hab) hab

open KFCausalTensorModeDynamics in
/-- In the same bare six-component metric, a longitudinal response is
charged by the linear tensor penalty; the transverse wave cancels out. -/
theorem longitudinal_symbol_cost (k q L : ℝ) :
    frobenius ![q,L,-q,0,0,0] (tensorPenalty 0 k 0 ![q,L,-q,0,0,0]) =
      4*k^2*L^2 := by
  simp [KFCausalTensorModeDynamics.frobenius, tensorPenalty, divergence, scalarConstraint, ell, tr]
  ring

open KFCausalTensorModeDynamics in
theorem bare_sector_has_no_longitudinal_response (k q L : ℝ) (hk : k ≠ 0)
    (h : tensorPenalty 0 k 0 ![q,L,-q,0,0,0] = 0) : L = 0 := by
  have he := longitudinal_symbol_cost k q L
  rw [h] at he
  simp [KFCausalTensorModeDynamics.frobenius] at he
  exact he.resolve_left hk

#print axioms fixed_parent_clock_rigidity
#print axioms rescaling_canonical
#print axioms sqrt_scale_derivative
#print axioms rescaled_coordinate_equation
#print axioms rescaled_momentum_equation
#print axioms rescaledEnergy_nonneg
#print axioms rescaled_energy_derivative
#print axioms rescaled_energy_antitone
#print axioms finite_rescaled_energy_bound
#print axioms longitudinal_symbol_cost
#print axioms bare_sector_has_no_longitudinal_response

end
end UnifiedTheory.Audit.KFCausalArealMicroscopicBridge
