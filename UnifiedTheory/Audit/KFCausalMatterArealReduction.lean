/-
  The common-metric scalar extension in areal gauge. A massless scalar
  adds a positive wave with the same principal speed. A nonzero scalar
  potential prevents the old constant longitudinal momentum gauge.

  These are exact classical reduced-target statements. Existence of
  gauge slices, the full 3D theory and a spin realization remain open.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMatterArealReduction
noncomputable section

def reducedEnergy (a b κ γ c area p qx pi phix : ℝ) : ℝ :=
  c/2+(p^2+(b/a)*area^2*qx^2+(κ/a)*pi^2+(γ/a)*area^2*phix^2)/(2*c)

/-- The actual scalar constraint after T'=0 and P_L=-c, divided by ae.
No scalar potential is present in this massless reduction. -/
theorem massless_constraint_solved (a b κ γ c area pT p qx pi phix : ℝ)
    (hc : c ≠ 0) :
    p^2/2+c^2/2+c*pT+(b/a)*area^2*qx^2/2+
      (κ/a)*pi^2/2+(γ/a)*area^2*phix^2/2 = 0 ↔
        pT = -reducedEnergy a b κ γ c area p qx pi phix := by
  unfold reducedEnergy
  constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith [h]

theorem reduced_energy_positive (a b κ γ c area p qx pi phix : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ) (hc : 0 < c) :
    0 < reducedEnergy a b κ γ c area p qx pi phix := by
  unfold reducedEnergy
  positivity

theorem scalar_momentum_derivative (a b κ γ c area p qx pi phix : ℝ) :
    HasDerivAt (fun u => reducedEnergy a b κ γ c area p qx u phix)
      (κ*pi/(a*c)) pi := by
  have hd := (((((hasDerivAt_id pi).pow 2).const_mul (κ/a)).const_add
    (p^2+(b/a)*area^2*qx^2)).add_const ((γ/a)*area^2*phix^2)).div_const (2*c)
  convert hd.const_add (c/2) using 1
  dsimp
  ring

theorem scalar_gradient_derivative (a b κ γ c area p qx pi phix : ℝ) :
    HasDerivAt (fun u => reducedEnergy a b κ γ c area p qx pi u)
      (γ*area^2*phix/(a*c)) phix := by
  have hd := ((((hasDerivAt_id phix).pow 2).const_mul ((γ/a)*area^2)).const_add
    (p^2+(b/a)*area^2*qx^2+(κ/a)*pi^2)).div_const (2*c)
  convert hd.const_add (c/2) using 1
  dsimp
  ring

theorem scalar_gravity_wave_speed (a b κ γ c area : ℝ) (ha : a ≠ 0)
    (hcommon : κ*γ=a*b) :
    (κ/(a*c))*(γ*area^2/(a*c)) = (b/a)*area^2/c^2 := by
  calc
    _ = (κ*γ)*area^2/(a^2*c^2) := by ring
    _ = (a*b)*area^2/(a^2*c^2) := by rw [hcommon]
    _ = _ := by field_simp

theorem sourced_spatial_constraint (c p qx pi phix lx : ℝ) (hc : c ≠ 0) :
    p*qx+pi*phix-c*lx=0 ↔ lx=(p*qx+pi*phix)/c := by
  constructor <;> intro h
  · apply (eq_div_iff hc).mpr
    linarith
  · rw [h]
    field_simp
    ring

/-- Both fields source the longitudinal metric through a local momentum
flux. This identity itself does not require the common-cone condition. -/
theorem total_momentum_flux (a b κ γ c area p qx px qxx pi phix pix phixx : ℝ) :
    ((b/a)*area^2*qxx/c)*qx+p*(px/c)+
      (γ*area^2*phixx/(a*c))*phix+pi*(κ*pix/(a*c)) =
        (p*px+(b/a)*area^2*qx*qxx+(κ/a)*pi*pix+(γ/a)*area^2*phix*phixx)/c := by
  ring

/-- The full constrained Hamiltonian after imposing spatially constant T.
K contains the kinetic and gradient terms and is independent of L here.
The scalar potential V carries the required volume exp(T+L/2). -/
def gaugeHamiltonian (a T L K V : ℝ) : ℝ :=
  a*Real.exp (-T-L/2)*K+Real.exp (T+L/2)*V

theorem longitudinal_derivative (a T L K V : ℝ) :
    HasDerivAt (fun l => gaugeHamiltonian a T l K V)
      (-gaugeHamiltonian a T L K V/2+Real.exp (T+L/2)*V) L := by
  have hn := (((hasDerivAt_const L (-T)).sub ((hasDerivAt_id L).div_const 2)).exp.const_mul a).mul_const K
  have hp := (((hasDerivAt_const L T).add ((hasDerivAt_id L).div_const 2)).exp).mul_const V
  convert hn.add hp using 1
  dsimp [gaugeHamiltonian]
  ring

theorem potential_clock_force (a T L K V lapse : ℝ)
    (hconstraint : gaugeHamiltonian a T L K V = 0) :
    -lapse*(-gaugeHamiltonian a T L K V/2+Real.exp (T+L/2)*V) =
      -lapse*Real.exp (T+L/2)*V := by rw [hconstraint]; ring

/-- This obstruction is exact at any constrained point with positive lapse.
Nonzero potential means P_L cannot remain constant under Hamilton's law. -/
theorem constant_longitudinal_momentum_requires_zero_potential
    (pL : ℝ → ℝ) (t T L V lapse : ℝ) (hlapse : 0 < lapse)
    (hconstant : HasDerivAt pL 0 t)
    (hforce : HasDerivAt pL (-lapse*Real.exp (T+L/2)*V) t) : V = 0 := by
  have he := hconstant.unique hforce
  have hp : -lapse*Real.exp (T+L/2) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hlapse)) (ne_of_gt (Real.exp_pos _))
  exact (mul_eq_zero.mp he.symm).resolve_left hp

theorem positive_potential_accelerates_longitudinal_momentum (T L V lapse : ℝ)
    (hlapse : 0 < lapse) (hV : 0 < V) : -lapse*Real.exp (T+L/2)*V < 0 := by
  have hp : 0 < lapse*Real.exp (T+L/2)*V := by positivity
  nlinarith

/-- Revised areal reduction: c=-P_L is a dynamical field. E contains
both fields' nonnegative momentum/gradient terms; W=exp(2T+L)V/a.
The potential is retained instead of imposing c constant. -/
def dynamicEnergy (c E W : ℝ) : ℝ := c/2+(E+2*W)/(2*c)

theorem massive_constraint_solved (c E W pT : ℝ) (hc : c ≠ 0) :
    c*pT+c^2/2+E/2+W=0 ↔ pT = -dynamicEnergy c E W := by
  unfold dynamicEnergy
  constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith [h]

theorem dynamic_energy_positive (c E W : ℝ) (hc : 0 < c)
    (hE : 0 ≤ E) (hW : 0 ≤ W) : 0 < dynamicEnergy c E W := by
  unfold dynamicEnergy
  positivity

/-- Since c=-P_L, the Hamiltonian equation is Ldot=-dH/dc. -/
theorem dynamic_energy_derivative_c (c E W : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun u => dynamicEnergy u E W)
      (1/2-(E+2*W)/(2*c^2)) c := by
  have hd := ((hasDerivAt_id c).div_const 2).add
    ((hasDerivAt_const c (E+2*W)).div ((hasDerivAt_id c).const_mul 2)
      (by dsimp; positivity))
  convert hd using 1
  dsimp
  field_simp
  ring

/-- The revised c equation is cdot=dH/dL=W/c, with no external
clock force added by hand. The scalar field is held fixed in d/dL. -/
theorem dynamic_energy_derivative_L (a T L V c E : ℝ) :
    HasDerivAt (fun l => dynamicEnergy c E (Real.exp (2*T+l)*V/a))
      (Real.exp (2*T+L)*V/(a*c)) L := by
  have hd := ((((((hasDerivAt_const L (2*T)).add (hasDerivAt_id L)).exp.mul_const V).div_const a).const_mul 2).const_add E).div_const (2*c)
  convert hd.const_add (c/2) using 1
  dsimp [dynamicEnergy]
  ring

theorem dynamic_clock_force_nonnegative (a T L V c : ℝ)
    (ha : 0 < a) (hV : 0 ≤ V) (hc : 0 < c) :
    0 ≤ Real.exp (2*T+L)*V/(a*c) := by positivity

theorem dynamic_spatial_constraint (c cx p qx pi phix lx : ℝ) (hc : c ≠ 0) :
    p*qx+pi*phix-c*lx+2*cx=0 ↔ lx=(p*qx+pi*phix+2*cx)/c := by
  constructor <;> intro h
  · apply (eq_div_iff hc).mpr
    linarith
  · rw [h]
    field_simp
    ring

/-- Along any supplied positive-branch solution with V>=0, c cannot
decrease. This is a stability statement, not a solution-existence theorem. -/
theorem dynamic_clock_monotone (c W : ℝ → ℝ) (lo hi : ℝ)
    (hc : ∀ t ∈ Set.Icc lo hi, 0 < c t)
    (hW : ∀ t ∈ Set.Icc lo hi, 0 ≤ W t)
    (hd : ∀ t ∈ Set.Icc lo hi, HasDerivAt c (W t/c t) t) :
    MonotoneOn c (Set.Icc lo hi) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc lo hi)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact div_nonneg (hW t (interior_subset ht)) (hc t (interior_subset ht)).le

#print axioms massless_constraint_solved
#print axioms reduced_energy_positive
#print axioms scalar_momentum_derivative
#print axioms scalar_gradient_derivative
#print axioms scalar_gravity_wave_speed
#print axioms sourced_spatial_constraint
#print axioms total_momentum_flux
#print axioms longitudinal_derivative
#print axioms potential_clock_force
#print axioms constant_longitudinal_momentum_requires_zero_potential
#print axioms positive_potential_accelerates_longitudinal_momentum
#print axioms massive_constraint_solved
#print axioms dynamic_energy_positive
#print axioms dynamic_energy_derivative_c
#print axioms dynamic_energy_derivative_L
#print axioms dynamic_clock_force_nonnegative
#print axioms dynamic_spatial_constraint
#print axioms dynamic_clock_monotone

end
end UnifiedTheory.Audit.KFCausalMatterArealReduction
