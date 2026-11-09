/- Domain of the exact classical positive-clock vacuum branch. Finite
matrix evolution is global, but a global positive classical clock is not
available for every admissible initial datum. This is a domain obstruction
to an unrestricted classical limit, not an obstruction to finite unitarity. -/
import UnifiedTheory.Audit.KFCausalClockEnergyObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalVacuumClockDomain
noncomputable section

def vacuumRate (c L t : ℝ) : ℝ := Real.exp (2*t+L)/c

/-- For H=c/2+exp(2t+L)/c and {c,L}=1, the potential contribution
V=exp(2t+L)/c obeys V'=(3/2)V along the canonical equations. -/
theorem vacuum_rate_derivative (c L : ℝ → ℝ) (t : ℝ) (hc : c t ≠ 0)
    (hdc : HasDerivAt c (vacuumRate (c t) (L t) t) t)
    (hdL : HasDerivAt L (-1/2+vacuumRate (c t) (L t) t/c t) t) :
    HasDerivAt (fun s => vacuumRate (c s) (L s) s)
      ((3/2)*vacuumRate (c t) (L t) t) t := by
  have hd := ((((hasDerivAt_id t).const_mul 2).add hdL).exp).div hdc hc
  convert hd using 1
  dsimp [vacuumRate]
  field_simp
  ring

theorem rate_solution (V : ℝ → ℝ) (v₀ : ℝ) (hinit : V 0=v₀)
    (hV : ∀ t, HasDerivAt V ((3/2)*V t) t) (t : ℝ) :
    V t=v₀*Real.exp ((3/2)*t) := by
  have hd (s : ℝ) : HasDerivAt (fun z => Real.exp (-(3/2)*z)*V z) 0 s := by
    convert (((hasDerivAt_id s).const_mul (-(3/2))).exp).mul (hV s) using 1
    dsimp
    ring
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [mul_zero,Real.exp_zero,one_mul,hinit] at he
  have hp : Real.exp ((3/2)*t)*Real.exp (-(3/2)*t)=1 := by
    rw [← Real.exp_add,show (3/2)*t+(-(3/2))*t=0 by ring,Real.exp_zero]
  have hh := congrArg (fun x => Real.exp ((3/2)*t)*x) he
  dsimp only at hh
  rw [← mul_assoc,hp,one_mul] at hh
  simpa only [mul_comm] using hh

theorem clock_solution (c V : ℝ → ℝ) (c₀ v₀ : ℝ) (hc₀ : c 0=c₀) (hv₀ : V 0=v₀)
    (hc : ∀ t, HasDerivAt c (V t) t)
    (hV : ∀ t, HasDerivAt V ((3/2)*V t) t) (t : ℝ) :
    c t=c₀+(2/3)*v₀*(Real.exp ((3/2)*t)-1) := by
  have hd (s : ℝ) : HasDerivAt (fun z => c z-(2/3)*V z) 0 s := by
    convert (hc s).sub ((hV s).const_mul (2/3)) using 1
    dsimp
    ring
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [hc₀,hv₀,rate_solution V v₀ hv₀ hV t] at he
  linarith

/-- The positive initial data c(0)=1, exp(L(0))=3 cannot have an
everywhere-positive global classical solution. The explicit branch
reaches c=0 at t=-(2/3)log 2. The contradiction below uses t=-1,
so it does not need a numerical approximation to that crossing time. -/
theorem no_global_positive_vacuum_branch :
    ¬∃ c L : ℝ → ℝ,
      (∀ t, 0 < c t) ∧ c 0=1 ∧ Real.exp (L 0)=3 ∧
      (∀ t, HasDerivAt c (vacuumRate (c t) (L t) t) t) ∧
      (∀ t, HasDerivAt L (-1/2+vacuumRate (c t) (L t) t/c t) t) := by
  rintro ⟨c,L,hpos,hc₀,hL₀,hc,hL⟩
  let V := fun t => vacuumRate (c t) (L t) t
  have hv₀ : V 0=3 := by simp [V,vacuumRate,hc₀,hL₀]
  have hV (t : ℝ) : HasDerivAt V ((3/2)*V t) t :=
    vacuum_rate_derivative c L t (ne_of_gt (hpos t)) (hc t) (hL t)
  have hs := clock_solution c V 1 3 hc₀ hv₀ hc hV (-1)
  have hp : Real.exp (3/2)*Real.exp (-(3/2))=1 := by rw [← Real.exp_add]; simp
  have hbig : 0 ≤ Real.exp (3/2)-(5/2) := by linarith [Real.add_one_le_exp (3/2)]
  have hsmall : Real.exp (-(3/2))<1/2 := by
    nlinarith [mul_nonneg hbig (Real.exp_pos (-(3/2))).le]
  norm_num at hs
  linarith [hpos (-1)]

def branchClock (t : ℝ) : ℝ := 2*Real.exp ((3/2)*t)-1
def branchLongitudinal (t : ℝ) : ℝ := Real.log (3*branchClock t)-t/2

theorem branch_clock_derivative (t : ℝ) :
    HasDerivAt branchClock (3*Real.exp ((3/2)*t)) t := by
  convert ((((hasDerivAt_id t).const_mul (3/2)).exp).const_mul 2).sub_const 1 using 1
  dsimp [branchClock]
  ring

theorem branch_rate (t : ℝ) (hc : 0 < branchClock t) :
    vacuumRate (branchClock t) (branchLongitudinal t) t=3*Real.exp ((3/2)*t) := by
  unfold vacuumRate branchLongitudinal
  rw [show 2*t+(Real.log (3*branchClock t)-t/2)=
      Real.log (3*branchClock t)+(3/2)*t by ring,
    Real.exp_add,Real.exp_log (by positivity : 0 < 3*branchClock t)]
  field_simp

/-- This explicitly supplies a solution wherever c>0; the global
obstruction is not caused by inconsistent initial data. -/
theorem branch_solves_equations (t : ℝ) (hc : 0 < branchClock t) :
    HasDerivAt branchClock (vacuumRate (branchClock t) (branchLongitudinal t) t) t ∧
    HasDerivAt branchLongitudinal
      (-1/2+vacuumRate (branchClock t) (branchLongitudinal t) t/branchClock t) t := by
  rw [branch_rate t hc]
  refine ⟨branch_clock_derivative t,?_⟩
  have hd := (((branch_clock_derivative t).const_mul 3).log
    (ne_of_gt (show 0 < 3*branchClock t by positivity))).sub ((hasDerivAt_id t).div_const 2)
  convert hd using 1
  dsimp [branchLongitudinal]
  field_simp
  ring

theorem branch_initial_data : branchClock 0=1 ∧ Real.exp (branchLongitudinal 0)=3 := by
  norm_num [branchClock,branchLongitudinal,Real.exp_log]

theorem branch_positive_future (t : ℝ) (ht : 0 ≤ t) : 0 < branchClock t := by
  have he : 1 ≤ Real.exp ((3/2)*t) := Real.one_le_exp_iff.mpr (by positivity)
  dsimp [branchClock]
  linarith

theorem branch_boundary : branchClock (-(2/3)*Real.log 2)=0 := by
  unfold branchClock
  rw [show (3/2)*(-(2/3)*Real.log 2)= -Real.log 2 by ring,
    Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  norm_num

theorem branch_energy (t : ℝ) (hc : 0 < branchClock t) :
    branchClock t/2+vacuumRate (branchClock t) (branchLongitudinal t) t=
      4*Real.exp ((3/2)*t)-1/2 := by
  rw [branch_rate t hc,branchClock]
  ring

theorem branch_energy_bound_before_zero (t : ℝ) (hc : 0 < branchClock t) (ht : t ≤ 0) :
    3/2 < branchClock t/2+vacuumRate (branchClock t) (branchLongitudinal t) t ∧
      branchClock t/2+vacuumRate (branchClock t) (branchLongitudinal t) t ≤ 7/2 := by
  rw [branch_energy t hc]
  have he : Real.exp ((3/2)*t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  dsimp [branchClock] at hc
  constructor <;> linarith

#print axioms vacuum_rate_derivative
#print axioms rate_solution
#print axioms clock_solution
#print axioms no_global_positive_vacuum_branch
#print axioms branch_solves_equations
#print axioms branch_initial_data
#print axioms branch_positive_future
#print axioms branch_boundary
#print axioms branch_energy
#print axioms branch_energy_bound_before_zero

end
end UnifiedTheory.Audit.KFCausalVacuumClockDomain
