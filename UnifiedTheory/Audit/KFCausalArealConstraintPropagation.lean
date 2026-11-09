/-
  Exact propagation of the reduced classical spatial constraint, a
  counterexample for the earlier collocated graph discretization, and
  the homogeneous-density gauge needed to eliminate the local constraint.
  These statements do not prove PDE existence or quantum/continuum limits.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalArealConstraintPropagation
noncomputable section

def constraint (c cx lx p qx pi fx : ℝ) : ℝ := p*qx+pi*fx-c*lx+2*cx
def energy (k g h p qx pi fx : ℝ) : ℝ := p^2+g*qx^2+k*pi^2+h*fx^2
def energyX (k g h p px qx qxx pi pix fx fxx : ℝ) : ℝ :=
  2*(p*px+g*qx*qxx+k*pi*pix+h*fx*fxx)

/-- W=exp(2T+L)V/a and U=exp(2T+L)V'/a, hence W_x=W L_x+U phi_x.
The coefficients k,g,h are spatially constant, but may depend on time. -/
def constraintRate (c cx lx p px qx qxx pi pix fx fxx W U k g h : ℝ) : ℝ :=
  (g*(qxx/c-qx*cx/c^2))*qx+p*(px/c-p*cx/c^2)+
  (h*(fxx/c-fx*cx/c^2)-U/c)*fx+pi*(k*(pix/c-pi*cx/c^2))-
  (W/c)*lx-c*(energyX k g h p px qx qxx pi pix fx fxx/(2*c^2)+
    (W*lx+U*fx)/c^2-(energy k g h p qx pi fx+2*W)*cx/c^3)+
  2*((W*lx+U*fx)/c-W*cx/c^2)

theorem constraintRate_zero (c cx lx p px qx qxx pi pix fx fxx W U k g h : ℝ)
    (hc : c ≠ 0) : constraintRate c cx lx p px qx qxx pi pix fx fxx W U k g h = 0 := by
  unfold constraintRate energyX energy
  field_simp
  ring

/-- An actual time-derivative theorem at a fixed spatial point. Spatial
jets and their differentiated equations are supplied by a smooth solution. -/
theorem constraint_hasDerivAt_zero
    (c cx lx p qx pi fx : ℝ → ℝ) (t px qxx pix fxx W U k g h : ℝ)
    (hc : c t ≠ 0)
    (dc : HasDerivAt c (W/c t) t)
    (dcx : HasDerivAt cx ((W*lx t+U*fx t)/c t-W*cx t/(c t)^2) t)
    (dlx : HasDerivAt lx
      (energyX k g h (p t) px (qx t) qxx (pi t) pix (fx t) fxx/(2*(c t)^2)+
       (W*lx t+U*fx t)/(c t)^2-(energy k g h (p t) (qx t) (pi t) (fx t)+2*W)*cx t/(c t)^3) t)
    (dp : HasDerivAt p (g*(qxx/c t-qx t*cx t/(c t)^2)) t)
    (dqx : HasDerivAt qx (px/c t-p t*cx t/(c t)^2) t)
    (dpi : HasDerivAt pi (h*(fxx/c t-fx t*cx t/(c t)^2)-U/c t) t)
    (dfx : HasDerivAt fx (k*(pix/c t-pi t*cx t/(c t)^2)) t) :
    HasDerivAt (fun s => constraint (c s) (cx s) (lx s) (p s) (qx s) (pi s) (fx s)) 0 t := by
  have hd := (((dp.mul dqx).add (dpi.mul dfx)).sub (dc.mul dlx)).add (dcx.const_mul 2)
  convert hd using 1
  dsimp [energyX, energy]
  field_simp
  ring

theorem constraint_preserved_on_interval (D : ℝ → ℝ) (lo hi : ℝ)
    (hd : ∀ t ∈ Set.Icc lo hi, HasDerivAt D 0 t) (hlo : D lo = 0)
    (t : ℝ) (ht : t ∈ Set.Icc lo hi) : D t = 0 := by
  have hm : MonotoneOn D (Set.Icc lo hi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc lo hi)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [(hd x (interior_subset hx)).deriv]
  have ha : AntitoneOn D (Set.Icc lo hi) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [(hd x (interior_subset hx)).deriv]
  have hloMem : lo ∈ Set.Icc lo hi := ⟨le_rfl, ht.1.trans ht.2⟩
  exact le_antisymm (by simpa [hlo] using ha hloMem ht ht.1)
    (by simpa [hlo] using hm hloMem ht ht.1)

/-- At p=pi=phi=L=0,c=1, the central-difference constraint vanishes.
This is its time derivative under the previous unit-spacing bond model. -/
def latticeInitialRate (qm2 qm1 q qp1 qp2 : ℝ) : ℝ :=
  (qp1-2*q+qm1)*(qp1-qm1)/2-
  (((qp2-qp1)^2+(qp1-q)^2)/4-((q-qm1)^2+(qm1-qm2)^2)/4)/2

theorem lattice_constraint_counterexample : latticeInitialRate 0 0 0 1 0 = 1/4 := by
  norm_num [latticeInitialRate]

/-- With c spatially homogeneous, the required shift gradient redistributes
the inhomogeneous potential force into the mean clock force. -/
theorem homogeneous_clock_shift (c W meanW : ℝ) (hc : c ≠ 0) :
    W/c+c*((meanW-W)/c^2)=meanW/c := by field_simp; ring

theorem homogeneous_density_constraint (c p qx pi fx lx : ℝ) (hc : c ≠ 0) :
    constraint c 0 lx p qx pi fx = 0 ↔ lx=(p*qx+pi*fx)/c := by
  unfold constraint
  constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith

/-- The mixed-partial compatibility reconstructs the metric evolution
when the mean clock is evolved and the required shift is retained. -/
theorem reconstructed_source_rate (c meanW W U lx p px qx qxx pi pix fx fxx vx v g : ℝ)
    (hc : c ≠ 0) (hconstraint : p*qx+pi*fx=c*lx)
    (hshift : vx=(meanW-W)/c^2) :
    ((g*qxx/c+vx*p+v*px)*qx+p*(px/c+vx*qx+v*qxx)+
      (g*fxx/c-U/c+vx*pi+v*pix)*fx+pi*(pix/c+vx*fx+v*fxx))/c-
      (p*qx+pi*fx)*meanW/c^3 =
    (p*px+g*qx*qxx+pi*pix+g*fx*fxx)/c^2-U*fx/c^2+
      (meanW-2*W)*lx/c^2+v*(px*qx+p*qxx+pix*fx+pi*fxx)/c := by
  rw [hshift]
  field_simp
  linear_combination (meanW-2*W)*hconstraint

#print axioms constraintRate_zero
#print axioms constraint_hasDerivAt_zero
#print axioms constraint_preserved_on_interval
#print axioms lattice_constraint_counterexample
#print axioms homogeneous_clock_shift
#print axioms homogeneous_density_constraint
#print axioms reconstructed_source_rate

end
end UnifiedTheory.Audit.KFCausalArealConstraintPropagation
