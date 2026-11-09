/- The six-flavor spin source for arbitrary finite capacity and arbitrary
real radial weights. The zero-charge source hypothesis in constraint
reconstruction is proved here from concrete finite ladder matrices. -/
import UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
import UnifiedTheory.Audit.KFCausalGradedSpinSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSpinSourceIdentity
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction

abbrev State (R : ℕ) := Active 6 R

def occupationCharge {R : ℕ} (v : Occupation 6 R) : ℤ :=
  (v 1 : ℕ)-(v 2 : ℤ)+(v 3 : ℤ)-(v 4 : ℤ)

def charge {R : ℕ} (v : State R) : ℤ := occupationCharge v.val

def ladder {R : ℕ} (r : ℕ → ℝ) (a : Fin 6) : Matrix (State R) (State R) ℂ :=
  compress (annihilator r a)

def flavorCharge (a : Fin 6) : ℤ := ![0,1,-1,1,-1,0] a

theorem charge_lower {R : ℕ} (a : Fin 6) (v : Occupation 6 R) (hv : 0 < (v a : ℕ)) :
    occupationCharge (lower a v)=occupationCharge v-flavorCharge a := by
  fin_cases a <;> simp_all [occupationCharge,lower,flavorCharge] <;> omega

theorem ladder_charge {R : ℕ} (r : ℕ → ℝ) (a : Fin 6) :
    HasCharge (charge (R := R)) (-flavorCharge a) (ladder r a) := by
  intro i j hij
  by_cases h : 0 < (j.val a : ℕ) ∧ i.val=lower a j.val
  · have he := charge_lower a j.val h.1
    rw [← h.2] at he
    exact False.elim (hij (by unfold charge; omega))
  · exact if_neg h

def source (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  spinSource hbar (ladder r 1) (ladder r 2)
    (ladder r 3) (ladder r 4) (ladder r 5)

def coefficient {R : ℕ} (r : ℕ → ℝ) (hbar : ℝ) (v : State R) : ℂ :=
  (hbar/2 : ℂ)*((weight R r (total v.val) : ℂ)^2+(weight R r (total v.val+1) : ℂ)^2)

theorem loops_ladder {R : ℕ} (r : ℕ → ℝ) (a : Fin 6) :
    loops (ladder (R := R) r a)=
      Matrix.diagonal (fun v =>
        ((((v.val a : ℝ)+1)*weight R r (total v.val+1)^2+(v.val a : ℝ)*weight R r (total v.val)^2 : ℝ) : ℂ)) := by
  rw [loops,ladder,active_square_adjoint,active_adjoint_square]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [h]

/-- Exact finite-capacity identity, including N=R. No CCR or asymptotic
approximation is used. The radial weights can have either sign. -/
theorem source_mean (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    meanPart charge (source R r hbar)=
      Matrix.diagonal (fun v => coefficient r hbar v*(charge v : ℂ)) := by
  have hg (a : Fin 6) := ladder_charge (R := R) r a
  rw [source,spinSource_mean charge hbar _ _ _ _ _
    (by simpa [flavorCharge] using hg 1) (by simpa [flavorCharge] using hg 2)
    (by simpa [flavorCharge] using hg 3) (by simpa [flavorCharge] using hg 4)
    (by simpa [flavorCharge] using hg 5)]
  simp only [loops_ladder]
  ext i j
  by_cases hij : i=j
  · subst j
    simp [coefficient,charge,occupationCharge]
    ring
  · simp [hij]

theorem source_annihilates_zero (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    meanPart charge (source R r hbar)*sector charge 0=0 := by
  rw [source_mean]
  exact charge_weighted_mean_annihilates_zero charge (coefficient r hbar)

/-- At the highest retained occupation the upward term is exactly zero. -/
theorem coefficient_at_capacity {R : ℕ} (r : ℕ → ℝ) (hbar : ℝ) (v : State R)
    (hv : total v.val=R) : coefficient r hbar v=(hbar/2 : ℂ)*(r R : ℂ)^2 := by
  simp [coefficient,hv,weight]

/-- The earlier preservation theorem with its spin-source hypothesis
removed. This endpoint uses a diagonal positive clock in the occupation
basis; transporting to another charge-preserving clock basis is separate. -/
theorem concrete_constraint_after_step (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (c : State R → ℝ) (hc : ∀ i, 0 < c i)
    (base H : Matrix (State R) (State R) ℂ) (hb : spatialDeriv charge base=0)
    (z : ℂ) (v : State R → ℂ) (hv : (sector charge 0).mulVec v=v) :
    (source R r hbar-jordan c (spatialDeriv charge
      (reconstructedL c charge base (source R r hbar)))).mulVec
      ((NormedSpace.exp (z • dephase charge H)).mulVec v)=0 :=
  reconstructed_constraint_after_step c hc charge base (source R r hbar) H hb
    (source_annihilates_zero R r hbar) z v hv

/-- The source still annihilates the physical sector after any
charge-preserving change of basis (in particular, a unitary clock
spectral basis). Its coefficient need no longer be diagonal. -/
theorem transported_source_annihilates_zero (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (U : Matrix (State R) (State R) ℂ) (hU : HasCharge charge 0 U) :
    meanPart charge (Uᴴ*source R r hbar*U)*sector charge 0=0 := by
  rw [mean_conjugate charge U _ hU]
  calc
    (Uᴴ*meanPart charge (source R r hbar)*U)*sector charge 0 =
        Uᴴ*(meanPart charge (source R r hbar)*(U*sector charge 0)) := by simp [mul_assoc]
    _ = Uᴴ*(meanPart charge (source R r hbar)*(sector charge 0*U)) := by
      rw [(neutral_commutes_sector charge U hU 0).eq]
    _ = 0 := by rw [← mul_assoc (meanPart charge (source R r hbar)),
                    source_annihilates_zero,zero_mul,mul_zero]

/-- Concrete spin source, reconstructed local constraint and preserved
zero-charge sector in a supplied positive clock / charge basis. Existence
of the chosen clock spectral basis is not established by this theorem. -/
theorem transported_constraint_after_step (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (U : Matrix (State R) (State R) ℂ) (hU : HasCharge charge 0 U)
    (c : State R → ℝ) (hc : ∀ i, 0 < c i)
    (base H : Matrix (State R) (State R) ℂ) (hb : spatialDeriv charge base=0)
    (z : ℂ) (v : State R → ℂ) (hv : (sector charge 0).mulVec v=v) :
    (Uᴴ*source R r hbar*U-jordan c (spatialDeriv charge
      (reconstructedL c charge base (Uᴴ*source R r hbar*U)))).mulVec
      ((NormedSpace.exp (z • dephase charge H)).mulVec v)=0 :=
  reconstructed_constraint_after_step c hc charge base _ H hb
    (transported_source_annihilates_zero R r hbar U hU) z v hv

#print axioms transported_source_annihilates_zero
#print axioms transported_constraint_after_step

#print axioms charge_lower
#print axioms ladder_charge
#print axioms source_mean
#print axioms source_annihilates_zero
#print axioms coefficient_at_capacity
#print axioms concrete_constraint_after_step

end
end UnifiedTheory.Audit.KFCausalSpinSourceIdentity
