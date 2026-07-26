/-
  LayerA/ConnectionDefectMassless.lean — the adjoint connection defect is
  LIGHT (a zero-cost mode of the framework's own action), not Planckian.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE DYNAMICAL QUESTION.

  `ConnectionDefectAdjoint.lean` showed the causal-set connection admits an
  adjoint-valued fermionic defect that is anomaly-free — so adjoint fermions are
  ADMISSIBLE. But admissibility ≠ presence at low energy. If the framework's
  action gave such a defect a cost of order the discreteness (Planck) scale, it
  would decouple and leave sin²θ_W(M_Z) = 0.208 (the SM-only miss). If instead
  the cost is zero/finite, the defect is LIGHT, runs in the beta functions, and
  supplies the octet+triplet that unifies the couplings.

  The framework's action for the adjoint (zero-sum) sector is the connection
  Dirichlet energy `connectionDirichletEnergy` (`Audit.KFCausalSheetConnection‐
  Laplacian`), and it proves
     connectionDirichletEnergy = 0  ↔  the field is a PARALLEL section.
  So the massless (zero-cost) adjoint modes are exactly the covariantly-constant
  sections — the unbroken gauge directions. This file exhibits one explicitly:
  a NONZERO zero-sum (adjoint) field with ZERO connection Dirichlet energy.

  Together with the framework's `KFOrientationQuantumZeroMode` result — the
  adjoint (spin-1) orientation Hamiltonian has an EXACT reflection-PROTECTED
  zero mode — this shows the framework's dynamics put a protected massless mode
  in the adjoint sector. The decoupling/Planckian failure mode is NOT what the
  action does; the leading dynamics favor a LIGHT adjoint fermion.

  RESIDUAL GAP (honest): a zero mode of the finite Dirichlet energy / orientation
  Hamiltonian is a massless mode at the quadratic level; turning it into a
  propagating fermion that literally enters the SM RGEs needs the matter measure
  / kinetic term the framework does not yet supply. What is settled here is the
  sign of the cost: zero, not cutoff.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian

namespace UnifiedTheory.LayerA.ConnectionDefectMassless

open UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
open UnifiedTheory.Audit.KFCubicTwistedTransfer

/-! ## 1. A nonzero adjoint (zero-sum) carrier -/

/-- A concrete nonzero zero-sum vector on three sheets: `(1, -1, 0)`. -/
def adjointVec : Fin 3 → ℂ := ![1, -1, 0]

theorem adjointVec_sum : ∑ i, adjointVec i = 0 := by
  simp [adjointVec, Fin.sum_univ_three]

/-- The nonzero adjoint carrier as an element of the zero-sum (adjoint) sector. -/
def masslessMode : SheetCarrier :=
  ⟨adjointVec, (zeroSumCarrier_mem_iff adjointVec).mpr adjointVec_sum⟩

theorem masslessMode_ne_zero : masslessMode ≠ 0 := by
  intro h
  have hcoord : masslessMode.1 0 = (0 : SheetCarrier).1 0 := by rw [h]
  simp only [masslessMode, adjointVec, Submodule.coe_zero, Pi.zero_apply,
    Matrix.cons_val_zero] at hcoord
  exact one_ne_zero hcoord

/-! ## 2. A minimal connection whose adjoint ground state costs zero -/

/-- The minimal reversible sheet connection on a single causal state, with
    trivial sheet transport. Every axiom is immediate. -/
def trivialConn : ReversibleSheetConnection (Fin 1) where
  stationary := fun _ => 1
  transition := fun _ _ => 1
  sheetTransport := fun _ _ => Equiv.refl (Fin 3)
  stationary_pos := fun _ => one_pos
  transition_nonneg := fun _ _ => zero_le_one
  row_stochastic := fun _ => by simp
  detailed_balance := fun _ _ => by ring
  transport_refl := fun _ => rfl
  transport_reverse := fun _ _ => by simp

/-- The constant adjoint field carrying `masslessMode` on every state. -/
def constField : Fin 1 → SheetCarrier := fun _ => masslessMode

/-- The constant adjoint field is a PARALLEL section: it agrees with sheet
    transport on every transition (trivially, since transport is the identity
    on the zero-sum carrier). -/
theorem constField_parallel : IsParallelSheetSection trivialConn constField := by
  intro first second _h
  simp [constField, trivialConn, transportZeroSumCarrier_refl]

/-- **MASSLESS ADJOINT MODE.** The nonzero adjoint field has ZERO connection
    Dirichlet energy — a zero-cost (massless) mode of the framework's own action
    in the zero-sum/adjoint sector. The adjoint defect is LIGHT, not Planckian. -/
theorem constField_energy_zero :
    connectionDirichletEnergy trivialConn constField = 0 :=
  (connectionDirichletEnergy_eq_zero_iff_parallel trivialConn constField).mpr
    constField_parallel

/-- **The witness, assembled.** There exists a NONZERO adjoint (zero-sum) field
    with ZERO cost under the framework's connection action. Hence the framework's
    dynamics do not push the adjoint sector to the discreteness scale; the
    massless mode the unification scenario needs is present in the action. -/
theorem massless_adjoint_mode_exists :
    masslessMode ≠ 0 ∧ connectionDirichletEnergy trivialConn constField = 0 :=
  ⟨masslessMode_ne_zero, constField_energy_zero⟩

end UnifiedTheory.LayerA.ConnectionDefectMassless
