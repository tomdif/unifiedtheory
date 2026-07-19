/-
  LayerB/MandelstamTamm.lean
  ───────────────────────────

  The Mandelstam–Tamm energy-time uncertainty relation, derived as a
  direct corollary of the Robertson uncertainty bound by substituting
  the Heisenberg equation of motion `dA/dt = i·[H, A]`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `HeisenbergSnapshot n` structure bundling a Hamiltonian H, an
       observable A, and its instantaneous time derivative `dA_dt`
       satisfying the Heisenberg equation.
    2. `mandelstam_tamm` :  for any ℂ density matrix ρ in dim n and
       any Heisenberg snapshot (H, A, dA_dt) with H, A Hermitian:

           Var_ρ(H) · Var_ρ(A)  ≥  (1/4) · ( Re(Tr(ρ · dA_dt)) )²

       The right-hand side is the squared rate of change of the
       expectation ⟨A⟩_ρ = Re(Tr(ρ·A)).  In sqrt form (not stated
       here) this is the energy-time uncertainty
           ΔE · ΔA  ≥  (ℏ/2) · |d⟨A⟩/dt| .

  SCOPE:
    – Finite-dimensional, Heisenberg-picture.
    – `dA_dt` is supplied as a hypothesis along with the Heisenberg
      equation `dA_dt = i·[H,A]`.  This sidesteps deriv-of-matrix
      machinery and keeps the proof algebraic.
    – Uses units where ℏ = 1; the inequality has the factor 1/4
      rather than (ℏ/2)².
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import Mathlib.Analysis.Complex.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RobertsonSchrodinger

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. Heisenberg snapshot -/

/-- A "Heisenberg snapshot" at a single time t: a Hamiltonian H, an
    observable A, and the instantaneous derivative `dA_dt` satisfying
    the Heisenberg equation of motion `dA/dt = i · [H, A]` (in units
    where ℏ = 1).

    All three matrices live in `Matrix (Fin n) (Fin n) ℂ`.  H and A
    are Hermitian; `dA_dt` is then anti-Hermitian (consequence of the
    Heisenberg equation, not needed as a separate field). -/
structure HeisenbergSnapshot (n : ℕ) where
  H : Matrix (Fin n) (Fin n) ℂ
  A : Matrix (Fin n) (Fin n) ℂ
  dA_dt : Matrix (Fin n) (Fin n) ℂ
  hH : H.IsHermitian
  hA : A.IsHermitian
  hHeisenberg : dA_dt = Complex.I • ComplexDensityMatrix.commutator H A

/-! ## 2. The Mandelstam–Tamm bound -/

/-- **Mandelstam–Tamm energy-time uncertainty (finite-dim form).**

    Given a complex density matrix ρ in dimension n, and any Heisenberg
    snapshot (H, A, dA_dt) with H and A Hermitian and `dA_dt = i·[H,A]`,

        Var_ρ(H) · Var_ρ(A)  ≥  (1/4) · ( Re(Tr(ρ · dA_dt)) )² .

    Reading: the product of the energy variance and the observable
    variance is at least (1/4) times the squared rate of change of
    the expectation ⟨A⟩_ρ.  Taking square roots gives the standard

        Δ E · Δ A  ≥  (ℏ/2) · |d⟨A⟩/dt|

    (with ℏ = 1 in these units).

    Proof: direct corollary of `robertson_uncertainty` applied to
    (H, A), with the Heisenberg substitution
    `Tr(ρ · dA_dt) = i · Tr(ρ · [H, A])` translating the commutator
    bound into the expectation-derivative bound.  Uses that
    `Tr(ρ · [H, A])` is purely imaginary
    (`trace_rho_commutator_re_zero`). -/
theorem mandelstam_tamm
    {n : ℕ} (ρ : ComplexDensityMatrix n) (HS : HeisenbergSnapshot n) :
    ComplexDensityMatrix.variance ρ HS.H * ComplexDensityMatrix.variance ρ HS.A
      ≥ (1 / 4) * ((Matrix.trace (ρ.M * HS.dA_dt)).re)^2 := by
  -- Robertson bound on the commutator term
  have h_robertson := ComplexDensityMatrix.robertson_uncertainty ρ HS.hH HS.hA
  -- Re(Tr(ρ·[H,A])) = 0  (purely imaginary)
  have h_re_zero :=
    ComplexDensityMatrix.trace_rho_commutator_re_zero ρ HS.hH HS.hA
  -- Heisenberg substitution:  Tr(ρ · dA_dt) = i · Tr(ρ · [H,A])
  have h_tr_dA : Matrix.trace (ρ.M * HS.dA_dt)
              = Complex.I * Matrix.trace (ρ.M * ComplexDensityMatrix.commutator HS.H HS.A) := by
    rw [HS.hHeisenberg, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  -- Algebraic identity:
  --   normSq z  =  ((i·z).re)²    when z.re = 0
  set z := Matrix.trace (ρ.M * ComplexDensityMatrix.commutator HS.H HS.A) with hz_def
  have h_normSq_eq : Complex.normSq z = ((Matrix.trace (ρ.M * HS.dA_dt)).re)^2 := by
    rw [h_tr_dA]
    -- Goal: normSq z = ((I * z).re)^2
    rw [Complex.normSq_apply, h_re_zero]
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
    ring
  -- Chain: Var(H)·Var(A) ≥ (1/4)·normSq z = (1/4)·((Tr(ρ·dA_dt)).re)²
  rw [← h_normSq_eq]
  exact h_robertson

end UnifiedTheory.LayerB.RobertsonSchrodinger
