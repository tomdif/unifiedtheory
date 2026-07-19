/-
  LayerB/PeierlsBogoliubov.lean
  ─────────────────────────────

  **The Peierls–Bogoliubov inequality**, discharging the named-`Prop`
  hole `PeierlsBogoliubov_Target` of `GibbsVariational.lean` as a REAL
  theorem, assembled entirely from the now-proved Gibbs variational
  principle (`gibbs_variational_target`, `freeEnergy_gibbs_eq`).

  ## Statement

  For Hamiltonians `H` and a perturbation `ΔH` (both Hermitian),

      log Tr e^{H+ΔH}  ≥  log Tr e^{H}  +  ⟨ΔH⟩_{ρ_H} ,

  where `⟨ΔH⟩_{ρ_H}` is the thermal average of the perturbation in the
  **unperturbed** Gibbs state `ρ_H`.  In the partition-function notation
  of the existing stack, `Tr e^{K} = Z(-1, K)`, so this is exactly

      `PeierlsBogoliubov_Target H ΔH (expectation ρ_H ΔH)`.

  ## Derivation (the variational principle is the engine)

  Work at inverse temperature `β = 1`, temperature `T = 1`, with the
  SIGN-FLIPPED Hamiltonian `-K`, so that

      Z(1, -K)  =  ∑ exp(λ_i(K))  =  Z(-1, K) = Tr e^{K}.            (♭)

  The unperturbed Gibbs state is `ρ_H := gibbsDensity 1 (-H)`.  Apply the
  variational principle (against the closed form `-T log Z`) for the
  *perturbed* Hamiltonian `-(H+ΔH)` evaluated at `ρ_H`:

      gibbsMinimum 1 (Z(1,-(H+ΔH)))  ≤  F_{-(H+ΔH)}(ρ_H).            (V)

  The unperturbed self-consistency `freeEnergy_gibbs_eq` gives

      F_{-H}(ρ_H)  =  gibbsMinimum 1 (Z(1,-H)).                      (S)

  Subtracting (S) from (V) and using free-energy linearity in the
  Hamiltonian, `F_{-(H+ΔH)}(ρ_H) − F_{-H}(ρ_H) = ⟨-ΔH⟩_{ρ_H}
  = −⟨ΔH⟩_{ρ_H}` (the entropy terms cancel), yields

      −log Z(1,-(H+ΔH)) + log Z(1,-H)  ≤  −⟨ΔH⟩_{ρ_H},

  i.e., via (♭),

      log Z(-1,H+ΔH)  ≥  log Z(-1,H) + ⟨ΔH⟩_{ρ_H}.                  ∎

  ## Scope / honesty

    * Finite-dimensional, `[Nonempty (Fin n)]` (needed for `Z > 0`).
    * `H`, `ΔH` Hermitian (so `-H`, `-(H+ΔH)` are Hermitian and the
      Gibbs machinery applies).
    * The thermal average `⟨ΔH⟩_{ρ_H}` is the genuine expectation of
      `ΔH` in the unperturbed Gibbs state `gibbsDensity 1 (-H)`.
    * No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.GibbsVariationalFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PeierlsBogoliubov

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.GibbsVariational
open UnifiedTheory.LayerB.GibbsVariationalFull
open UnifiedTheory.LayerB.QuantumJarzynski (partitionFunction partitionFunction_pos_of_nonempty)

variable {n : ℕ}

/-! ## 0.  The sign-flip bridge for the partition function. -/

/-- **Sign-flip bridge** (♭):  `Z(-1, K) = Z(1, -K)`.

    Both equal `Tr e^{K} = ∑ exp(λ_i(K))`.  Proved directly from the
    `cfc` definition: `Z(1,-K) = Re Tr (cfc (x ↦ e^{-x}) (-K))`, and
    `cfc_comp_neg` rewrites `cfc (x ↦ e^{-x}) (-K) = cfc (x ↦ e^{-(-x)}) K
    = cfc (x ↦ e^{x}) K`, which is `Z(-1,K) = Re Tr (cfc (x ↦ e^{x}) K)`. -/
theorem partitionFunction_neg_one_eq
    (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.IsHermitian) :
    partitionFunction (-1) K = partitionFunction 1 (-K) := by
  unfold partitionFunction
  -- Bring both integrands to the same function `x ↦ e^{x}` on `K`.
  have hSA : IsSelfAdjoint K := hK
  -- cfc (x ↦ e^{-1·x}) (-K) = cfc (x ↦ e^{-1·(-x)}) K  via cfc_comp_neg.
  have hcomp :
      cfc (fun x : ℝ => Real.exp (-(1 : ℝ) * x)) (-K)
        = cfc (fun x : ℝ => Real.exp (-(1 : ℝ) * (-x))) K := by
    rw [← cfc_comp_neg (R := ℝ) (fun x : ℝ => Real.exp (-(1 : ℝ) * x)) K]
  rw [hcomp]
  -- The two integrands coincide: e^{-(-1)·x} = e^{x} = e^{-1·(-x)}.
  have hfun :
      (fun x : ℝ => Real.exp (-(-1 : ℝ) * x))
        = (fun x : ℝ => Real.exp (-(1 : ℝ) * (-x))) := by
    funext x; congr 1; ring
  rw [hfun]

/-- `partitionFunction (-1) K > 0` (it is `Tr e^{K} > 0`).  Reduced to
    `partitionFunction_pos` via the sign-flip bridge. -/
theorem partitionFunction_neg_one_pos [Nonempty (Fin n)]
    (K : Matrix (Fin n) (Fin n) ℂ) (hK : K.IsHermitian) :
    0 < partitionFunction (-1) K := by
  rw [partitionFunction_neg_one_eq K hK]
  exact UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
    1 (-K) hK.neg

/-! ## 1.  The unperturbed Gibbs state and its free-energy self-consistency. -/

/-- **The (β = 1) thermal Gibbs state of the unperturbed Hamiltonian.**

    Modelled on the SIGN-FLIPPED Hamiltonian `-H` so that the partition
    function is `Z(1,-H) = Tr e^{H} = Z(-1,H)`.  This is the state in
    which the Peierls–Bogoliubov thermal average is taken. -/
noncomputable def unperturbedGibbs
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction 1 (-H)) :
    ComplexDensityMatrix n :=
  gibbsDensity 1 (-H) hH.neg hZ

/-! ## 2.  Peierls–Bogoliubov as a real theorem. -/

/-- **Peierls–Bogoliubov inequality.**

      log Tr e^{H+ΔH}  ≥  log Tr e^{H}  +  ⟨ΔH⟩_{ρ_H},

    with `⟨ΔH⟩_{ρ_H} = expectation (gibbsDensity 1 (-H)) ΔH` the thermal
    average of the perturbation in the unperturbed Gibbs state.

    This discharges `PeierlsBogoliubov_Target H ΔH ⟨ΔH⟩_{ρ_H}`, assembled
    from the proved variational principle `gibbs_variational_target` and
    the self-consistency `freeEnergy_gibbs_eq`. -/
theorem peierls_bogoliubov [Nonempty (Fin n)]
    (H ΔH : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hΔH : ΔH.IsHermitian) :
    PeierlsBogoliubov_Target H ΔH
      (ComplexDensityMatrix.expectation
        (gibbsDensity 1 (-H) hH.neg
          (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
            1 (-H) hH.neg)) ΔH) := by
  classical
  -- Hermiticity of the sign-flipped Hamiltonians.
  have hnegH : (-H).IsHermitian := hH.neg
  have hHΔH : (H + ΔH).IsHermitian := hH.add hΔH
  have hnegHΔH : (-(H + ΔH)).IsHermitian := hHΔH.neg
  -- Positivity of the relevant partition functions (β = 1).
  have hZH : 0 < partitionFunction 1 (-H) :=
    UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
      1 (-H) hnegH
  have hZHΔH : 0 < partitionFunction 1 (-(H + ΔH)) :=
    UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
      1 (-(H + ΔH)) hnegHΔH
  -- The unperturbed Gibbs state ρ_H = gibbsDensity 1 (-H).
  set ρH : ComplexDensityMatrix n := gibbsDensity 1 (-H) hnegH hZH with hρH_def
  have hρH_pos : ρH.M.PosDef := by rw [hρH_def]; exact gibbsDensity_posDef 1 (-H) hnegH hZH
  -- Temperature data: T = 1, β = 1.
  have hTβ : (1 : ℝ) * (1 : ℝ) = 1 := by norm_num
  have hT : (0 : ℝ) ≤ 1 := by norm_num
  -- (V) Variational principle for the PERTURBED Hamiltonian -(H+ΔH) at ρ_H.
  have hV : Gibbs_Variational_Target ρH (-(H + ΔH)) 1
              (partitionFunction 1 (-(H + ΔH))) :=
    gibbs_variational_target ρH 1 (-(H + ΔH)) hnegHΔH hZHΔH 1 hTβ hT hρH_pos
  -- Unfold (V): gibbsMinimum 1 Z_{pert} ≤ F_{-(H+ΔH)}(ρ_H).
  have hV' : gibbsMinimum 1 (partitionFunction 1 (-(H + ΔH)))
              ≤ freeEnergy ρH (-(H + ΔH)) 1 := hV
  -- (S) Self-consistency: F_{-H}(ρ_H) = gibbsMinimum 1 Z_{unpert}.
  have hS : freeEnergy ρH (-H) 1 = gibbsMinimum 1 (partitionFunction 1 (-H)) := by
    rw [hρH_def]; exact freeEnergy_gibbs_eq 1 (-H) hnegH hZH 1 hTβ
  -- Free-energy difference = ⟨-ΔH⟩ = -⟨ΔH⟩ (entropy terms cancel).
  have hdiff : freeEnergy ρH (-(H + ΔH)) 1 - freeEnergy ρH (-H) 1
                = - ComplexDensityMatrix.expectation ρH ΔH := by
    unfold freeEnergy
    have hsplit : ρH.expectation (-(H + ΔH))
                    = ρH.expectation (-H) - ρH.expectation ΔH := by
      have hrw : (-(H + ΔH)) = (-H) - ΔH := by abel
      rw [hrw, ComplexDensityMatrix.expectation_sub]
    rw [hsplit]; ring
  -- Combine (V'), (S), (hdiff) into the partition-function inequality.
  -- From hV' and hS:  gibbsMin Z_pert ≤ F_{-(H+ΔH)}(ρ_H)
  --                    = F_{-H}(ρ_H) - ⟨ΔH⟩ = gibbsMin Z_unpert - ⟨ΔH⟩.
  have hkey : gibbsMinimum 1 (partitionFunction 1 (-(H + ΔH)))
                ≤ gibbsMinimum 1 (partitionFunction 1 (-H))
                    - ComplexDensityMatrix.expectation ρH ΔH := by
    have : freeEnergy ρH (-(H + ΔH)) 1
            = freeEnergy ρH (-H) 1 - ComplexDensityMatrix.expectation ρH ΔH := by
      linarith [hdiff]
    rw [this, hS] at hV'
    exact hV'
  -- Translate gibbsMinimum 1 Z = -log Z and the sign-flip bridge.
  have hbridgeH : partitionFunction 1 (-H) = partitionFunction (-1) H :=
    (partitionFunction_neg_one_eq H hH).symm
  have hbridgeHΔH : partitionFunction 1 (-(H + ΔH)) = partitionFunction (-1) (H + ΔH) :=
    (partitionFunction_neg_one_eq (H + ΔH) hHΔH).symm
  unfold PeierlsBogoliubov_Target
  -- hkey:  -log Z(1,-(H+ΔH)) ≤ -log Z(1,-H) - ⟨ΔH⟩.
  unfold gibbsMinimum at hkey
  rw [hbridgeH, hbridgeHΔH] at hkey
  -- hkey now: -1 * log Z(-1,H+ΔH) ≤ -1 * log Z(-1,H) - ⟨ΔH⟩.
  -- ρH is definitionally the state in the target's expectation argument.
  have hρH_eq : ρH = gibbsDensity 1 (-H) hH.neg
      (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
        1 (-H) hH.neg) := rfl
  rw [hρH_eq] at hkey
  linarith [hkey]

/-! ## 3.  Axiom audit. -/

#print axioms partitionFunction_neg_one_eq
#print axioms peierls_bogoliubov

end UnifiedTheory.LayerB.PeierlsBogoliubov
