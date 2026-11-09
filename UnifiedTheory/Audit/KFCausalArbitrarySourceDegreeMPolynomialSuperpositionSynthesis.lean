/- Arbitrary-source degree-`M` neutral polynomial (`C (c₀ i) + ∑ r, C (d r i) * X^(r+1)`)
superposition decomposition across all 9 state, momentum, factor, lift, and strong
Hamiltonian maps for differing complex sources `b : Fin n → ℂ`, common constant
mode scalar factoring, triangle upper bounds, reverse-triangle lower bounds, and
joint synthesis with uniform Hamiltonian response lower bounds. -/
import UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift inputLift_embedding momentumLift_embedding
   fullEnergy fullResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude state_constant_eq momentum_constant_eq
   output_constant_eq momentumOutput_constant_eq)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (seconds_scalar_polynomial_eq hamiltonianOutput_scalar_polynomial_eq
   inputLift_scalar_polynomial_eq momentumLift_scalar_polynomial_eq)
open KFCausalCommonComplexAffineNeutralPolynomialDecomposition
  (state_poly_add state_poly_smul
   momentum_poly_add momentum_poly_smul
   output_poly_add output_poly_smul
   momentumOutput_poly_add momentumOutput_poly_smul
   seconds_poly_add seconds_poly_smul
   hamiltonianOutput_poly_add hamiltonianOutput_poly_smul
   inputLift_poly_add inputLift_poly_smul
   momentumLift_poly_add momentumLift_poly_smul)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
  (unitMonomialPolyProfile
   state_poly_finset_sum momentum_poly_finset_sum
   output_poly_finset_sum momentumOutput_poly_finset_sum
   seconds_poly_finset_sum hamiltonianOutput_poly_finset_sum
   inputLift_poly_finset_sum momentumLift_poly_finset_sum
   state_monomial_eq momentum_monomial_eq
   output_monomial_eq momentumOutput_monomial_eq
   seconds_monomial_eq hamiltonianOutput_monomial_eq
   inputLift_monomial_eq momentumLift_monomial_eq)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (degreeMPolyProfile full_bound_degreeM_neutral)

private lemma const_poly_eq_smul_one {n : ℕ} (z : ℂ) :
    (fun _ : Fin n => Polynomial.C z) =
      fun _ : Fin n => Polynomial.C z * (1 : Polynomial ℂ) := by
  funext _
  simp

private lemma norm_add_finset_sum_le {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E) :
    ‖x + ∑ r : Fin M, f r‖ ≤ ‖x‖ + ∑ r : Fin M, ‖f r‖ := by
  have h1 : ‖x + ∑ r : Fin M, f r‖ ≤ ‖x‖ + ‖∑ r : Fin M, f r‖ :=
    norm_add_le x (∑ r : Fin M, f r)
  have h2 : ‖∑ r : Fin M, f r‖ ≤ ∑ r : Fin M, ‖f r‖ :=
    norm_sum_le Finset.univ f
  linarith

private lemma norm_sub_finset_sum_le_add {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E) :
    ‖x‖ - ∑ r : Fin M, ‖f r‖ ≤ ‖x + ∑ r : Fin M, f r‖ := by
  have h1 : ‖x‖ ≤ ‖x + ∑ r : Fin M, f r‖ + ‖∑ r : Fin M, f r‖ :=
     norm_le_add_norm_add x (∑ r : Fin M, f r)
  have h2 : ‖∑ r : Fin M, f r‖ ≤ ∑ r : Fin M, ‖f r‖ :=
    norm_sum_le Finset.univ f
  linarith

variable (n M : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b c₀ : Fin n → ℂ)
  (d : Fin M → Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### 1. Arbitrary-Source Degree-`M` Polynomial Decomposition Across All 9 Maps -/

theorem state_degreeM_arbitrary_source_eq :
    state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw := by
  unfold degreeMPolyProfile
  rw [state_poly_add, state_constant_eq, state_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    state_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)))

theorem momentum_degreeM_arbitrary_source_eq :
    momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw := by
  unfold degreeMPolyProfile
  rw [momentum_poly_add, momentum_constant_eq, momentum_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    momentum_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)))

theorem output_degreeM_arbitrary_source_eq (j : Fin 8) :
    output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j +
        ∑ r : Fin M,
          output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j := by
  unfold degreeMPolyProfile
  rw [output_poly_add, output_constant_eq, output_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    output_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1) j))

theorem momentumOutput_degreeM_arbitrary_source_eq (j : Fin 8) :
    momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j +
        ∑ r : Fin M,
          momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j := by
  unfold degreeMPolyProfile
  rw [momentumOutput_poly_add, momentumOutput_constant_eq, momentumOutput_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    momentumOutput_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1) j))

theorem seconds_degreeM_arbitrary_source_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j +
        ∑ r : Fin M,
          seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j := by
  unfold degreeMPolyProfile
  rw [seconds_poly_add, seconds_scalar_polynomial_eq, seconds_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    seconds_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1) hb_narrow j))

theorem hamiltonianOutput_degreeM_arbitrary_source_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        ∑ r : Fin M,
          hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold degreeMPolyProfile
  rw [hamiltonianOutput_poly_add, hamiltonianOutput_scalar_polynomial_eq,
    hamiltonianOutput_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    hamiltonianOutput_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)
      hb_narrow mass2 quartic vacuum t))

theorem inputLift_degreeM_arbitrary_source_eq (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        ∑ r : Fin M,
          inputLift n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb mass2 quartic vacuum t := by
  unfold degreeMPolyProfile
  rw [inputLift_poly_add, inputLift_scalar_polynomial_eq, inputLift_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    inputLift_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1)
      mass2 quartic vacuum t))

theorem momentumLift_degreeM_arbitrary_source_eq (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        ∑ r : Fin M,
          momentumLift n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb mass2 quartic vacuum t := by
  unfold degreeMPolyProfile
  rw [momentumLift_poly_add, momentumLift_scalar_polynomial_eq, momentumLift_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    momentumLift_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1)
      mass2 quartic vacuum t))

theorem hamiltonian_degreeM_arbitrary_source_action
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        ∑ r : Fin M, H ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
          hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  exact (hamiltonian_action n ε h a w p C b (degreeMPolyProfile M c₀ d)
    hε ha hh hw hb_narrow mass2 quartic vacuum t).trans
    ((hamiltonianOutput_degreeM_arbitrary_source_eq n M ε h a w p C b c₀ d
      hε ha hh hw hb_narrow mass2 quartic vacuum t).trans
      (congrArg₂ (· + ·)
        (hamiltonian_action n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t).symm
        (Finset.sum_congr rfl (fun r _ =>
          (hamiltonian_action n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t).symm))))

/-! ### 2. Common Constant Scalar Factoring (`c₀ = fun _ => z`) for Arbitrary Sources -/

theorem state_degreeM_common_constant_arbitrary_source_eq (z : ℂ) :
    state n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw =
      z • state n ε h a w p C b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw := by
  unfold degreeMPolyProfile
  rw [state_poly_add, const_poly_eq_smul_one z, state_poly_smul, state_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    state_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)))

theorem momentum_degreeM_common_constant_arbitrary_source_eq (z : ℂ) :
    momentum n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw =
      z • momentum n ε h a w p C b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw := by
  unfold degreeMPolyProfile
  rw [momentum_poly_add, const_poly_eq_smul_one z, momentum_poly_smul, momentum_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    momentum_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)))

theorem output_degreeM_common_constant_arbitrary_source_eq (z : ℂ) (j : Fin 8) :
    output n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb j =
      z • output n ε h a w p C b (fun _ => 1) hε ha hh hw hb j +
        ∑ r : Fin M,
          output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j := by
  unfold degreeMPolyProfile
  rw [output_poly_add, const_poly_eq_smul_one z, output_poly_smul, output_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    output_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1) j))

theorem momentumOutput_degreeM_common_constant_arbitrary_source_eq (z : ℂ) (j : Fin 8) :
    momentumOutput n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb j =
      z • momentumOutput n ε h a w p C b (fun _ => 1) hε ha hh hw hb j +
        ∑ r : Fin M,
          momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j := by
  unfold degreeMPolyProfile
  rw [momentumOutput_poly_add, const_poly_eq_smul_one z, momentumOutput_poly_smul,
    momentumOutput_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    momentumOutput_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1) j))

theorem seconds_degreeM_common_constant_arbitrary_source_eq (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb_narrow j =
      z • seconds n ε h a w p C b (fun _ => 1) hε ha hh hw hb_narrow j +
        ∑ r : Fin M,
          seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j := by
  unfold degreeMPolyProfile
  rw [seconds_poly_add, const_poly_eq_smul_one z, seconds_poly_smul, seconds_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    seconds_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1) hb_narrow j))

theorem hamiltonianOutput_degreeM_common_constant_arbitrary_source_eq (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      z • hamiltonianOutput n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        ∑ r : Fin M,
          hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold degreeMPolyProfile
  rw [hamiltonianOutput_poly_add, const_poly_eq_smul_one z, hamiltonianOutput_poly_smul,
    hamiltonianOutput_poly_finset_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun r _ =>
    hamiltonianOutput_monomial_eq n ε h a w p C b (d r) hε ha hh hw ((r : ℕ) + 1)
      hb_narrow mass2 quartic vacuum t))

theorem inputLift_degreeM_common_constant_arbitrary_source_eq (z : ℂ)
    (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb mass2 quartic vacuum t =
      z • inputLift n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        ∑ r : Fin M,
          inputLift n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb mass2 quartic vacuum t := by
  have hconst :
      inputLift n ε h a w p C b (fun _ => Polynomial.C z)
          hε ha hh hw hb mass2 quartic vacuum t =
        z • inputLift n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t := by
    rw [const_poly_eq_smul_one z]
    exact inputLift_poly_smul n ε h a w p C b (fun _ => 1) hε ha hh hw hb z mass2 quartic vacuum t
  exact (inputLift_poly_add n ε h a w p C b (fun _ => Polynomial.C z)
    (fun i => ∑ r : Fin M, Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
    hε ha hh hw hb mass2 quartic vacuum t).trans
    (congrArg₂ (· + ·) hconst
      ((inputLift_poly_finset_sum n ε h a w p C b hε ha hh hw hb Finset.univ
        (fun r i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
        mass2 quartic vacuum t).trans
        (Finset.sum_congr rfl (fun r _ =>
          inputLift_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1)
            mass2 quartic vacuum t))))

theorem momentumLift_degreeM_common_constant_arbitrary_source_eq (z : ℂ)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb mass2 quartic vacuum t =
      z • momentumLift n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        ∑ r : Fin M,
          momentumLift n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb mass2 quartic vacuum t := by
  have hconst :
      momentumLift n ε h a w p C b (fun _ => Polynomial.C z)
          hε ha hh hw hb mass2 quartic vacuum t =
        z • momentumLift n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t := by
    rw [const_poly_eq_smul_one z]
    exact momentumLift_poly_smul n ε h a w p C b (fun _ => 1)
      hε ha hh hw hb z mass2 quartic vacuum t
  exact (momentumLift_poly_add n ε h a w p C b (fun _ => Polynomial.C z)
    (fun i => ∑ r : Fin M, Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
    hε ha hh hw hb mass2 quartic vacuum t).trans
    (congrArg₂ (· + ·) hconst
      ((momentumLift_poly_finset_sum n ε h a w p C b hε ha hh hw hb Finset.univ
        (fun r i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
        mass2 quartic vacuum t).trans
        (Finset.sum_congr rfl (fun r _ =>
          momentumLift_monomial_eq n ε h a w p C b (d r) hε ha hh hw hb ((r : ℕ) + 1)
            mass2 quartic vacuum t))))

theorem hamiltonian_degreeM_common_constant_arbitrary_source_action (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw;
    let ψ₁ := state n ε h a w p C b (fun _ => 1) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      z • H ⟨ψ₁, hamiltonian_domain n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        ∑ r : Fin M, H ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
          hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  exact (hamiltonian_action n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
    hε ha hh hw hb_narrow mass2 quartic vacuum t).trans
    ((hamiltonianOutput_degreeM_common_constant_arbitrary_source_eq n M ε h a w p C b d
      hε ha hh hw z hb_narrow mass2 quartic vacuum t).trans
      (congrArg₂ (· + ·)
        (congrArg (z • ·) (hamiltonian_action n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t).symm)
        (Finset.sum_congr rfl (fun r _ =>
          (hamiltonian_action n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t).symm))))

/-! ### 3. Arbitrary-Source Degree-`M` Norm Triangle Upper Bounds Across All 7 Normed Maps -/

theorem state_degreeM_arbitrary_source_norm_le :
    ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ≤
      ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ +
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ := by
  rw [state_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem momentum_degreeM_arbitrary_source_norm_le :
    ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ +
        ∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem output_degreeM_arbitrary_source_norm_le (j : Fin 8) :
    ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ +
        ∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ := by
  rw [output_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem momentumOutput_degreeM_arbitrary_source_norm_le (j : Fin 8) :
    ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ +
        ∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem seconds_degreeM_arbitrary_source_norm_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ +
        ∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem hamiltonianOutput_degreeM_arbitrary_source_norm_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ +
        ∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact norm_add_finset_sum_le _ _

theorem hamiltonian_degreeM_arbitrary_source_action_norm_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw;
    ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      ‖H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ +
        ∑ r : Fin M, ‖H ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
          hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ := by
  dsimp only
  rw [hamiltonian_degreeM_arbitrary_source_action n M ε h a w p C b c₀ d
    hε ha hh hw hb_narrow mass2 quartic vacuum t]
  exact norm_add_finset_sum_le _ _

/-! ### 4. Arbitrary-Source Degree-`M` Reverse-Triangle Norm Lower Bounds Across All 7 Maps -/

theorem state_degreeM_arbitrary_source_norm_ge :
    ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [state_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem momentum_degreeM_arbitrary_source_norm_ge :
    ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem output_degreeM_arbitrary_source_norm_ge (j : Fin 8) :
    ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [output_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem momentumOutput_degreeM_arbitrary_source_norm_ge (j : Fin 8) :
    ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem seconds_degreeM_arbitrary_source_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ -
        ∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem hamiltonianOutput_degreeM_arbitrary_source_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ -
        ∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact norm_sub_finset_sum_le_add _ _

theorem hamiltonian_degreeM_arbitrary_source_action_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw;
    ‖H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ -
        ∑ r : Fin M, ‖H ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
          hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ := by
  dsimp only
  rw [hamiltonian_degreeM_arbitrary_source_action n M ε h a w p C b c₀ d
    hε ha hh hw hb_narrow mass2 quartic vacuum t]
  exact norm_sub_finset_sum_le_add _ _

/-! ### 5. Degree-`0` Base Reduction and Master Arbitrary-Source Degree-`M` Synthesis -/

theorem degreeMPolyProfile_zero_eq_constant (d0 : Fin 0 → Fin n → ℂ) :
    degreeMPolyProfile 0 c₀ d0 = fun i => Polynomial.C (c₀ i) := by
  funext i
  simp [degreeMPolyProfile]

theorem state_degreeM_zero_arbitrary_source_eq (d0 : Fin 0 → Fin n → ℂ) :
    state n ε h a w p C b (degreeMPolyProfile 0 c₀ d0) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw := by
  rw [state_degreeM_arbitrary_source_eq]
  simp

theorem momentum_degreeM_zero_arbitrary_source_eq (d0 : Fin 0 → Fin n → ℂ) :
    momentum n ε h a w p C b (degreeMPolyProfile 0 c₀ d0) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw := by
  rw [momentum_degreeM_arbitrary_source_eq]
  simp

theorem hamiltonianOutput_degreeM_zero_arbitrary_source_eq (d0 : Fin 0 → Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (degreeMPolyProfile 0 c₀ d0)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
        hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  simp

theorem arbitrary_source_degreeM_superposition_master_synthesis
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    (state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw) ∧
    (momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw +
        ∑ r : Fin M,
          momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw) ∧
    (hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        ∑ r : Fin M,
          hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t) ∧
    (‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (m2 q4 v0 : ℝ),
      0 ≤ m2 → 0 ≤ q4 → 0 ≤ v0 →
      ∀ (n' M' : ℕ) (ε' h' a₀' w₀' p₀' : ℝ) (b₀' : ℂ) (C' c₀' : Fin n' → ℂ)
      (d' : Fin M' → Fin n' → ℂ)
      (hε' : 0 < ε') (ha₀' : 0 < a₀') (hh' : h' ≠ 0) (hw₀' : 1 ≤ w₀')
      (hb' : |h'| ≤ 2 * Real.pi * ε' / 3)
      (_hneutral : ∀ r : Fin M', ∑ i : Fin n', C' i * d' r i = 0) (t' : ℝ),
      -(K / ε') * fullEnergy n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t' ≤
      fullResponse n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t') :=
  ⟨state_degreeM_arbitrary_source_eq n M ε h a w p C b c₀ d hε ha hh hw,
   momentum_degreeM_arbitrary_source_eq n M ε h a w p C b c₀ d hε ha hh hw,
   hamiltonianOutput_degreeM_arbitrary_source_eq n M ε h a w p C b c₀ d
     hε ha hh hw hb_narrow mass2 quartic vacuum t,
   state_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw,
   full_bound_degreeM_neutral⟩

#print axioms state_degreeM_arbitrary_source_eq
#print axioms momentum_degreeM_arbitrary_source_eq
#print axioms output_degreeM_arbitrary_source_eq
#print axioms momentumOutput_degreeM_arbitrary_source_eq
#print axioms seconds_degreeM_arbitrary_source_eq
#print axioms hamiltonianOutput_degreeM_arbitrary_source_eq
#print axioms inputLift_degreeM_arbitrary_source_eq
#print axioms momentumLift_degreeM_arbitrary_source_eq
#print axioms hamiltonian_degreeM_arbitrary_source_action
#print axioms state_degreeM_common_constant_arbitrary_source_eq
#print axioms momentum_degreeM_common_constant_arbitrary_source_eq
#print axioms output_degreeM_common_constant_arbitrary_source_eq
#print axioms momentumOutput_degreeM_common_constant_arbitrary_source_eq
#print axioms seconds_degreeM_common_constant_arbitrary_source_eq
#print axioms hamiltonianOutput_degreeM_common_constant_arbitrary_source_eq
#print axioms inputLift_degreeM_common_constant_arbitrary_source_eq
#print axioms momentumLift_degreeM_common_constant_arbitrary_source_eq
#print axioms hamiltonian_degreeM_common_constant_arbitrary_source_action
#print axioms state_degreeM_arbitrary_source_norm_le
#print axioms momentum_degreeM_arbitrary_source_norm_le
#print axioms output_degreeM_arbitrary_source_norm_le
#print axioms momentumOutput_degreeM_arbitrary_source_norm_le
#print axioms seconds_degreeM_arbitrary_source_norm_le
#print axioms hamiltonianOutput_degreeM_arbitrary_source_norm_le
#print axioms hamiltonian_degreeM_arbitrary_source_action_norm_le
#print axioms state_degreeM_arbitrary_source_norm_ge
#print axioms momentum_degreeM_arbitrary_source_norm_ge
#print axioms output_degreeM_arbitrary_source_norm_ge
#print axioms momentumOutput_degreeM_arbitrary_source_norm_ge
#print axioms seconds_degreeM_arbitrary_source_norm_ge
#print axioms hamiltonianOutput_degreeM_arbitrary_source_norm_ge
#print axioms hamiltonian_degreeM_arbitrary_source_action_norm_ge
#print axioms degreeMPolyProfile_zero_eq_constant
#print axioms state_degreeM_zero_arbitrary_source_eq
#print axioms momentum_degreeM_zero_arbitrary_source_eq
#print axioms hamiltonianOutput_degreeM_zero_arbitrary_source_eq
#print axioms arbitrary_source_degreeM_superposition_master_synthesis
end
end UnifiedTheory.Audit.KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis
