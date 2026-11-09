/- Finite-sum superposition linearity in the neutral polynomial profile,
degree-`r` monomial amplitude absorption, 3-term quadratic polynomial
decomposition, and general `M`-term degree-`M` monomial basis decomposition
across all 9 state, momentum, factor, lift, and strong Hamiltonian maps for
arbitrary differing complex sources `b : Fin n → ℂ`. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition
import UnifiedTheory.Audit.KFCausalCommonComplexLinearMonomialAmplitudeAbsorption

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude state_constant_eq momentum_constant_eq
   output_constant_eq momentumOutput_constant_eq)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (seconds_scalar_polynomial_eq hamiltonianOutput_scalar_polynomial_eq)
open KFCausalCommonComplexAffineNeutralPolynomialDecomposition
  (state_poly_add state_poly_scale
   momentum_poly_add momentum_poly_scale
   output_poly_add output_poly_scale
   momentumOutput_poly_add momentumOutput_poly_scale
   seconds_poly_add seconds_poly_scale
   hamiltonianOutput_poly_add hamiltonianOutput_poly_scale
   inputLift_poly_add inputLift_poly_scale
   momentumLift_poly_add momentumLift_poly_scale
   affinePolynomial inputLift_affine_poly_eq momentumLift_affine_poly_eq)
open KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition
  (state_poly_zero momentum_poly_zero output_poly_zero momentumOutput_poly_zero
   seconds_poly_zero hamiltonianOutput_poly_zero inputLift_poly_zero momentumLift_poly_zero)

private theorem finset_sum_poly_map {ι E : Type*} {n : ℕ} [AddCommMonoid E]
    (F : (Fin n → Polynomial ℂ) → E)
    (h0 : F (fun _ => 0) = 0)
    (hadd : ∀ P₁ P₂ : Fin n → Polynomial ℂ, F (fun i => P₁ i + P₂ i) = F P₁ + F P₂)
    (S : Finset ι) (P : ι → Fin n → Polynomial ℂ) :
    F (fun i => ∑ r ∈ S, P r i) = ∑ r ∈ S, F (P r) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using h0
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hadd, ih]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d d₀ d₁ d₂ : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### 1. Finite-Sum (`Finset.sum`) Polynomial Superposition Linearity Across All 9 Maps -/

theorem state_poly_finset_sum {ι : Type*} (S : Finset ι) (P : ι → Fin n → Polynomial ℂ) :
    state n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw =
      ∑ r ∈ S, state n ε h a w p C b (P r) hε ha hh hw :=
  finset_sum_poly_map (fun Q => state n ε h a w p C b Q hε ha hh hw)
    (state_poly_zero n ε h a w p C b hε ha hh hw)
    (fun P₁ P₂ => state_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw) S P

theorem momentum_poly_finset_sum {ι : Type*} (S : Finset ι) (P : ι → Fin n → Polynomial ℂ) :
    momentum n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw =
      ∑ r ∈ S, momentum n ε h a w p C b (P r) hε ha hh hw :=
  finset_sum_poly_map (fun Q => momentum n ε h a w p C b Q hε ha hh hw)
    (momentum_poly_zero n ε h a w p C b hε ha hh hw)
    (fun P₁ P₂ => momentum_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw) S P

theorem output_poly_finset_sum {ι : Type*} (S : Finset ι) (P : ι → Fin n → Polynomial ℂ)
    (j : Fin 8) :
    output n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw hb j =
      ∑ r ∈ S, output n ε h a w p C b (P r) hε ha hh hw hb j :=
  finset_sum_poly_map (fun Q => output n ε h a w p C b Q hε ha hh hw hb j)
    (output_poly_zero n ε h a w p C b hε ha hh hw hb j)
    (fun P₁ P₂ => output_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw hb j) S P

theorem momentumOutput_poly_finset_sum {ι : Type*} (S : Finset ι) (P : ι → Fin n → Polynomial ℂ)
    (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw hb j =
      ∑ r ∈ S, momentumOutput n ε h a w p C b (P r) hε ha hh hw hb j :=
  finset_sum_poly_map (fun Q => momentumOutput n ε h a w p C b Q hε ha hh hw hb j)
    (momentumOutput_poly_zero n ε h a w p C b hε ha hh hw hb j)
    (fun P₁ P₂ => momentumOutput_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw hb j) S P

theorem seconds_poly_finset_sum {ι : Type*} (S : Finset ι) (P : ι → Fin n → Polynomial ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw hb_narrow j =
      ∑ r ∈ S, seconds n ε h a w p C b (P r) hε ha hh hw hb_narrow j :=
  finset_sum_poly_map (fun Q => seconds n ε h a w p C b Q hε ha hh hw hb_narrow j)
    (seconds_poly_zero n ε h a w p C b hε ha hh hw hb_narrow j)
    (fun P₁ P₂ => seconds_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw hb_narrow j) S P

theorem hamiltonianOutput_poly_finset_sum {ι : Type*} (S : Finset ι)
    (P : ι → Fin n → Polynomial ℂ) (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => ∑ r ∈ S, P r i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      ∑ r ∈ S, hamiltonianOutput n ε h a w p C b (P r)
        hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  finset_sum_poly_map
    (fun Q => hamiltonianOutput n ε h a w p C b Q hε ha hh hw hb_narrow mass2 quartic vacuum t)
    (hamiltonianOutput_poly_zero n ε h a w p C b hε ha hh hw hb_narrow mass2 quartic vacuum t)
    (fun P₁ P₂ => hamiltonianOutput_poly_add n ε h a w p C b P₁ P₂
      hε ha hh hw hb_narrow mass2 quartic vacuum t) S P

theorem inputLift_poly_finset_sum {ι : Type*} (S : Finset ι)
    (P : ι → Fin n → Polynomial ℂ) (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => ∑ r ∈ S, P r i)
        hε ha hh hw hb mass2 quartic vacuum t =
      ∑ r ∈ S, inputLift n ε h a w p C b (P r)
        hε ha hh hw hb mass2 quartic vacuum t :=
  finset_sum_poly_map
    (fun Q => inputLift n ε h a w p C b Q hε ha hh hw hb mass2 quartic vacuum t)
    (inputLift_poly_zero n ε h a w p C b hε ha hh hw hb mass2 quartic vacuum t)
    (fun P₁ P₂ => inputLift_poly_add n ε h a w p C b P₁ P₂
      hε ha hh hw hb mass2 quartic vacuum t) S P

theorem momentumLift_poly_finset_sum {ι : Type*} (S : Finset ι)
    (P : ι → Fin n → Polynomial ℂ) (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => ∑ r ∈ S, P r i)
        hε ha hh hw hb mass2 quartic vacuum t =
      ∑ r ∈ S, momentumLift n ε h a w p C b (P r)
        hε ha hh hw hb mass2 quartic vacuum t :=
  finset_sum_poly_map
    (fun Q => momentumLift n ε h a w p C b Q hε ha hh hw hb mass2 quartic vacuum t)
    (momentumLift_poly_zero n ε h a w p C b hε ha hh hw hb mass2 quartic vacuum t)
    (fun P₁ P₂ => momentumLift_poly_add n ε h a w p C b P₁ P₂
      hε ha hh hw hb mass2 quartic vacuum t) S P

theorem hamiltonian_poly_finset_sum_action {ι : Type*} (S : Finset ι)
    (P : ι → Fin n → Polynomial ℂ) (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (fun i => ∑ r ∈ S, P r i) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (fun i => ∑ r ∈ S, P r i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      ∑ r ∈ S, H ⟨state n ε h a w p C b (P r) hε ha hh hw,
        hamiltonian_domain n ε h a w p C b (P r)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  exact (hamiltonian_action n ε h a w p C b (fun i => ∑ r ∈ S, P r i)
    hε ha hh hw hb_narrow mass2 quartic vacuum t).trans
    ((hamiltonianOutput_poly_finset_sum n ε h a w p C b hε ha hh hw S P
      hb_narrow mass2 quartic vacuum t).trans
      (Finset.sum_congr rfl (fun r _ => (hamiltonian_action n ε h a w p C b (P r)
        hε ha hh hw hb_narrow mass2 quartic vacuum t).symm)))

/-! ### 2. Degree-`r` Monomial Amplitude Absorption Across All 9 Maps -/

abbrev monomialPolyProfile {n : ℕ} (r : ℕ) (c : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  fun i => Polynomial.C (c i) * Polynomial.X ^ r

abbrev unitMonomialPolyProfile (n : ℕ) (r : ℕ) : Fin n → Polynomial ℂ :=
  fun _ => Polynomial.X ^ r

theorem state_monomial_eq (r : ℕ) :
    state n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r) hε ha hh hw :=
  state_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r) hε ha hh hw

theorem momentum_monomial_eq (r : ℕ) :
    momentum n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r) hε ha hh hw :=
  momentum_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r) hε ha hh hw

theorem output_monomial_eq (r : ℕ) (j : Fin 8) :
    output n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r) hε ha hh hw hb j :=
  output_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r) hε ha hh hw hb j

theorem momentumOutput_monomial_eq (r : ℕ) (j : Fin 8) :
    momentumOutput n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d) b
        (unitMonomialPolyProfile n r) hε ha hh hw hb j :=
  momentumOutput_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r) hε ha hh hw hb j

theorem seconds_monomial_eq (r : ℕ) (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d) b
        (unitMonomialPolyProfile n r) hε ha hh hw hb_narrow j :=
  seconds_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r) hε ha hh hw hb_narrow j

theorem hamiltonianOutput_monomial_eq (r : ℕ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  hamiltonianOutput_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r)
    hε ha hh hw hb_narrow mass2 quartic vacuum t

theorem inputLift_monomial_eq (r : ℕ) (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb mass2 quartic vacuum t :=
  inputLift_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r)
    hε ha hh hw hb mass2 quartic vacuum t

theorem momentumLift_monomial_eq (r : ℕ) (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb mass2 quartic vacuum t :=
  momentumLift_poly_scale n ε h a w p C b d (unitMonomialPolyProfile n r)
    hε ha hh hw hb mass2 quartic vacuum t

theorem hamiltonian_monomial_action (r : ℕ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (monomialPolyProfile r d) hε ha hh hw;
    let ψr := state n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψr, hamiltonian_domain n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_monomial_eq n ε h a w p C b d hε ha hh hw r
    hb_narrow mass2 quartic vacuum t

theorem fullEnergy_monomial_eq (r : ℕ) (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb mass2 quartic vacuum t =
      fullEnergy n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    KFCausalReciprocalNeutralHamiltonian.energy_decomposition]
  simp only [output_monomial_eq]

theorem fullResponse_monomial_eq (r : ℕ) (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h a w p C b (monomialPolyProfile r d)
        hε ha hh hw hb mass2 quartic vacuum t =
      fullResponse n ε h a w p (scaleAmplitude C d) b (unitMonomialPolyProfile n r)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.response_decomposition,
    KFCausalReciprocalNeutralHamiltonian.response_decomposition]
  simp only [output_monomial_eq, momentumOutput_monomial_eq]

/-! ### 3. Three-Term Quadratic Neutral Polynomial Decomposition (`1`, `X`, `X^2`) -/

def quadraticPolyProfile {n : ℕ} (d₀ d₁ d₂ : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  Polynomial.C (d₀ i) + Polynomial.C (d₁ i) * Polynomial.X +
    Polynomial.C (d₂ i) * Polynomial.X ^ 2

theorem state_quadratic_poly_eq :
    state n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw +
        state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw +
        state n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2) hε ha hh hw := by
  unfold quadraticPolyProfile
  rw [state_poly_add, state_poly_add, state_constant_eq, state_poly_scale, state_poly_scale]

theorem momentum_quadratic_poly_eq :
    momentum n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw +
        momentum n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw +
        momentum n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2) hε ha hh hw := by
  unfold quadraticPolyProfile
  rw [momentum_poly_add, momentum_poly_add, momentum_constant_eq,
    momentum_poly_scale, momentum_poly_scale]

theorem output_quadratic_poly_eq (j : Fin 8) :
    output n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j +
        output n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j +
        output n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2) hε ha hh hw hb j := by
  unfold quadraticPolyProfile
  rw [output_poly_add, output_poly_add, output_constant_eq, output_poly_scale, output_poly_scale]

theorem momentumOutput_quadratic_poly_eq (j : Fin 8) :
    momentumOutput n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j +
        momentumOutput n ε h a w p (scaleAmplitude C d₁) b
          (fun _ => Polynomial.X) hε ha hh hw hb j +
        momentumOutput n ε h a w p (scaleAmplitude C d₂) b
          (fun _ => Polynomial.X ^ 2) hε ha hh hw hb j := by
  unfold quadraticPolyProfile
  rw [momentumOutput_poly_add, momentumOutput_poly_add, momentumOutput_constant_eq,
    momentumOutput_poly_scale, momentumOutput_poly_scale]

theorem seconds_quadratic_poly_eq (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb_narrow j +
        seconds n ε h a w p (scaleAmplitude C d₁) b
          (fun _ => Polynomial.X) hε ha hh hw hb_narrow j +
        seconds n ε h a w p (scaleAmplitude C d₂) b
          (fun _ => Polynomial.X ^ 2) hε ha hh hw hb_narrow j := by
  unfold quadraticPolyProfile
  rw [seconds_poly_add, seconds_poly_add, seconds_scalar_polynomial_eq,
    seconds_poly_scale, seconds_poly_scale]

theorem hamiltonianOutput_quadratic_poly_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2)
          hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold quadraticPolyProfile
  rw [hamiltonianOutput_poly_add, hamiltonianOutput_poly_add,
    hamiltonianOutput_scalar_polynomial_eq,
    hamiltonianOutput_poly_scale, hamiltonianOutput_poly_scale]

theorem inputLift_quadratic_poly_eq (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂)
        hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        inputLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t +
        inputLift n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2)
          hε ha hh hw hb mass2 quartic vacuum t :=
  (inputLift_poly_add n ε h a w p C b
    (affinePolynomial d₀ d₁) (monomialPolyProfile 2 d₂)
    hε ha hh hw hb mass2 quartic vacuum t).trans
    (congrArg₂ (· + ·)
      (inputLift_affine_poly_eq n ε h a w p C b hε ha hh hw hb d₀ d₁ mass2 quartic vacuum t)
      (inputLift_monomial_eq n ε h a w p C b d₂ hε ha hh hw hb 2 mass2 quartic vacuum t))

theorem momentumLift_quadratic_poly_eq (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂)
        hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        momentumLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t +
        momentumLift n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2)
          hε ha hh hw hb mass2 quartic vacuum t :=
  (momentumLift_poly_add n ε h a w p C b
    (affinePolynomial d₀ d₁) (monomialPolyProfile 2 d₂)
    hε ha hh hw hb mass2 quartic vacuum t).trans
    (congrArg₂ (· + ·)
      (momentumLift_affine_poly_eq n ε h a w p C b hε ha hh hw hb d₀ d₁ mass2 quartic vacuum t)
      (momentumLift_monomial_eq n ε h a w p C b d₂ hε ha hh hw hb 2 mass2 quartic vacuum t))

theorem hamiltonian_quadratic_poly_action
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw;
    let ψ₁ := state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw;
    let ψ₂ := state n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (quadraticPolyProfile d₀ d₁ d₂)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₁, hamiltonian_domain n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₂, hamiltonian_domain n ε h a w p (scaleAmplitude C d₂) b (fun _ => Polynomial.X ^ 2)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action, hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_quadratic_poly_eq n ε h a w p C b d₀ d₁ d₂ hε ha hh hw
    hb_narrow mass2 quartic vacuum t

/-! ### 4. General `M`-Term Degree-`M` Monomial Basis Decomposition Across All 9 Maps -/

def polyBasisProfile (M : ℕ) {n : ℕ} (c : Fin M → Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  ∑ r : Fin M, Polynomial.C (c r i) * Polynomial.X ^ (r : ℕ)

theorem state_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ) :
    state n ε h a w p C b (polyBasisProfile M c) hε ha hh hw =
      ∑ r : Fin M,
        state n ε h a w p (scaleAmplitude C (c r)) b (unitMonomialPolyProfile n (r : ℕ))
          hε ha hh hw := by
  unfold polyBasisProfile
  rw [state_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    state_monomial_eq n ε h a w p C b (c r) hε ha hh hw (r : ℕ))

theorem momentum_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ) :
    momentum n ε h a w p C b (polyBasisProfile M c) hε ha hh hw =
      ∑ r : Fin M,
        momentum n ε h a w p (scaleAmplitude C (c r)) b (unitMonomialPolyProfile n (r : ℕ))
          hε ha hh hw := by
  unfold polyBasisProfile
  rw [momentum_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    momentum_monomial_eq n ε h a w p C b (c r) hε ha hh hw (r : ℕ))

theorem output_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ) (j : Fin 8) :
    output n ε h a w p C b (polyBasisProfile M c) hε ha hh hw hb j =
      ∑ r : Fin M,
        output n ε h a w p (scaleAmplitude C (c r)) b (unitMonomialPolyProfile n (r : ℕ))
          hε ha hh hw hb j := by
  unfold polyBasisProfile
  rw [output_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    output_monomial_eq n ε h a w p C b (c r) hε ha hh hw hb (r : ℕ) j)

theorem momentumOutput_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ) (j : Fin 8) :
    momentumOutput n ε h a w p C b (polyBasisProfile M c) hε ha hh hw hb j =
      ∑ r : Fin M,
        momentumOutput n ε h a w p (scaleAmplitude C (c r)) b (unitMonomialPolyProfile n (r : ℕ))
          hε ha hh hw hb j := by
  unfold polyBasisProfile
  rw [momentumOutput_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    momentumOutput_monomial_eq n ε h a w p C b (c r) hε ha hh hw hb (r : ℕ) j)

theorem seconds_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (polyBasisProfile M c) hε ha hh hw hb_narrow j =
      ∑ r : Fin M,
        seconds n ε h a w p (scaleAmplitude C (c r)) b (unitMonomialPolyProfile n (r : ℕ))
          hε ha hh hw hb_narrow j := by
  unfold polyBasisProfile
  rw [seconds_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    seconds_monomial_eq n ε h a w p C b (c r) hε ha hh hw (r : ℕ) hb_narrow j)

theorem hamiltonianOutput_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (polyBasisProfile M c)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      ∑ r : Fin M,
        hamiltonianOutput n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold polyBasisProfile
  rw [hamiltonianOutput_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    hamiltonianOutput_monomial_eq n ε h a w p C b (c r) hε ha hh hw (r : ℕ)
      hb_narrow mass2 quartic vacuum t)

theorem inputLift_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ)
    (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (polyBasisProfile M c)
        hε ha hh hw hb mass2 quartic vacuum t =
      ∑ r : Fin M,
        inputLift n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw hb mass2 quartic vacuum t := by
  unfold polyBasisProfile
  rw [inputLift_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    inputLift_monomial_eq n ε h a w p C b (c r) hε ha hh hw hb (r : ℕ) mass2 quartic vacuum t)

theorem momentumLift_polyBasis_eq (M : ℕ) (c : Fin M → Fin n → ℂ)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (polyBasisProfile M c)
        hε ha hh hw hb mass2 quartic vacuum t =
      ∑ r : Fin M,
        momentumLift n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw hb mass2 quartic vacuum t := by
  unfold polyBasisProfile
  rw [momentumLift_poly_finset_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    momentumLift_monomial_eq n ε h a w p C b (c r) hε ha hh hw hb (r : ℕ) mass2 quartic vacuum t)

theorem hamiltonian_polyBasis_action (M : ℕ) (c : Fin M → Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (polyBasisProfile M c) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (polyBasisProfile M c)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      ∑ r : Fin M, H ⟨state n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw,
        hamiltonian_domain n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  exact (hamiltonian_action n ε h a w p C b (polyBasisProfile M c)
    hε ha hh hw hb_narrow mass2 quartic vacuum t).trans
    ((hamiltonianOutput_polyBasis_eq n ε h a w p C b hε ha hh hw M c
      hb_narrow mass2 quartic vacuum t).trans
      (Finset.sum_congr rfl (fun r _ =>
        (hamiltonian_action n ε h a w p (scaleAmplitude C (c r)) b
          (unitMonomialPolyProfile n (r : ℕ)) hε ha hh hw hb_narrow mass2 quartic vacuum t).symm)))

#print axioms state_poly_finset_sum
#print axioms momentum_poly_finset_sum
#print axioms output_poly_finset_sum
#print axioms momentumOutput_poly_finset_sum
#print axioms seconds_poly_finset_sum
#print axioms hamiltonianOutput_poly_finset_sum
#print axioms inputLift_poly_finset_sum
#print axioms momentumLift_poly_finset_sum
#print axioms hamiltonian_poly_finset_sum_action
#print axioms state_monomial_eq
#print axioms momentum_monomial_eq
#print axioms output_monomial_eq
#print axioms momentumOutput_monomial_eq
#print axioms seconds_monomial_eq
#print axioms hamiltonianOutput_monomial_eq
#print axioms inputLift_monomial_eq
#print axioms momentumLift_monomial_eq
#print axioms hamiltonian_monomial_action
#print axioms fullEnergy_monomial_eq
#print axioms fullResponse_monomial_eq
#print axioms state_quadratic_poly_eq
#print axioms momentum_quadratic_poly_eq
#print axioms output_quadratic_poly_eq
#print axioms momentumOutput_quadratic_poly_eq
#print axioms seconds_quadratic_poly_eq
#print axioms hamiltonianOutput_quadratic_poly_eq
#print axioms inputLift_quadratic_poly_eq
#print axioms momentumLift_quadratic_poly_eq
#print axioms hamiltonian_quadratic_poly_action
#print axioms state_polyBasis_eq
#print axioms momentum_polyBasis_eq
#print axioms output_polyBasis_eq
#print axioms momentumOutput_polyBasis_eq
#print axioms seconds_polyBasis_eq
#print axioms hamiltonianOutput_polyBasis_eq
#print axioms inputLift_polyBasis_eq
#print axioms momentumLift_polyBasis_eq
#print axioms hamiltonian_polyBasis_action
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
