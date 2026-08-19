/-
  Audit/KFCausalCSpecArakiHorizonRelativeEntropy.lean
  -- Dorau--Much relative-entropy route to the semiclassical Einstein equations

  CITATION.
    Philipp Dorau and Albert Much,
    "From Quantum Relative Entropy to the Semiclassical Einstein Equations,"
    arXiv:2510.24491v3 [hep-th], 3 Mar 2026.
    Journal reference: Phys. Rev. Lett. 136, 091602 (2026).
    DOI: 10.1103/lmq8-nsty.  arXiv DOI: 10.48550/arXiv.2510.24491.

  WHAT THIS FILE FORMALIZES.

  Dorau--Much replace Jacobson's thermodynamic entropy input by the
  Araki--Uhlmann relative entropy of a coherent scalar-field excitation
  restricted to a local bifurcate Killing/Rindler horizon.  The analytic
  AQFT theorem is represented here as explicit target propositions over an
  abstract horizon model:

    * `HorizonArakiRelativeEntropyFlux_Target`:
        S_rel = -2*pi * (weighted null-energy flux).

    * `RelativeEntropyAreaVariation_Target`:
        delta A = alpha/(2*pi) * S_rel.

    * `RaychaudhuriAreaVariation_Target`:
        delta A = - (weighted Ricci flux).

  From these inputs, the scalar algebra is fully proved:

    1.  the Dorau--Much area law is
          delta A = - alpha * (weighted null-energy flux);

    2.  matching it with Raychaudhuri gives the null-null balance
          Ricci_null = alpha * T_null;

    3.  the Bekenstein--Hawking identification S_rel = delta A / 4
        fixes alpha = 8*pi for nonzero relative entropy;

    4.  on null vectors, the trace term in the Einstein tensor drops, so the
        Dorau--Much null Ricci balance supplies exactly the `hequil` input of
        `KFCausalCSpecEinsteinEquations.einstein_equation`.

  HONEST SCOPE.
    The full modular-theoretic AQFT calculation, Type III local algebra,
    KMS horizon restriction, coherent-state limitation, and higher-curvature
    corrections remain target propositions, not hidden axioms.  The Lean
    proofs below certify the constants, sign conventions, null trace-drop,
    and connection to the repository's existing Einstein-equation theorem.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecEinsteinEquations

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecArakiHorizonRelativeEntropy

open UnifiedTheory.Audit.KFCausalCSpecEinsteinEquations

/-! ## 1. Scalar horizon bookkeeping -/

/-- Dorau--Much weighted horizon flux convention:
`S_rel = -2*pi*W`, where `W` abbreviates the weighted null-energy integral
appearing in the paper. -/
noncomputable def arakiRelativeEntropyFromWeightedFlux (W : ℝ) : ℝ :=
  -(2 * Real.pi) * W

/-- Dorau--Much area variation after introducing the gravitational coupling
constant `alpha`: `delta A = -alpha*W`. -/
def dorauMuchAreaFromWeightedFlux (alpha W : ℝ) : ℝ :=
  -alpha * W

/-- The same area variation written in relative-entropy form:
`delta A = alpha/(2*pi) * S_rel`. -/
noncomputable def relativeEntropyAreaVariation (alpha Srel : ℝ) : ℝ :=
  alpha / (2 * Real.pi) * Srel

/-- Raychaudhuri focusing convention:
`delta A = -R`, where `R` abbreviates the weighted Ricci-null flux. -/
def raychaudhuriAreaFromRicci (R : ℝ) : ℝ :=
  -R

/-- Bekenstein--Hawking identification in Dorau--Much's convention:
`S_rel = delta A / 4`, equivalently `delta A = 4*S_rel`. -/
def bekensteinHawkingAreaVariation (Srel : ℝ) : ℝ :=
  4 * Srel

/-- The flux and relative-entropy versions of the Dorau--Much area law agree. -/
theorem relativeEntropyArea_eq_fluxArea (alpha W : ℝ) :
    relativeEntropyAreaVariation alpha (arakiRelativeEntropyFromWeightedFlux W)
      = dorauMuchAreaFromWeightedFlux alpha W := by
  unfold relativeEntropyAreaVariation arakiRelativeEntropyFromWeightedFlux
    dorauMuchAreaFromWeightedFlux
  have h2π : (2 * Real.pi) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  field_simp [h2π]

/-- With no weighted null-energy flux, the Araki relative entropy vanishes. -/
theorem arakiRelativeEntropy_zero_of_flux_zero {W : ℝ} (hW : W = 0) :
    arakiRelativeEntropyFromWeightedFlux W = 0 := by
  simp [arakiRelativeEntropyFromWeightedFlux, hW]

/-- The Bekenstein--Hawking identification fixes `alpha = 8*pi` for a nonzero
relative entropy excitation. -/
theorem alpha_eq_eight_pi_of_bh_area_law
    (alpha Srel deltaA : ℝ)
    (hS : Srel ≠ 0)
    (hDM : deltaA = relativeEntropyAreaVariation alpha Srel)
    (hBH : deltaA = bekensteinHawkingAreaVariation Srel) :
    alpha = 8 * Real.pi := by
  have h2π : (2 * Real.pi) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have hcoef : alpha / (2 * Real.pi) = 4 := by
    have h := hBH
    rw [hDM] at h
    simpa [relativeEntropyAreaVariation, bekensteinHawkingAreaVariation] using
      (mul_right_cancel₀ hS h)
  rw [div_eq_iff h2π] at hcoef
  calc
    alpha = 4 * (2 * Real.pi) := hcoef
    _ = 8 * Real.pi := by ring

/-- Matching Dorau--Much area variation with Raychaudhuri focusing gives the
weighted null-null field equation `R = alpha*W`. -/
theorem ricciFlux_eq_alpha_stressFlux_of_area_matching
    (alpha W R : ℝ)
    (hmatch :
      dorauMuchAreaFromWeightedFlux alpha W = raychaudhuriAreaFromRicci R) :
    R = alpha * W := by
  unfold dorauMuchAreaFromWeightedFlux raychaudhuriAreaFromRicci at hmatch
  linarith

/-! ## 2. AQFT target interface for the Dorau--Much theorem -/

/-- Abstract data carried by a local bifurcate Killing/Rindler horizon.

`Excitation` should be read as the coherent scalar-field excitations used in
Dorau--Much.  The full AQFT construction of this type and these functionals is
deliberately not attempted here. -/
structure HorizonAQFTModel where
  Excitation : Type
  Srel : Excitation → ℝ
  weightedNullEnergy : Excitation → ℝ
  areaVariation : Excitation → ℝ
  ricciWeightedFlux : Excitation → ℝ

/-- Target: the modular-theoretic Araki--Uhlmann relative-entropy computation
on the horizon, specialized to coherent scalar-field excitations. -/
def HorizonArakiRelativeEntropyFlux_Target (H : HorizonAQFTModel) : Prop :=
  ∀ phi : H.Excitation,
    H.Srel phi =
      arakiRelativeEntropyFromWeightedFlux (H.weightedNullEnergy phi)

/-- Target: the relative-entropy/area identification used by Dorau--Much. -/
noncomputable def RelativeEntropyAreaVariation_Target
    (H : HorizonAQFTModel) (alpha : ℝ) : Prop :=
  ∀ phi : H.Excitation,
    H.areaVariation phi =
      relativeEntropyAreaVariation alpha (H.Srel phi)

/-- Target: Raychaudhuri focusing expressed as area variation of the local
horizon cross section. -/
def RaychaudhuriAreaVariation_Target (H : HorizonAQFTModel) : Prop :=
  ∀ phi : H.Excitation,
    H.areaVariation phi =
      raychaudhuriAreaFromRicci (H.ricciWeightedFlux phi)

/-- Target: Bekenstein--Hawking entropy-area normalization in the convention
`S_rel = delta A/4`. -/
def BekensteinHawkingEntropyArea_Target (H : HorizonAQFTModel) : Prop :=
  ∀ phi : H.Excitation,
    H.areaVariation phi =
      bekensteinHawkingAreaVariation (H.Srel phi)

/-- Araki flux + relative-entropy/area identification imply the Dorau--Much
flux-area law for every coherent excitation in the abstract horizon model. -/
theorem areaVariation_eq_dorauMuchFluxArea
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (phi : H.Excitation) :
    H.areaVariation phi =
      dorauMuchAreaFromWeightedFlux alpha (H.weightedNullEnergy phi) := by
  rw [hArea phi, hFlux phi, relativeEntropyArea_eq_fluxArea]

/-- Dorau--Much + Raychaudhuri gives the weighted null-null balance. -/
theorem raychaudhuri_relativeEntropy_flux_balance
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (hRay : RaychaudhuriAreaVariation_Target H) :
    ∀ phi : H.Excitation,
      H.ricciWeightedFlux phi = alpha * H.weightedNullEnergy phi := by
  intro phi
  have h1 := areaVariation_eq_dorauMuchFluxArea hFlux hArea phi
  have h2 := hRay phi
  exact ricciFlux_eq_alpha_stressFlux_of_area_matching
    alpha (H.weightedNullEnergy phi) (H.ricciWeightedFlux phi)
    (h1.symm.trans h2)

/-- In the nonzero-excitation sector, the Bekenstein--Hawking normalization
fixes the Dorau--Much coupling to `8*pi`. -/
theorem bekensteinHawking_fixes_dorauMuch_coupling
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (hBH : BekensteinHawkingEntropyArea_Target H)
    {phi : H.Excitation} (hS : H.Srel phi ≠ 0) :
    alpha = 8 * Real.pi :=
  alpha_eq_eight_pi_of_bh_area_law
    alpha (H.Srel phi) (H.areaVariation phi) hS (hArea phi) (hBH phi)

/-- Combining Araki relative entropy, the Dorau--Much area law,
Raychaudhuri focusing, and Bekenstein--Hawking normalization gives the fixed
`8*pi` weighted null-null balance for every nonzero excitation. -/
theorem bekensteinHawking_raychaudhuri_flux_balance_eight_pi
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (hRay : RaychaudhuriAreaVariation_Target H)
    (hBH : BekensteinHawkingEntropyArea_Target H)
    {phi : H.Excitation} (hS : H.Srel phi ≠ 0) :
    H.ricciWeightedFlux phi =
      (8 * Real.pi) * H.weightedNullEnergy phi := by
  have hBalance :=
    raychaudhuri_relativeEntropy_flux_balance
      (H := H) (alpha := alpha) hFlux hArea hRay phi
  have hAlpha :=
    bekensteinHawking_fixes_dorauMuch_coupling
      (H := H) (alpha := alpha) hArea hBH hS
  rw [hAlpha] at hBalance
  exact hBalance

/-- The zero-excitation check: zero weighted null energy gives zero relative
entropy and zero area variation. -/
theorem zero_excitation_has_zero_entropy_and_area
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    {phi : H.Excitation} (hW : H.weightedNullEnergy phi = 0) :
    H.Srel phi = 0 ∧ H.areaVariation phi = 0 := by
  have hS : H.Srel phi = 0 := by
    rw [hFlux phi]
    exact arakiRelativeEntropy_zero_of_flux_zero hW
  constructor
  · exact hS
  · rw [hArea phi, hS]
    simp [relativeEntropyAreaVariation]

/-! ## 3. Interface to the repository's Einstein-equation theorem -/

/-- The Minkowski metric matrix used by the existing Einstein-equation module
is symmetric. -/
theorem eta_symm : ∀ i j : Fin 4, eta i j = eta j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [eta]

/-- On a null vector, any pure metric trace term has zero quadratic form. -/
theorem null_trace_term_drops (c : ℝ) {v : Fin 4 → ℝ}
    (hv : quad eta v = 0) :
    quad (c • eta) v = 0 := by
  rw [quad_smul, hv, mul_zero]

/-- Therefore the null contraction of `Ricci - (R/2) eta` equals the null
contraction of `Ricci`.  This is the precise bridge from Dorau--Much's
`R_ab k^a k^b = 8*pi <T_ab> k^a k^b` to the existing Einstein-tensor
null-equilibrium input. -/
theorem einsteinTensor_null_eq_ricciNull
    (Ricci : Matrix (Fin 4) (Fin 4) ℝ) (Rscalar : ℝ)
    {v : Fin 4 → ℝ} (hv : quad eta v = 0) :
    quad (Ricci - (Rscalar / 2) • eta) v = quad Ricci v := by
  rw [quad_sub, quad_smul, hv, mul_zero, sub_zero]

/-- Pointwise Dorau--Much null Ricci balance supplies the `hequil` hypothesis
of `KFCausalCSpecEinsteinEquations.einstein_equation`. -/
theorem ricci_null_balance_supplies_hequil
    (kappa : ℝ)
    (Ricci T : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (Rscalar : ℝ → ℝ)
    (hRicciNull : ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
      quad (Ricci x) v = kappa * quad (T x) v) :
    ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
      quad (Ricci x - (Rscalar x / 2) • eta) v =
        kappa * quad (T x) v := by
  intro x v hv
  rw [einsteinTensor_null_eq_ricciNull (Ricci x) (Rscalar x) hv]
  exact hRicciNull x v hv

/-- The Dorau--Much route, plugged into the repository's existing
Einstein-equation theorem.

The theorem's non-algebraic input is exactly the pointwise null Ricci balance
coming from the AQFT + area + Raychaudhuri chain above.  Once supplied, the
existing null-polarization argument yields the semiclassical Einstein equation
with a cosmological integration constant. -/
theorem dorau_much_semiclassical_einstein_equation
    (kappa : ℝ)
    (Ricci T : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (Rscalar : ℝ → ℝ)
    (hRicciSymm : ∀ x i j, Ricci x i j = Ricci x j i)
    (hTsymm : ∀ x i j, T x i j = T x j i)
    (hRicciNull : ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
      quad (Ricci x) v = kappa * quad (T x) v)
    (hdiff : Differentiable ℝ
      (fun x => (Ricci x - (Rscalar x / 2) • eta) 0 0
        - kappa * T x 0 0))
    (hcons : ∀ x, deriv
      (fun y => (Ricci y - (Rscalar y / 2) • eta) 0 0
        - kappa * T y 0 0) x = 0) :
    ∃ Lambda : ℝ, ∀ x,
      (Ricci x - (Rscalar x / 2) • eta) + Lambda • eta =
        kappa • T x := by
  have hGsymm :
      ∀ x i j,
        (Ricci x - (Rscalar x / 2) • eta) i j =
          (Ricci x - (Rscalar x / 2) • eta) j i := by
    intro x i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hRicciSymm x i j, eta_symm i j]
  have hequil :
      ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
        quad (Ricci x - (Rscalar x / 2) • eta) v =
          kappa * quad (T x) v :=
    ricci_null_balance_supplies_hequil kappa Ricci T Rscalar hRicciNull
  exact einstein_equation kappa
    (fun x => Ricci x - (Rscalar x / 2) • eta) T
    hGsymm hTsymm hequil hdiff hcons

#print axioms relativeEntropyArea_eq_fluxArea
#print axioms alpha_eq_eight_pi_of_bh_area_law
#print axioms ricciFlux_eq_alpha_stressFlux_of_area_matching
#print axioms raychaudhuri_relativeEntropy_flux_balance
#print axioms bekensteinHawking_fixes_dorauMuch_coupling
#print axioms bekensteinHawking_raychaudhuri_flux_balance_eight_pi
#print axioms zero_excitation_has_zero_entropy_and_area
#print axioms null_trace_term_drops
#print axioms einsteinTensor_null_eq_ricciNull
#print axioms ricci_null_balance_supplies_hequil
#print axioms dorau_much_semiclassical_einstein_equation

end UnifiedTheory.Audit.KFCausalCSpecArakiHorizonRelativeEntropy
