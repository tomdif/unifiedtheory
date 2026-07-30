/-
  Audit/KFCausalCSpecEinsteinEquations.lean
  — EINSTEIN'S EQUATIONS AS AN EQUATION OF STATE (the geometric spine)

  The Jacobson/unimodular derivation, formalized in its exact algebraic and
  analytic core.  The physical inputs (one hypothesis each, both quantified
  elsewhere in this repository):

  ·  EQUILIBRIUM:  in every local frame, the null-null component of the
     geometric tensor equals κ times that of the matter tensor.  This is
     what entanglement equilibrium / counting stationarity supplies; its
     quantitative content here is the DERIVED small-diamond dictionary
     (RSS conformal expansion, c₁ = −R/180 + R₀₀/30), the BD action mean
     (the −R/2 channel), and the quantitative Hauptvermutung (the metric IS
     counting data).
  ·  CONSERVATION:  the 00-mismatch is differentiable with zero derivative
     along the parameter — Bianchi plus matter conservation, modeled.

  What is then a THEOREM:

  1.  `null_polarization`:  a symmetric matrix whose quadratic form vanishes
      on every η-null vector is a multiple of η.  (The step that turns
      frame-by-frame scalar equilibrium into a tensor equation.)
  2.  `einstein_equation`:  equilibrium in all null directions at every
      parameter point + conservation  ⟹  ∃ Λ,  G(x) + Λ·η = κ·T(x) —
      Einstein's equations, with the cosmological constant arising as an
      INTEGRATION CONSTANT, undetermined by the field equations.

  That freedom is the point of contact with the rest of this repository:
  the fluctuation calculus (action variance, Λ ∝ 1/T law, Károlyházy
  closure, DESI bound) computes the statistics of exactly the quantity this
  derivation leaves free.  Gravity as the equation of state of order and
  number; Λ as its residual fluctuation.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecEinsteinEquations

/-- The Minkowski metric matrix, signature (−,+,+,+). -/
noncomputable def eta : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then (-1:ℝ) else 1)

/-- The quadratic form of a matrix. -/
def quad (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : ℝ :=
  v ⬝ᵥ M.mulVec v

/-- Normal form of the quadratic form. -/
theorem quad_expand (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    quad M v =
      v 0 * (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2 + M 0 3 * v 3)
      + v 1 * (M 1 0 * v 0 + M 1 1 * v 1 + M 1 2 * v 2 + M 1 3 * v 3)
      + v 2 * (M 2 0 * v 0 + M 2 1 * v 1 + M 2 2 * v 2 + M 2 3 * v 3)
      + v 3 * (M 3 0 * v 0 + M 3 1 * v 1 + M 3 2 * v 2 + M 3 3 * v 3) := by
  unfold quad
  first
  | (simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring)
  | simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem quad_eta (v : Fin 4 → ℝ) :
    quad eta v = -(v 0 * v 0) + v 1 * v 1 + v 2 * v 2 + v 3 * v 3 := by
  rw [quad_expand]
  simp only [eta, Matrix.diagonal_apply]
  first
  | (norm_num [Fin.ext_iff]; ring)
  | norm_num [Fin.ext_iff]

theorem quad_sub (A B : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    quad (A - B) v = quad A v - quad B v := by
  rw [quad_expand, quad_expand, quad_expand]
  simp only [Matrix.sub_apply]
  ring

theorem quad_smul (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    quad (c • A) v = c * quad A v := by
  rw [quad_expand, quad_expand]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Null polarization.**  A symmetric matrix whose quadratic form vanishes
on every η-null vector is a multiple of η, coefficient `−M₀₀`.  This is the
algebraic step that promotes scalar equilibrium in every local null frame to
a tensor equation. -/
theorem null_polarization (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hsymm : ∀ i j, M i j = M j i)
    (hnull : ∀ v : Fin 4 → ℝ, quad eta v = 0 → quad M v = 0) :
    M = (-(M 0 0)) • eta := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  -- e0 + ei and e0 - ei null directions
  have hp1 : quad M (fun j => if j = 0 then 1 else if j = 1 then 1 else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  have hm1 : quad M (fun j => if j = 0 then 1 else if j = 1 then (-1) else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  have hp2 : quad M (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  have hm2 : quad M (fun j => if j = 0 then 1 else if j = 2 then (-1) else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  have hp3 : quad M (fun j => if j = 0 then 1 else if j = 3 then 1 else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  have hm3 : quad M (fun j => if j = 0 then 1 else if j = 3 then (-1) else 0)
      = 0 := by
    apply hnull
    rw [quad_eta]
    norm_num [Fin.ext_iff]
  rw [quad_expand] at hp1 hm1 hp2 hm2 hp3 hm3
  norm_num [Fin.ext_iff] at hp1 hm1 hp2 hm2 hp3 hm3
  have h01 : M 0 1 = 0 := by
    have s := hsymm 1 0
    linarith [hp1, hm1]
  have h11 : M 1 1 = -(M 0 0) := by
    have s := hsymm 1 0
    linarith [hp1, hm1]
  have h02 : M 0 2 = 0 := by
    have s := hsymm 2 0
    linarith [hp2, hm2]
  have h22 : M 2 2 = -(M 0 0) := by
    have s := hsymm 2 0
    linarith [hp2, hm2]
  have h03 : M 0 3 = 0 := by
    have s := hsymm 3 0
    linarith [hp3, hm3]
  have h33 : M 3 3 = -(M 0 0) := by
    have s := hsymm 3 0
    linarith [hp3, hm3]
  -- (√2, 1, 1, 0)-type null directions for the space-space components
  have hx12 : quad M (fun j => if j = 0 then Real.sqrt 2
      else if j = 3 then 0 else 1) = 0 := by
    apply hnull
    rw [quad_eta]
    first
    | (norm_num [Fin.ext_iff]; linarith [hs2])
    | norm_num [Fin.ext_iff]
  have hx13 : quad M (fun j => if j = 0 then Real.sqrt 2
      else if j = 2 then 0 else 1) = 0 := by
    apply hnull
    rw [quad_eta]
    first
    | (norm_num [Fin.ext_iff]; linarith [hs2])
    | norm_num [Fin.ext_iff]
  have hx23 : quad M (fun j => if j = 0 then Real.sqrt 2
      else if j = 1 then 0 else 1) = 0 := by
    apply hnull
    rw [quad_eta]
    first
    | (norm_num [Fin.ext_iff]; linarith [hs2])
    | norm_num [Fin.ext_iff]
  rw [quad_expand] at hx12 hx13 hx23
  norm_num [Fin.ext_iff] at hx12 hx13 hx23
  have h12 : M 1 2 = 0 := by
    have s10 := hsymm 1 0
    have s20 := hsymm 2 0
    have s21 := hsymm 2 1
    have e12 : Real.sqrt 2 * (M 0 0 * Real.sqrt 2 + M 0 1 + M 0 2)
        + (M 1 0 * Real.sqrt 2 + M 1 1 + M 1 2)
        + (M 2 0 * Real.sqrt 2 + M 2 1 + M 2 2)
        = (Real.sqrt 2 * Real.sqrt 2) * M 0 0
          + Real.sqrt 2 * (M 0 1 + M 0 2 + M 1 0 + M 2 0)
          + (M 1 1 + M 2 2 + M 1 2 + M 2 1) := by ring
    rw [e12, hs2] at hx12
    have hz : M 0 1 + M 0 2 + M 1 0 + M 2 0 = 0 := by
      linarith [h01, h02, s10, s20]
    rw [hz, mul_zero] at hx12
    linarith [hx12, h11, h22, s21]
  have h13 : M 1 3 = 0 := by
    have s10 := hsymm 1 0
    have s30 := hsymm 3 0
    have s31 := hsymm 3 1
    have e13 : Real.sqrt 2 * (M 0 0 * Real.sqrt 2 + M 0 1 + M 0 3)
        + (M 1 0 * Real.sqrt 2 + M 1 1 + M 1 3)
        + (M 3 0 * Real.sqrt 2 + M 3 1 + M 3 3)
        = (Real.sqrt 2 * Real.sqrt 2) * M 0 0
          + Real.sqrt 2 * (M 0 1 + M 0 3 + M 1 0 + M 3 0)
          + (M 1 1 + M 3 3 + M 1 3 + M 3 1) := by ring
    rw [e13, hs2] at hx13
    have hz : M 0 1 + M 0 3 + M 1 0 + M 3 0 = 0 := by
      linarith [h01, h03, s10, s30]
    rw [hz, mul_zero] at hx13
    linarith [hx13, h11, h33, s31]
  have h23 : M 2 3 = 0 := by
    have s20 := hsymm 2 0
    have s30 := hsymm 3 0
    have s32 := hsymm 3 2
    have e23 : Real.sqrt 2 * (M 0 0 * Real.sqrt 2 + M 0 2 + M 0 3)
        + (M 2 0 * Real.sqrt 2 + M 2 2 + M 2 3)
        + (M 3 0 * Real.sqrt 2 + M 3 2 + M 3 3)
        = (Real.sqrt 2 * Real.sqrt 2) * M 0 0
          + Real.sqrt 2 * (M 0 2 + M 0 3 + M 2 0 + M 3 0)
          + (M 2 2 + M 3 3 + M 2 3 + M 3 2) := by ring
    rw [e23, hs2] at hx23
    have hz : M 0 2 + M 0 3 + M 2 0 + M 3 0 = 0 := by
      linarith [h02, h03, s20, s30]
    rw [hz, mul_zero] at hx23
    linarith [hx23, h22, h33, s32]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, eta, Matrix.diagonal_apply, smul_eq_mul] <;>
    norm_num [Fin.ext_iff] <;>
    first
    | exact h01
    | exact h02
    | exact h03
    | exact h11
    | exact h22
    | exact h33
    | exact h12
    | exact h13
    | exact h23
    | exact (hsymm 1 0).trans h01
    | exact (hsymm 2 0).trans h02
    | exact (hsymm 3 0).trans h03
    | exact (hsymm 2 1).trans h12
    | exact (hsymm 3 1).trans h13
    | exact (hsymm 3 2).trans h23

/-- **EINSTEIN'S EQUATIONS.**  If, at every parameter point, the geometric
tensor `G` and matter tensor `T` satisfy scalar equilibrium in EVERY null
direction (the equation-of-state input, quantified by the derived
small-diamond dictionary of this repository), and the 00-mismatch is
conserved (differentiable with zero derivative — Bianchi + matter
conservation), then

    ∃ Λ,  ∀ x,   G x + Λ·η = κ·T x :

the Einstein field equations, with the cosmological constant Λ arising as an
INTEGRATION CONSTANT — undetermined by the field equations, hence free to
fluctuate.  The statistics of that free constant are exactly what the
fluctuation calculus of this repository computes. -/
theorem einstein_equation (κ : ℝ)
    (G T : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hGsymm : ∀ x i j, G x i j = G x j i)
    (hTsymm : ∀ x i j, T x i j = T x j i)
    (hequil : ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
      quad (G x) v = κ * quad (T x) v)
    (hdiff : Differentiable ℝ (fun x => G x 0 0 - κ * T x 0 0))
    (hcons : ∀ x, deriv (fun y => G y 0 0 - κ * T y 0 0) x = 0) :
    ∃ Λ : ℝ, ∀ x, G x + Λ • eta = κ • T x := by
  have hpoint : ∀ x, G x - κ • T x
      = (-(G x 0 0 - κ * T x 0 0)) • eta := by
    intro x
    have hsymm : ∀ i j, (G x - κ • T x) i j = (G x - κ • T x) j i := by
      intro i j
      simp [Matrix.sub_apply, Matrix.smul_apply, hGsymm x i j, hTsymm x i j]
    have hnull : ∀ v : Fin 4 → ℝ, quad eta v = 0 →
        quad (G x - κ • T x) v = 0 := by
      intro v hv
      rw [quad_sub, quad_smul, hequil x v hv]
      ring
    have hpol := null_polarization (G x - κ • T x) hsymm hnull
    rw [hpol]
    have hentry : (G x - κ • T x) 0 0 = G x 0 0 - κ * T x 0 0 := by
      simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hentry]
  have hconst := is_const_of_deriv_eq_zero hdiff hcons
  refine ⟨G 0 0 0 - κ * T 0 0 0, ?_⟩
  intro x
  have hlam : G x 0 0 - κ * T x 0 0 = G 0 0 0 - κ * T 0 0 0 := hconst x 0
  have h2 : G x - κ • T x = (-(G 0 0 0 - κ * T 0 0 0)) • eta := by
    rw [hpoint x, hlam]
  rw [sub_eq_iff_eq_add] at h2
  rw [h2, neg_smul]
  abel

#print axioms null_polarization
#print axioms einstein_equation

end UnifiedTheory.Audit.KFCausalCSpecEinsteinEquations
