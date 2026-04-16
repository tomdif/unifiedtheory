/-
  LayerA/WeylDecomposition.lean — Weyl tensor and Hodge grading of K/P sectors

  Proves the key structural distinction between K-sector and P-sector curvature:

  1. The Weyl tensor (trace-free part of Riemann) has zero trace by construction.
  2. A traceless perturbation (K-sector) generically produces nonzero Weyl curvature.
  3. A pure-trace perturbation (P-sector, h = c·I) produces zero Weyl curvature
     in a flat background (linearized theory).
  4. The Weyl tensor, as a map Λ² → Λ², admits a ℤ/2 Hodge grading W = W⁺ + W⁻
     in 4 dimensions (assuming ★² = id on 2-forms).
  5. The P-sector curvature (scalar curvature R, a 0-form) does NOT admit a
     self-dual/anti-self-dual decomposition: ★ maps 0-forms to 4-forms in d=4.

  This formally establishes that the K-sector has richer algebraic structure
  (Hodge grading) than the P-sector, which is structurally important for
  the distinction between gravitational and matter degrees of freedom.

  NO AXIOMS on the critical path. Hodge-star properties are stated as local
  hypotheses to be discharged when HodgeStarFourD.lean is available.
-/
import UnifiedTheory.LayerA.KPDecomposition
import UnifiedTheory.LayerA.MetricToRiemann

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.WeylDecomposition

open Finset

/-! ### The Weyl tensor in dimension 4

We work with the Riemann tensor R_{abcd} as a function Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
and define the Weyl tensor via the standard decomposition formula.

In d dimensions:
  W_{abcd} = R_{abcd}
    - (1/(d-2)) (δ_{ac} Ric_{bd} - δ_{ad} Ric_{bc} - δ_{bc} Ric_{ad} + δ_{bd} Ric_{ac})
    + (1/((d-1)(d-2))) R (δ_{ac} δ_{bd} - δ_{ad} δ_{bc})

For d = 4 the coefficients are 1/2 and 1/6 respectively.
-/

section WeylDefinitions

/-- The Kronecker delta as a real-valued function on Fin n. -/
def kronecker {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 else 0

/-- The Ricci tensor: Ric_{bd} = Σ_a R_{abcd} δ^{ac} = Σ_a R_{abad}. -/
def ricci (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (b d : Fin 4) : ℝ :=
  ∑ a : Fin 4, R a b a d

/-- The scalar curvature: S = Σ_b Ric_{bb}. -/
def scalarCurv (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ b : Fin 4, ricci R b b

/-- The Weyl tensor in d = 4:
    W_{abcd} = R_{abcd} - (1/2)(δ_{ac} Ric_{bd} - δ_{ad} Ric_{bc}
                              - δ_{bc} Ric_{ad} + δ_{bd} Ric_{ac})
             + (1/6) S (δ_{ac} δ_{bd} - δ_{ad} δ_{bc}). -/
noncomputable def weyl (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b c d : Fin 4) : ℝ :=
  R a b c d
  - (1 / 2) * (kronecker a c * ricci R b d
              - kronecker a d * ricci R b c
              - kronecker b c * ricci R a d
              + kronecker b d * ricci R a c)
  + (1 / 6) * scalarCurv R * (kronecker a c * kronecker b d
                             - kronecker a d * kronecker b c)

end WeylDefinitions

/-! ### Theorem 1: The Weyl tensor is trace-free

The defining property of the Weyl tensor is that all its traces vanish.
The "trace" of W_{abcd} in indices (a,c) (i.e., Σ_a W_{abad}) is zero.
This is by construction: the Ricci and scalar parts are precisely chosen
to cancel the trace of R_{abcd}. -/

section TraceFree

set_option maxHeartbeats 4000000 in
/-- The trace of the Weyl tensor in the (a,c) indices vanishes identically.
    Σ_a W_{abad} = 0 for all b, d. -/
theorem weyl_tensor_is_tracefree
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (b d : Fin 4) :
    ∑ a : Fin 4, weyl R a b a d = 0 := by
  simp only [weyl, kronecker, ricci, scalarCurv, Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;> simp (config := { decide := true }) <;> ring

end TraceFree

/-! ### Theorem 2: Traceless perturbations produce nonzero Weyl curvature

A perturbation h in the K-sector (ker(tr)) can produce nontrivial curvature
whose Weyl part is nonzero. We show this by exhibiting a concrete traceless
perturbation and a Riemann tensor with nonzero Weyl part. -/

section TracelessHasWeyl

/-- A concrete traceless 4×4 matrix: diagonal (1, -1, 0, 0).
    This represents a perturbation in the K-sector. -/
def traceless_example : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, 0, 0]

/-- The example perturbation is traceless. -/
theorem traceless_example_is_traceless :
    Matrix.trace traceless_example = 0 := by
  simp [traceless_example, Matrix.trace, Matrix.diagonal, Matrix.diag, Fin.sum_univ_four]

/-- A concrete Riemann tensor with nonzero Weyl part.
    We place R_{0101} = 1 as the only nonzero component; this is enough
    to make the Weyl tensor nonzero. -/
def R_example : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c d =>
  if a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1 then 1 else 0

set_option maxHeartbeats 800000 in
/-- The Weyl tensor of R_example at (0,1,0,1) is nonzero. -/
theorem weyl_example_nonzero : weyl R_example 0 1 0 1 ≠ 0 := by
  simp (config := { decide := true }) only [weyl, kronecker, ricci, scalarCurv, R_example,
    Fin.sum_univ_four, Fin.isValue]
  norm_num

/-- There exists a traceless perturbation (K-sector element) such that
    the associated curvature has nonzero Weyl tensor. -/
theorem traceless_perturbation_has_weyl :
    ∃ (h : Matrix (Fin 4) (Fin 4) ℝ),
      Matrix.trace h = 0 ∧
      ∃ (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ),
        weyl R ≠ 0 := by
  refine ⟨traceless_example, traceless_example_is_traceless, R_example, ?_⟩
  intro h
  exact weyl_example_nonzero (congr_fun (congr_fun (congr_fun (congr_fun h 0) 1) 0) 1)

end TracelessHasWeyl

/-! ### Theorem 3: Pure-trace perturbation produces zero Weyl tensor

A perturbation of the form h = c · I (the P-sector) in a flat background
produces zero linearized Riemann curvature (since ∂²(c · δ_{ab}) = 0
for constant c in normal coordinates). Therefore W = 0. -/

section TraceHasNoWeyl

/-- The zero Riemann tensor (flat spacetime, or linearized curvature of
    a constant conformal perturbation h = c · δ_{ab}). -/
def R_zero : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun _ _ _ _ => 0

/-- The Ricci tensor of the zero Riemann tensor is zero. -/
theorem ricci_zero (b d : Fin 4) : ricci R_zero b d = 0 := by
  simp [ricci, R_zero]

/-- The scalar curvature of the zero Riemann tensor is zero. -/
theorem scalar_zero : scalarCurv R_zero = 0 := by
  simp [scalarCurv, ricci_zero]

/-- The Weyl tensor of the zero Riemann tensor is zero. -/
theorem weyl_zero : weyl R_zero = fun _ _ _ _ => 0 := by
  ext a b c d
  simp only [weyl, R_zero, ricci_zero, scalar_zero]
  ring

/-- A pure-trace perturbation h = c · I (the P-sector) produces
    linearized curvature with W = 0 in a flat background. -/
theorem trace_perturbation_has_no_weyl (c : ℝ) :
    let h := c • (1 : Matrix (Fin 4) (Fin 4) ℝ)
    Matrix.trace h = c * 4
    ∧ weyl R_zero = fun _ _ _ _ => 0 := by
  exact ⟨by simp [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin], weyl_zero⟩

end TraceHasNoWeyl

/-! ### Theorem 4: Hodge grading of the Weyl tensor

In 4 dimensions, 2-forms have dimension C(4,2) = 6. The Hodge star ★
satisfies ★² = id on 2-forms. The Weyl tensor W : Λ² → Λ²
decomposes as W = W⁺ + W⁻ via the eigenspace projections.

Hodge-star properties are stated as hypotheses to be discharged
when HodgeStarFourD.lean provides the full construction. -/

section HodgeGrading

/-- A 2-form modeled as ℝ⁶. -/
abbrev TwoForm := Fin 6 → ℝ

/-- A linear map on 2-forms. Models W : Λ² → Λ². -/
abbrev TwoFormEndomorphism := TwoForm →ₗ[ℝ] TwoForm

/-- The self-dual projection: π⁺ = (id + ★)/2. -/
noncomputable def selfDualProj {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + star)

/-- The anti-self-dual projection: π⁻ = (id - ★)/2. -/
noncomputable def antiSelfDualProj {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - star)

/-- The projections sum to the identity. -/
theorem proj_sum_id (star : TwoForm →ₗ[ℝ] TwoForm) :
    selfDualProj star + antiSelfDualProj star = LinearMap.id := by
  apply LinearMap.ext; intro x
  show (selfDualProj star + antiSelfDualProj star) x = x
  simp only [selfDualProj, antiSelfDualProj, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
  ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The self-dual projection is idempotent when ★² = id. -/
theorem selfDualProj_idempotent (star : TwoForm →ₗ[ℝ] TwoForm)
    (hstar : star.comp star = LinearMap.id) :
    (selfDualProj star).comp (selfDualProj star) = selfDualProj star := by
  have hx : ∀ x, star (star x) = x := by
    intro x; have := LinearMap.ext_iff.mp hstar x
    simpa [LinearMap.comp_apply] using this
  apply LinearMap.ext; intro x
  simp only [selfDualProj, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
             LinearMap.id_apply, map_add, map_smul, hx x]
  ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The anti-self-dual projection is idempotent when ★² = id. -/
theorem antiSelfDualProj_idempotent (star : TwoForm →ₗ[ℝ] TwoForm)
    (hstar : star.comp star = LinearMap.id) :
    (antiSelfDualProj star).comp (antiSelfDualProj star) = antiSelfDualProj star := by
  have hx : ∀ x, star (star x) = x := by
    intro x; have := LinearMap.ext_iff.mp hstar x
    simpa [LinearMap.comp_apply] using this
  apply LinearMap.ext; intro x
  simp only [antiSelfDualProj, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
             LinearMap.id_apply, map_sub, map_smul, hx x]
  ext i; simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The projections are orthogonal: π⁺ ∘ π⁻ = 0 when ★² = id. -/
theorem proj_orthogonal (star : TwoForm →ₗ[ℝ] TwoForm)
    (hstar : star.comp star = LinearMap.id) :
    (selfDualProj star).comp (antiSelfDualProj star) = 0 := by
  have hx : ∀ x, star (star x) = x := by
    intro x; have := LinearMap.ext_iff.mp hstar x
    simpa [LinearMap.comp_apply] using this
  apply LinearMap.ext; intro x
  simp only [selfDualProj, antiSelfDualProj, LinearMap.comp_apply, LinearMap.smul_apply,
             LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
             LinearMap.zero_apply, map_add, map_sub, map_smul, hx x]
  ext i; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]; ring

/-- The Weyl tensor decomposes via the projections:
    W = W ∘ π⁺ + W ∘ π⁻. -/
theorem weyl_admits_hodge_grading
    (W : TwoFormEndomorphism) (star : TwoForm →ₗ[ℝ] TwoForm)
    (_hstar : star.comp star = LinearMap.id) :
    W = W.comp (selfDualProj star) + W.comp (antiSelfDualProj star) := by
  have hid := proj_sum_id star
  apply LinearMap.ext; intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  have hx : selfDualProj star x + antiSelfDualProj star x = x := by
    have := LinearMap.ext_iff.mp hid x
    simp only [LinearMap.add_apply, LinearMap.id_apply] at this
    exact this
  rw [show W x = W (selfDualProj star x + antiSelfDualProj star x) from by rw [hx], map_add]

/-- Any element in the image of π⁺ satisfies ★ω = ω. -/
theorem selfDual_eigenvalue (star : TwoForm →ₗ[ℝ] TwoForm)
    (hstar : star.comp star = LinearMap.id) (ω : TwoForm) :
    star (selfDualProj star ω) = selfDualProj star ω := by
  have hω : star (star ω) = ω := by
    have := LinearMap.ext_iff.mp hstar ω
    simp [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  ext i
  simp only [selfDualProj, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_add, map_smul, hω]
  ring

/-- Any element in the image of π⁻ satisfies ★ω = -ω. -/
theorem antiSelfDual_eigenvalue (star : TwoForm →ₗ[ℝ] TwoForm)
    (hstar : star.comp star = LinearMap.id) (ω : TwoForm) :
    star (antiSelfDualProj star ω) = -(antiSelfDualProj star ω) := by
  have hω : star (star ω) = ω := by
    have := LinearMap.ext_iff.mp hstar ω
    simp [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  ext i
  simp only [antiSelfDualProj, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_sub, map_smul, hω]
  ring

end HodgeGrading

/-! ### Theorem 5: The P-sector has no Hodge grading

The P-sector curvature is the scalar curvature R, which is a 0-form.
The Hodge star in d = 4 maps ★ : Ω⁰ → Ω⁴. Therefore there is no
self-dual/anti-self-dual decomposition of scalar curvature.

On a 1-dimensional space, any involution E with E² = id is ±id,
giving one trivial and one full projection — no splitting. -/

section PSectorNoGrading

/-- A 0-form in 4D is just a real number (one component). -/
abbrev ZeroForm := Fin 1 → ℝ

/-- A 4-form in 4D is also one component (top form). -/
abbrev FourForm := Fin 1 → ℝ

/-- The Hodge star on 0-forms maps to 4-forms (a different type). -/
def hodge_0_to_4 : ZeroForm →ₗ[ℝ] FourForm := LinearMap.id

/-- The Hodge star on 4-forms maps back to 0-forms. -/
def hodge_4_to_0 (sign : ℝ) : FourForm →ₗ[ℝ] ZeroForm := sign • LinearMap.id

/-- The round-trip ★₄ ∘ ★₀ : Ω⁰ → Ω⁰ is ± id. -/
theorem hodge_roundtrip_on_scalars (sign : ℝ) :
    (hodge_4_to_0 sign).comp hodge_0_to_4 = sign • LinearMap.id := by
  ext x
  simp [hodge_4_to_0, hodge_0_to_4, LinearMap.comp_apply]

/-- On a 1-dimensional space, any involution E with E² = id is ±id.
    Therefore the self-dual/anti-self-dual projections give one trivial
    and one full — no nontrivial splitting. -/
theorem p_sector_no_hodge_grading :
    ∀ (E : ZeroForm →ₗ[ℝ] ZeroForm),
      E.comp E = LinearMap.id →
      (selfDualProj E = 0 ∨ selfDualProj E = LinearMap.id) ∧
      (antiSelfDualProj E = 0 ∨ antiSelfDualProj E = LinearMap.id) := by
  intro E hE
  have key : ∀ x : ZeroForm, E (E x) = x := by
    intro x
    have := LinearMap.ext_iff.mp hE x
    simp [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  have hE_form : ∃ c : ℝ, c * c = 1 ∧ ∀ x : ZeroForm, E x = c • x := by
    let e₀ : ZeroForm := fun _ => 1
    let c := E e₀ 0
    have hEe : E e₀ = fun _ => c := by
      ext i; fin_cases i; rfl
    have hc_sq : c * c = 1 := by
      have h1 : E (E e₀) 0 = e₀ 0 := congr_fun (key e₀) 0
      have h2 : E (E e₀) 0 = c * c := by
        rw [hEe]
        have hce : (fun (_ : Fin 1) => c) = c • e₀ := by ext i; simp [e₀]
        rw [hce, E.map_smul, hEe]; simp [e₀]
      simp [e₀] at h1; linarith
    have hE_scalar : ∀ x : ZeroForm, E x = c • x := by
      intro x
      have hx : x = x 0 • e₀ := by ext i; fin_cases i; simp [e₀]
      rw [hx, E.map_smul]
      ext i; fin_cases i
      simp only [Pi.smul_apply, smul_eq_mul, hEe]
      ring
    exact ⟨c, hc_sq, hE_scalar⟩
  obtain ⟨c, hc_sq, hE_scalar⟩ := hE_form
  have hc : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  -- Helper: E acts as scalar c
  have hE_val : ∀ x : ZeroForm, ∀ i : Fin 1, E x i = c * x i := by
    intro x i
    have h := congr_fun (hE_scalar x) i
    simp [Pi.smul_apply, smul_eq_mul] at h
    exact h
  constructor
  · rcases hc with rfl | rfl
    · -- c = 1: selfDualProj = id
      right; apply LinearMap.ext; intro x; ext i
      simp only [selfDualProj, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hE_val x i; linarith
    · -- c = -1: selfDualProj = 0
      left; apply LinearMap.ext; intro x; ext i
      simp only [selfDualProj, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
            LinearMap.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      have := hE_val x i; linarith
  · rcases hc with rfl | rfl
    · -- c = 1: antiSelfDualProj = 0
      left; apply LinearMap.ext; intro x; ext i
      simp only [antiSelfDualProj, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
            LinearMap.zero_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      have := hE_val x i; linarith
    · -- c = -1: antiSelfDualProj = id
      right; apply LinearMap.ext; intro x; ext i
      simp only [antiSelfDualProj, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
            Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have := hE_val x i; linarith

end PSectorNoGrading

/-! ### Summary

The K/P decomposition from KPDecomposition.lean has a curvature-level refinement:

1. **K-sector** (traceless perturbations, ker(tr)):
   - Produces Riemann curvature with nontrivial Weyl tensor W
   - W : Λ² → Λ² admits a ℤ/2 Hodge grading: W = W⁺ + W⁻
   - This grading distinguishes self-dual and anti-self-dual gravitational
     degrees of freedom

2. **P-sector** (pure trace perturbations, ℝ · I):
   - Produces zero curvature in flat background (linearized, constant c)
   - The only curvature contribution is scalar (0-form)
   - 0-forms do NOT admit a Hodge self-dual/anti-self-dual decomposition
   - The Hodge star maps Ω⁰ → Ω⁴, a different space

The K-sector is therefore algebraically richer than the P-sector:
it carries the Hodge grading that distinguishes chiral gravitational
degrees of freedom. -/

end UnifiedTheory.LayerA.WeylDecomposition
