/- Two facts about commuting orthogonal shifts on a real inner product space.
A lattice Weitzenböck identity: |curl|² + |div|² = sum of all |∇_ν ω_μ|².
An antiperiodic spectral bound: T^N = -1 implies |Tx - x|² ≥ (2 - 2cos(π/N))|x|². -/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal shift with its inverse, given as an adjoint pair. -/
structure Shift (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  T : E →ₗ[ℝ] E
  S : E →ₗ[ℝ] E
  adj : ∀ x y, ⟪T x, y⟫ = ⟪x, S y⟫
  left : ∀ x, S (T x) = x
  right : ∀ x, T (S x) = x

namespace Shift
variable (A B : Shift E)

theorem norm_T (x : E) : ‖A.T x‖ = ‖x‖ := by
  have h : ⟪A.T x, A.T x⟫ = ⟪x, x⟫ := by rw [A.adj, A.left]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem norm_S (x : E) : ‖A.S x‖ = ‖x‖ := by
  have h := A.norm_T (A.S x)
  rw [A.right] at h
  exact h.symm

/-- The covariant difference and its adjoint. -/
def D (x : E) : E := A.T x - x
def Dstar (x : E) : E := A.S x - x

theorem D_adj (x y : E) : ⟪A.D x, y⟫ = ⟪x, A.Dstar y⟫ := by
  simp only [D, Dstar, inner_sub_left, inner_sub_right, A.adj]

theorem norm_Dstar (x : E) : ‖A.Dstar x‖ = ‖A.D x‖ := by
  have h : ‖A.Dstar x‖ ^ 2 = ‖A.D x‖ ^ 2 := by
    simp only [D, Dstar]
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_S, norm_T, A.adj, real_inner_comm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem S_T_comm (h : ∀ x, A.T (B.T x) = B.T (A.T x)) (x : E) :
    A.S (B.T x) = B.T (A.S x) := by
  have : A.T (A.S (B.T x)) = A.T (B.T (A.S x)) := by
    rw [A.right, h, A.right]
  have h2 := congrArg A.S this
  rwa [A.left, A.left] at h2

/-- Mixed covariant differences commute with adjoint differences. -/
theorem D_Dstar_comm (h : ∀ x, A.T (B.T x) = B.T (A.T x)) (x : E) :
    B.D (A.Dstar x) = A.Dstar (B.D x) := by
  simp only [D, Dstar, map_sub]
  rw [S_T_comm A B h]
  abel

theorem cross (h : ∀ x, A.T (B.T x) = B.T (A.T x)) (x y : E) :
    ⟪A.Dstar x, B.Dstar y⟫ = ⟪B.D x, A.D y⟫ := by
  rw [← B.D_adj, D_Dstar_comm A B h, real_inner_comm, ← A.D_adj, real_inner_comm]

end Shift

/-- Lattice curl component in the plane (μ, ν). -/
def curl (A : Fin 4 → Shift E) (ω : Fin 4 → E) (μ ν : Fin 4) : E :=
  (A μ).D (ω ν) - (A ν).D (ω μ)

/-- Lattice divergence: the adjoint of the gauge direction. -/
def div (A : Fin 4 → Shift E) (ω : Fin 4 → E) : E := ∑ μ, (A μ).Dstar (ω μ)

/-- The curl energy over the six planes. -/
def curlEnergy (A : Fin 4 → Shift E) (ω : Fin 4 → E) : ℝ :=
  ∑ μ, ∑ ν, if μ < ν then ‖curl A ω μ ν‖ ^ 2 else 0

/-- Lattice Weitzenböck identity for commuting orthogonal shifts. -/
theorem weitzenbock (A : Fin 4 → Shift E)
    (hc : ∀ μ ν x, (A μ).T ((A ν).T x) = (A ν).T ((A μ).T x)) (ω : Fin 4 → E) :
    curlEnergy A ω + ‖div A ω‖ ^ 2 = ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 := by
  have hd : ‖div A ω‖ ^ 2 = ∑ μ, ∑ ν, ⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ := by
    rw [← real_inner_self_eq_norm_sq, div, sum_inner]
    simp only [inner_sum]
  have hx (μ ν : Fin 4) : ⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ =
      ⟪(A ν).D (ω μ), (A μ).D (ω ν)⟫ := Shift.cross _ _ (hc μ ν) _ _
  have hdiag (μ : Fin 4) : ⟪(A μ).D (ω μ), (A μ).D (ω μ)⟫ = ‖(A μ).D (ω μ)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [hd]
  simp only [hx, curlEnergy, curl, norm_sub_sq_real]
  simp only [Fin.sum_univ_four, hdiag]
  simp (decide := true) only [if_true, if_false]
  simp only [real_inner_comm]
  ring_nf

/-- The Weitzenböck lower bound using one direction `κ` for each form component. -/
theorem energy_lower_bound (A : Fin 4 → Shift E)
    (hc : ∀ μ ν x, (A μ).T ((A ν).T x) = (A ν).T ((A μ).T x)) (ω : Fin 4 → E)
    (κ : Fin 4) (lam : ℝ) (hb : ∀ x, lam * ‖x‖ ^ 2 ≤ ‖(A κ).D x‖ ^ 2) :
    lam * ∑ μ, ‖ω μ‖ ^ 2 ≤ curlEnergy A ω + ‖div A ω‖ ^ 2 := by
  rw [weitzenbock A hc, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => (hb (ω μ)).trans ?_
  exact Finset.single_le_sum (f := fun ν => ‖(A ν).D (ω μ)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ κ)

/-! ### The antiperiodic bound -/

section Antiperiodic
variable [FiniteDimensional ℝ E] (A : Shift E) (N : ℕ) (hN : 0 < N)
  (hper : ∀ x, (A.T ^ N) x = -x)

/-- The symmetric part of the shift. -/
noncomputable def symPart : E →ₗ[ℝ] E := (1 / 2 : ℝ) • (A.T + A.S)

theorem symPart_symmetric : (symPart A).IsSymmetric := by
  intro x y
  simp only [symPart, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, A.adj]
  have h : ⟪A.S x, y⟫ = ⟪x, A.T y⟫ := by
    rw [real_inner_comm, ← A.adj, real_inner_comm]
  rw [h]
  simp
  ring

theorem symPart_inner (x : E) : ⟪symPart A x, x⟫ = ⟪A.T x, x⟫ := by
  have h : ⟪A.S x, x⟫ = ⟪A.T x, x⟫ := by
    rw [real_inner_comm, ← A.adj]
  simp only [symPart, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_add_left, h]
  simp
  ring

include hN hper in
/-- Every eigenvalue of the symmetric part is at most `cos (π / N)`. -/
theorem eigenvalue_le (v : E) (μ : ℝ) (hv : ‖v‖ = 1) (he : symPart A v = μ • v) :
    μ ≤ Real.cos (Real.pi / N) := by
  have hrec : ∀ k x, (A.T ^ (k + 1)) x + (A.T ^ k) (A.S x) = (2 : ℝ) • (A.T ^ k) (symPart A x) := by
    intro k x
    simp only [symPart, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, smul_smul]
    norm_num
    rw [pow_succ]
    rfl
  set a : ℕ → ℝ := fun k => ⟪(A.T ^ k) v, v⟫ with ha
  have h0 : a 0 = 1 := by
    simp [ha, hv]
  have h1 : a 1 = μ := by
    have := symPart_inner A v
    rw [he, inner_smul_left, real_inner_self_eq_norm_sq, hv] at this
    simp [ha] at this ⊢
    linarith
  have hμ : |μ| ≤ 1 := by
    rw [← h1]
    have := abs_real_inner_le_norm (A.T v) v
    rw [A.norm_T, hv] at this
    simpa [ha] using (by simpa using this : |⟪A.T v, v⟫| ≤ 1)
  have hstep (k : ℕ) : a (k + 2) + a k = 2 * μ * a (k + 1) := by
    have hk := hrec (k + 1) v
    have hS : (A.T ^ (k + 1)) (A.S v) = (A.T ^ k) v := by
      rw [pow_succ, Module.End.mul_apply, A.right]
    rw [hS, he, map_smul, smul_smul] at hk
    have := congrArg (fun z => ⟪z, v⟫) hk
    simp only [inner_add_left, inner_smul_left] at this
    simpa [ha] using this
  have hmu : μ ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hμ
  set θ := Real.arccos μ with hθ
  have hcos : Real.cos θ = μ := Real.cos_arccos hmu.1 hmu.2
  have hform : ∀ k, a k = Real.cos (k * θ) ∧ a (k + 1) = Real.cos ((k + 1) * θ) := by
    intro k
    induction k with
    | zero => simp [h0, h1, hcos]
    | succ k ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have hs := hstep k
      have hc : Real.cos ((k + 2) * θ) + Real.cos (k * θ) = 2 * μ * Real.cos ((k + 1) * θ) := by
        have e1 : ((k : ℝ) + 2) * θ = (k + 1) * θ + θ := by ring
        have e2 : (k : ℝ) * θ = (k + 1) * θ - θ := by ring
        rw [e1, e2, Real.cos_add, Real.cos_sub, hcos]
        ring
      have : a (k + 2) = Real.cos ((k + 2) * θ) := by
        rw [ih.1, ih.2] at hs
        linarith
      push_cast
      rw [show ((k : ℝ) + 1 + 1) = k + 2 by ring]
      exact this
  have haN : a N = -1 := by
    simp [ha, hper, hv]
  have hNθ : Real.cos (N * θ) = -1 := by
    rw [← (hform N).1, haN]
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : Real.pi / N ≤ θ := by
    by_contra hlt
    push_neg at hlt
    have hlt' : N * θ < Real.pi := by
      rwa [lt_div_iff₀' hNpos] at hlt
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hlt'
    rw [Real.cos_pi, hNθ] at this
    exact lt_irrefl _ this
  rw [← hcos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθπ hle

include hN hper in
/-- The Rayleigh bound, by expansion in an eigenbasis of the symmetric part. -/
theorem inner_le (x : E) : ⟪A.T x, x⟫ ≤ Real.cos (Real.pi / N) * ‖x‖ ^ 2 := by
  have hs := symPart_symmetric A
  set b := hs.eigenvectorBasis rfl with hb
  have hexp (y : E) : ⟪y, x⟫ = ∑ i, ⟪y, b i⟫ * ⟪b i, x⟫ := (b.sum_inner_mul_inner y x).symm
  rw [← symPart_inner, hexp, ← real_inner_self_eq_norm_sq, hexp x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hev : symPart A (b i) = (hs.eigenvalues rfl i) • b i :=
    hs.apply_eigenvectorBasis rfl i
  have hl := eigenvalue_le A N hN hper (b i) _ (b.orthonormal.1 i) hev
  have hsy : ⟪symPart A x, b i⟫ = hs.eigenvalues rfl i * ⟪x, b i⟫ := by
    rw [hs x (b i), hev, inner_smul_right]
  rw [hsy, real_inner_comm x (b i)]
  nlinarith [mul_self_nonneg ⟪b i, x⟫, mul_le_mul_of_nonneg_right hl (mul_self_nonneg ⟪b i, x⟫)]

include hN hper in
/-- The antiperiodic spectral bound. -/
theorem D_lower_bound (x : E) :
    (2 - 2 * Real.cos (Real.pi / N)) * ‖x‖ ^ 2 ≤ ‖A.D x‖ ^ 2 := by
  have h := inner_le A N hN hper x
  have : ‖A.D x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪A.T x, x⟫ := by
    rw [Shift.D, norm_sub_sq_real, A.norm_T]
    ring
  rw [this]
  linarith

end Antiperiodic

/-- `2 - 2 cos (π / N) = 4 sin² (π / 2N)`. -/
theorem two_sub_cos (N : ℝ) :
    2 - 2 * Real.cos (Real.pi / N) = 4 * Real.sin (Real.pi / (2 * N)) ^ 2 := by
  have h : Real.pi / N = 2 * (Real.pi / (2 * N)) := by
    by_cases hN : N = 0
    · simp [hN]
    · field_simp
  rw [h, Real.cos_two_mul, Real.cos_sq']
  ring

end UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts
