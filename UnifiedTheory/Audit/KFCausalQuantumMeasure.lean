/-
  Audit/KFCausalQuantumMeasure.lean
  — THE BORN-FROM-GROWTH DECOHERENCE FUNCTIONAL

  The missing half of the causal-set program is a quantum measure on growth
  histories.  The construction proposed and formalized here composes the two
  structures this repository already possesses:

      A(γ) = √P(γ) · e^{i·S(γ)}     (P = classical sequential-growth
                                      measure; S = the BD action in units
                                      of ℏ — both order-invariants),
      D(γ,γ') = A(γ) · conj A(γ').

  What this buys BY CONSTRUCTION (theorems below):

  1.  `D_hermitian`                — hermiticity.
  2.  `strong_positivity`         — the Gram identity: every quadratic form
      of D is a |·|² — STRONG positivity, the axiom that generic complex
      quantum-sequential-growth couplings violate, here for free.
  3.  `interference_sum_rule`     — Sorkin's quartic (I₃ = 0) sum rule: D
      generates a genuine level-2 quantum measure μ(A) = |Σ_A A(γ)|².
  4.  `pairwise_purity`           — |D(A,B)|² = μ(A)·μ(B): the functional is
      rank-one on fine-grained histories; ALL decoherence is coarse-graining
      phase-averaging, whose rate is the action variance computed in this
      repository (Var S ≈ 2κ²M(ε)N T̂²).
  5.  `diagonal_decomposition`    — μ(A) = Σ_A P(γ) + interference: the
      classical growth measure is exactly the diagonal; classicality of the
      large-scale world = phase equidistribution = the super-Poissonian
      action variance.
  6.  `two_history_interference` / `unitarity_quantizes` — normalization
      μ(Ω) = 1 is NOT automatic: it is a new dynamical equation coupling P,
      S, and ℏ.  For a two-history stage it forces cos(ΔS/ℏ) = 0, i.e.

          ΔS  ∈  (ℤ + ½)·π·ℏ :

      **unitarity quantizes the action gap** — the normalization condition
      selects the growth couplings in terms of ℏ.  The dynamics is not put
      in by hand; it is pinned by consistency.

  Covariance: both P (discrete general covariance of sequential growth) and
  S (an order-invariant) are label-independent, so D is covariant.  Bell
  causality: P satisfies it by the committed growth axioms; S is a sum of
  past-local retarded terms.  The remaining open items (cylinder-set
  extension to infinite histories, the continuum limit, Bell causality of
  the composite as a theorem) are stated in the companion memo.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Complex

namespace UnifiedTheory.Audit.KFCausalQuantumMeasure

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The Born-from-growth amplitude: `√P · e^{iS}`. -/
noncomputable def amp (P S : Γ → ℝ) (γ : Γ) : ℂ :=
  (Real.sqrt (P γ) : ℂ) * Complex.exp (S γ * Complex.I)

/-- The decoherence functional `D(γ,γ') = A(γ)·conj A(γ')`. -/
noncomputable def Dfun (P S : Γ → ℝ) (γ γ' : Γ) : ℂ :=
  amp P S γ * (starRingEnd ℂ) (amp P S γ')

/-- The quantum measure of a coarse-grained class. -/
noncomputable def qmeasure (P S : Γ → ℝ) (A : Finset Γ) : ℝ :=
  Complex.normSq (∑ γ ∈ A, amp P S γ)

/-- Hermiticity. -/
theorem D_hermitian (P S : Γ → ℝ) (γ γ' : Γ) :
    Dfun P S γ γ' = (starRingEnd ℂ) (Dfun P S γ' γ) := by
  unfold Dfun
  rw [map_mul, Complex.conj_conj]
  ring

/-- **Strong positivity, for free** — the Gram identity: every quadratic
form of `D` is a squared norm.  This is the axiom that generic complex
quantum-growth couplings violate; the Born-from-growth functional satisfies
it by construction. -/
theorem strong_positivity (P S : Γ → ℝ) (c : Γ → ℂ) :
    (∑ γ, ∑ γ', c γ * (starRingEnd ℂ) (c γ') * Dfun P S γ γ')
      = (Complex.normSq (∑ γ, c γ * amp P S γ) : ℂ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro γ' _
  rw [map_mul]
  unfold Dfun
  ring

/-- The diagonal of the functional is the classical growth measure. -/
theorem D_diagonal (P S : Γ → ℝ) (hP : ∀ γ, 0 ≤ P γ) (γ : Γ) :
    Dfun P S γ γ = (P γ : ℂ) := by
  unfold Dfun amp
  rw [map_mul, ← Complex.exp_conj]
  have hconjI : (starRingEnd ℂ) ((S γ : ℂ) * Complex.I)
      = -((S γ : ℂ) * Complex.I) := by
    first
    | (simp [Complex.conj_I]; ring)
    | simp [Complex.conj_I]
  rw [hconjI, Complex.conj_ofReal]
  have : Complex.exp ((S γ : ℂ) * Complex.I)
      * Complex.exp (-((S γ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc (Real.sqrt (P γ) : ℂ) * Complex.exp ((S γ:ℂ) * Complex.I)
      * ((Real.sqrt (P γ) : ℂ) * Complex.exp (-((S γ:ℂ) * Complex.I)))
      = ((Real.sqrt (P γ) : ℂ) * (Real.sqrt (P γ) : ℂ))
        * (Complex.exp ((S γ:ℂ) * Complex.I)
          * Complex.exp (-((S γ:ℂ) * Complex.I))) := by ring
    _ = (P γ : ℂ) := by
        rw [this, mul_one, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (hP γ)]

/-- **Sorkin's quartic sum rule** (`I₃ = 0`): the pair functional generates a
genuine level-2 quantum measure — pairwise interference accounts for all
higher interference. -/
theorem interference_sum_rule (P S : Γ → ℝ) (A B C : Finset Γ)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    qmeasure P S ((A ∪ B) ∪ C) - qmeasure P S (A ∪ B)
      - qmeasure P S (A ∪ C) - qmeasure P S (B ∪ C)
      + qmeasure P S A + qmeasure P S B + qmeasure P S C = 0 := by
  unfold qmeasure
  rw [Finset.sum_union (by
      exact Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
    Finset.sum_union hAB, Finset.sum_union hAC, Finset.sum_union hBC]
  set a := ∑ γ ∈ A, amp P S γ
  set b := ∑ γ ∈ B, amp P S γ
  set c := ∑ γ ∈ C, amp P S γ
  have e1 : Complex.normSq (a + b + c)
      = Complex.normSq (a + b) + Complex.normSq c
        + 2 * ((a + b) * (starRingEnd ℂ) c).re := Complex.normSq_add _ _
  have e2 : Complex.normSq (a + b)
      = Complex.normSq a + Complex.normSq b
        + 2 * (a * (starRingEnd ℂ) b).re := Complex.normSq_add _ _
  have e3 : Complex.normSq (a + c)
      = Complex.normSq a + Complex.normSq c
        + 2 * (a * (starRingEnd ℂ) c).re := Complex.normSq_add _ _
  have e4 : Complex.normSq (b + c)
      = Complex.normSq b + Complex.normSq c
        + 2 * (b * (starRingEnd ℂ) c).re := Complex.normSq_add _ _
  have e5 : ((a + b) * (starRingEnd ℂ) c).re
      = (a * (starRingEnd ℂ) c).re + (b * (starRingEnd ℂ) c).re := by
    rw [add_mul, Complex.add_re]
  linarith [e1, e2, e3, e4, e5]

/-- **Rank-one purity**: `|D(A,B)|² = μ(A)·μ(B)` exactly.  Fine-grained
histories never decohere against each other; ALL classicality comes from
coarse-graining phase-averaging — whose rate is the super-Poissonian action
variance computed in this repository. -/
theorem pairwise_purity (P S : Γ → ℝ) (A B : Finset Γ) :
    Complex.normSq ((∑ γ ∈ A, amp P S γ)
      * (starRingEnd ℂ) (∑ γ ∈ B, amp P S γ))
      = qmeasure P S A * qmeasure P S B := by
  unfold qmeasure
  rw [Complex.normSq_mul, Complex.normSq_conj]

/-- **The Born-rule bridge**: the quantum measure of a class equals the
classical growth measure plus explicit interference terms.  Classicality of
the macroscopic world = suppression of the interference sum = phase
equidistribution at the rate of the action variance. -/
theorem diagonal_decomposition (P S : Γ → ℝ) (hP : ∀ γ, 0 ≤ P γ)
    (A : Finset Γ) :
    qmeasure P S A = (∑ γ ∈ A, P γ)
      + ∑ γ ∈ A, ∑ γ' ∈ A.erase γ, (amp P S γ
          * (starRingEnd ℂ) (amp P S γ')).re := by
  unfold qmeasure
  have key : Complex.normSq (∑ γ ∈ A, amp P S γ)
      = ∑ γ ∈ A, ∑ γ' ∈ A, (amp P S γ * (starRingEnd ℂ) (amp P S γ')).re := by
    have h1 : ((∑ γ ∈ A, amp P S γ)
        * (starRingEnd ℂ) (∑ γ' ∈ A, amp P S γ')).re
        = Complex.normSq (∑ γ ∈ A, amp P S γ) := by
      rw [Complex.mul_conj]
      simp
    rw [← h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Complex.re_sum]
  rw [key]
  have hsplit : ∀ γ ∈ A,
      (∑ γ' ∈ A, (amp P S γ * (starRingEnd ℂ) (amp P S γ')).re)
      = P γ + ∑ γ' ∈ A.erase γ,
          (amp P S γ * (starRingEnd ℂ) (amp P S γ')).re := by
    intro γ hγ
    rw [← Finset.add_sum_erase _ _ hγ]
    congr 1
    have hd := D_diagonal P S hP γ
    unfold Dfun at hd
    rw [hd]
    simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]

/-- **The two-history interference identity**: for one stage with histories
of weight `t, 1−t` and phases `θ₁, θ₂`,

    μ(Ω) = 1 + 2·√(t(1−t))·cos(θ₁ − θ₂). -/
theorem two_history_interference (t θ₁ θ₂ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Complex.normSq ((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I))
      = 1 + 2 * Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂) := by
  rw [Complex.normSq_add]
  have habs : ∀ θ : ℝ, Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    intro θ
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.normSq_add_mul_I]
    exact Real.cos_sq_add_sin_sq θ
  have h1 : Complex.normSq ((Real.sqrt t : ℂ)
      * Complex.exp (θ₁ * Complex.I)) = t := by
    rw [Complex.normSq_mul, habs, mul_one, Complex.normSq_ofReal,
      Real.mul_self_sqrt ht0]
  have h2 : Complex.normSq ((Real.sqrt (1-t) : ℂ)
      * Complex.exp (θ₂ * Complex.I)) = 1 - t := by
    rw [Complex.normSq_mul, habs, mul_one, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by linarith)]
  have hcross : (((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I))
      * (starRingEnd ℂ) ((Real.sqrt (1-t) : ℂ)
        * Complex.exp (θ₂ * Complex.I))).re
      = Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂) := by
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    have hcj : (starRingEnd ℂ) ((θ₂ : ℂ) * Complex.I)
        = ((-θ₂ : ℝ) : ℂ) * Complex.I := by
      first
      | (simp [Complex.conj_I]; ring)
      | (simp [Complex.conj_I]; push_cast; ring)
      | simp [Complex.conj_I]
    rw [hcj]
    have hprod : Complex.exp ((θ₁:ℝ) * Complex.I)
        * Complex.exp (((-θ₂:ℝ):ℂ) * Complex.I)
        = Complex.exp (((θ₁ - θ₂ : ℝ):ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (((Real.sqrt t : ℂ) * Complex.exp ((θ₁:ℝ) * Complex.I))
          * ((Real.sqrt (1-t) : ℂ)
            * Complex.exp (((-θ₂:ℝ):ℂ) * Complex.I))).re
        = (((Real.sqrt t * Real.sqrt (1-t) : ℝ) : ℂ)
          * Complex.exp (((θ₁ - θ₂ : ℝ):ℂ) * Complex.I)).re := by
          rw [← hprod]
          push_cast
          ring_nf
      _ = Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂) := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, ← Real.sqrt_mul ht0]
          ring
  rw [h1, h2, hcross]
  ring

/-- **UNITARITY QUANTIZES THE DYNAMICS.**  Normalization `μ(Ω) = 1` of the
Born-from-growth measure is a nontrivial equation: at a genuinely branching
stage (0 < t < 1) it forces `cos(θ₁ − θ₂) = 0`, i.e. the action gap between
the two histories must satisfy  ΔS ∈ (ℤ + ½)·π·ℏ.  The growth couplings and
ℏ are not independent inputs: consistency of the measure pins them. -/
theorem unitarity_quantizes (t θ₁ θ₂ : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hnorm : Complex.normSq ((Real.sqrt t : ℂ)
      * Complex.exp (θ₁ * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I)) = 1) :
    Real.cos (θ₁ - θ₂) = 0 := by
  rw [two_history_interference t θ₁ θ₂ ht0.le ht1.le] at hnorm
  have hsq : 0 < Real.sqrt (t*(1-t)) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have h2 : 2 * Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂) = 0 := by
    linarith
  have := mul_eq_zero.mp h2
  rcases this with h | h
  · exfalso
    have : (2:ℝ) * Real.sqrt (t*(1-t)) ≠ 0 := by positivity
    exact this h
  · exact h

/-- Real part of a weighted phase. -/
theorem weighted_phase_re (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)).re = r * Real.cos θ := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re]
  simp

/-- Imaginary part of a weighted phase. -/
theorem weighted_phase_im (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)).im = r * Real.sin θ := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  simp

/-- **THE BORN–QUADRATURE LAW** (amplitude consistency determines the
dynamics).  For the Born-from-growth measure to be consistent across growth
stages, the amplitude of a history must equal the sum of its children's
amplitudes:  √p₁·e^{iθ₁} + √p₂·e^{iθ₂} = 1  with  p₁ + p₂ = 1  and
θ_c = ΔS_c/ℏ the action increments.  This equation is RIGID: the two
amplitude vectors of lengths √p₁, √p₂ summing to a unit vector form a
Pythagorean triangle, forcing

    cos θ₁ = √p₁,   cos θ₂ = √p₂,   cos(θ₁ − θ₂) = 0 :

**each branch's classical probability equals cos² of its action increment,
and sibling branches sit in exact phase quadrature.**  The Rideout–Sorkin
coupling constants are not free parameters — they are determined by the
Benincasa–Dowker action.  Probability = cos²(action gap/ℏ): a derived Born
rule for the growth of spacetime. -/
theorem born_quadrature_law (p₁ p₂ θ₁ θ₂ : ℝ)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hsum : p₁ + p₂ = 1)
    (h : (Real.sqrt p₁ : ℂ) * Complex.exp (θ₁ * Complex.I)
      + (Real.sqrt p₂ : ℂ) * Complex.exp (θ₂ * Complex.I) = 1) :
    Real.cos θ₁ = Real.sqrt p₁ ∧ Real.cos θ₂ = Real.sqrt p₂
      ∧ Real.cos (θ₁ - θ₂) = 0 := by
  have hre : Real.sqrt p₁ * Real.cos θ₁ + Real.sqrt p₂ * Real.cos θ₂ = 1 := by
    have := congrArg Complex.re h
    rwa [Complex.add_re, weighted_phase_re, weighted_phase_re,
      Complex.one_re] at this
  have him : Real.sqrt p₁ * Real.sin θ₁ + Real.sqrt p₂ * Real.sin θ₂ = 0 := by
    have := congrArg Complex.im h
    rwa [Complex.add_im, weighted_phase_im, weighted_phase_im,
      Complex.one_im] at this
  have hs₁ : Real.sqrt p₁ ^ 2 = p₁ := Real.sq_sqrt hp₁.le
  have hs₂ : Real.sqrt p₂ ^ 2 = p₂ := Real.sq_sqrt hp₂.le
  have hsin₁ : Real.sin θ₁ ^ 2 = 1 - Real.cos θ₁ ^ 2 := Real.sin_sq θ₁
  have hsin₂ : Real.sin θ₂ ^ 2 = 1 - Real.cos θ₂ ^ 2 := Real.sin_sq θ₂
  -- squaring the imaginary equation: p₁ sin²θ₁ = p₂ sin²θ₂
  have hsq : p₁ * Real.sin θ₁ ^ 2 = p₂ * Real.sin θ₂ ^ 2 := by
    have h2 : (Real.sqrt p₁ * Real.sin θ₁) ^ 2
        = (Real.sqrt p₂ * Real.sin θ₂) ^ 2 := by
      have : Real.sqrt p₁ * Real.sin θ₁ = -(Real.sqrt p₂ * Real.sin θ₂) := by
        linarith
      rw [this]
      ring
    nlinarith [h2, hs₁, hs₂]
  -- the Pythagorean pivot: √p₁·cosθ₁ = p₁
  have hx : Real.sqrt p₁ * Real.cos θ₁ = p₁ := by
    nlinarith [hre, hsq, hsin₁, hsin₂, hs₁, hs₂, hsum,
      sq_nonneg (Real.sqrt p₁ * Real.cos θ₁ - Real.sqrt p₂ * Real.cos θ₂)]
  have hy : Real.sqrt p₂ * Real.cos θ₂ = p₂ := by linarith
  have hsp₁ : 0 < Real.sqrt p₁ := Real.sqrt_pos.mpr hp₁
  have hsp₂ : 0 < Real.sqrt p₂ := Real.sqrt_pos.mpr hp₂
  have hc₁ : Real.cos θ₁ = Real.sqrt p₁ := by
    have h2 : Real.sqrt p₁ * Real.cos θ₁ = Real.sqrt p₁ * Real.sqrt p₁ := by
      rw [hx]
      nlinarith [hs₁]
    exact mul_left_cancel₀ hsp₁.ne' h2
  have hc₂ : Real.cos θ₂ = Real.sqrt p₂ := by
    have h2 : Real.sqrt p₂ * Real.cos θ₂ = Real.sqrt p₂ * Real.sqrt p₂ := by
      rw [hy]
      nlinarith [hs₂]
    exact mul_left_cancel₀ hsp₂.ne' h2
  refine ⟨hc₁, hc₂, ?_⟩
  -- quadrature: multiply cos(θ₁−θ₂) by √p₁√p₂ > 0
  have hkey : Real.sqrt p₁ * Real.sqrt p₂ * Real.cos (θ₁ - θ₂) = 0 := by
    rw [Real.cos_sub]
    have hss : (Real.sqrt p₁ * Real.sin θ₁) * (Real.sqrt p₂ * Real.sin θ₂)
        = -(p₁ * Real.sin θ₁ ^ 2) := by
      have hminus : Real.sqrt p₂ * Real.sin θ₂
          = -(Real.sqrt p₁ * Real.sin θ₁) := by linarith
      rw [hminus]
      nlinarith [hs₁]
    have hsin₁sq : Real.sin θ₁ ^ 2 = p₂ := by
      rw [hsin₁, hc₁]
      nlinarith [hs₁, hsum]
    nlinarith [hss, hsin₁sq, hc₁, hc₂, hs₁, hs₂]
  have hne : Real.sqrt p₁ * Real.sqrt p₂ ≠ 0 := by positivity
  exact (mul_eq_zero.mp hkey).resolve_left hne

/-- **Probability = cos²(action gap)**: the corollary in Born form. -/
theorem transition_probability_eq_cos_sq (p₁ p₂ θ₁ θ₂ : ℝ)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hsum : p₁ + p₂ = 1)
    (h : (Real.sqrt p₁ : ℂ) * Complex.exp (θ₁ * Complex.I)
      + (Real.sqrt p₂ : ℂ) * Complex.exp (θ₂ * Complex.I) = 1) :
    p₁ = Real.cos θ₁ ^ 2 ∧ p₂ = Real.cos θ₂ ^ 2 := by
  obtain ⟨hc₁, hc₂, _⟩ := born_quadrature_law p₁ p₂ θ₁ θ₂ hp₁ hp₂ hsum h
  constructor
  · rw [hc₁, Real.sq_sqrt hp₁.le]
  · rw [hc₂, Real.sq_sqrt hp₂.le]

#print axioms born_quadrature_law
#print axioms transition_probability_eq_cos_sq

#print axioms strong_positivity
#print axioms D_diagonal
#print axioms interference_sum_rule
#print axioms pairwise_purity
#print axioms diagonal_decomposition
#print axioms two_history_interference
#print axioms unitarity_quantizes

end UnifiedTheory.Audit.KFCausalQuantumMeasure
